/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.TwoBatchBinary
import Mathlib.Tactic

/-!
# Exact integer-cost two-turn optimization

[Wang2027], Theorem 3(2), PDF p. 9 and Appendix A.2, p. 15.
We run the constructive minimum-product DP at tolerance `1 / (C+1)`, where
`C` is the numerical sum of the positive integer costs. In every maximum-member
branch the entire rounding error is strictly below one. Consequently two
witnesses with the same refined cost key have exactly the same original integer
cost; minimum-product dominance gives an exact optimum, not an approximation.
This implementation uses polynomially many refined keys rather than the paper's
unscaled subset-sum keys. The binary-input runtime is polynomial in input length
and `C`; it need not be polynomial in the binary length of `C`.

All probabilities and cutoffs remain heterogeneous binary rationals. Returned
batches are explicitly reconstructed. The optimum is against all feasible
maximum-success policies with arbitrary real private randomization.
## Main results

* `choose_exact`: exact savings dominance for every feasible first batch.
* `choose_policy_minimum`: exact cost comparison with every real-randomized competitor.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchIntegral
open Finset TwoBatchApproximation
open Cslib.Algorithms.Lean.DynamicProgramming.MinProduct

variable {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (c : Fin k → ℕ)

/-- Numerical total cost controls the precision of exact integral optimization. -/
@[expose] def tolerance : ℚ := 1 / ((∑ i, c i : ℕ) + 1)

/-- The exact constructive selector, using the already certified minimum-product tables. -/
@[expose] def choose (D : ℚ) : Finset (Fin k) :=
  TwoBatchApproximation.choose I (tolerance c) D

/-- Integral precision is positive, including on an empty population. -/
theorem tolerance_pos : 0 < tolerance c := by unfold tolerance; positivity

private theorem small_error (r : Fin k) : tolerance c * c r < 1 := by
  have hr : c r ≤ ∑ i, c i := single_le_sum (fun i _ => Nat.zero_le (c i)) (mem_univ r)
  have hr' : (c r : ℚ) < (∑ i, c i : ℕ) + 1 := by exact_mod_cast Nat.lt_succ_of_le hr
  unfold tolerance
  rw [one_div_mul_eq_div,div_lt_one (by positivity)]
  exact hr'

/-- Exact savings dominance for every feasible first batch, with no optimizer
or desired comparison inequality in the premises. -/
theorem choose_exact (hc : I.cost = fun i => (c i : ℚ)) {D : ℚ}
    {A : Finset (Fin k)} (hA : I.TwoBatchFeasible D A) :
    gain I A ≤ gain I (choose I c D) := by
  obtain ⟨⟨a,b⟩,hab,hfamily⟩ := cutoff_families_cover I hA
  have hfam : ∃ C ∈ familyCandidates I (tolerance c) a b, gain I A ≤ gain I C := by
    have h := family_gain_of_branches I (ε := tolerance c) (a := a) (b := b) (μ := 1) le_rfl
    simp only [one_mul] at h
    apply h ?_ hA.1 hfamily
    intro r outside _ _ items e he
    have hr : 0 < c r := by
      have hh := I.cost_pos r
      rw [hc] at hh
      change 0 < (c r : ℚ) at hh
      exact_mod_cast hh
    have hE : 0 ≤ cost I (population.filter (fun i => a < I.cutoff i)) := by
      unfold cost
      exact List.sum_nonneg (fun x hx => by
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact (I.cost_pos i).le)
    have hf : 0 ≤ I.batchFailure (forced I b).toFinset :=
      (I.batchFailure_pos _).le
    rw [hc] at he
    obtain ⟨d,hd,_,hp,hgain⟩ := branch_integral_exact c (failure I) r hr
      (tolerance_pos c) (small_error c r)
      (fun i => (sub_pos.mpr (I.success_lt_one i)).le) hE hf items he
    exact ⟨d,by simpa only [hc] using hd,hp,by simpa only [hc] using hgain⟩
  obtain ⟨C,hC,hgain⟩ := hfam
  apply hgain.trans (gain_choose_ge I (tolerance c) D ?_)
  obtain ⟨hp,hD⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  apply List.mem_flatMap.mpr
  refine ⟨a,?_,List.mem_flatMap.mpr ⟨b,?_,?_⟩⟩
  · simpa [population] using ha
  · simpa [population] using hb
  · simpa only [hD,ite_true] using hC

/-- The exact selected cost is no larger than any real-randomized competitor.
This includes empty padding in competing policies and empty complementary batches. -/
theorem choose_policy_minimum (hc : I.cost = fun i => (c i : ℚ)) {D : ℚ} (hk : 0 < k)
    (π : Policy (Fin k) ℝ 2) (hπ : π.Feasible I.realify (D : ℝ))
    (hp : (π.execution I.realify).mean executionSuccess =
      1 - I.realify.batchFailure univ) :
    ((I.twoBatchCost (choose I c D) : ℚ) : ℝ) ≤
      (π.execution I.realify).mean (executionCost I.realify) := by
  classical
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  obtain ⟨A,hA,hcost⟩ := two_batch_reduction I.realify (D : ℝ) π hπ hp
  have hAq : I.TwoBatchFeasible D A := by
    refine ⟨hA.1,?_⟩
    have hd := hA.2
    rw [I.batchDuration_realify,I.batchDuration_realify] at hd
    exact_mod_cast hd
  have hgain := choose_exact I c hc hAq
  have hmin : I.twoBatchCost (choose I c D) ≤ I.twoBatchCost A := by
    have hs (B : Finset (Fin k)) : I.twoBatchCost B = I.batchCost univ - gain I B := by
      rw [twoBatchCost_eq_total_sub]
      unfold gain
      congr 2
      congr 1
      ext i
      simp
    rw [hs,hs]
    exact sub_le_sub_left hgain (I.batchCost univ)
  have hcast : I.realify.twoBatchCost A = (I.twoBatchCost A : ℝ) := by
    simp [FullCoverInstance.twoBatchCost,FullCoverInstance.batchCost_realify,
      FullCoverInstance.batchFailure_realify]
  rw [hcast] at hcost
  have hminr : (I.twoBatchCost (choose I c D) : ℝ) ≤ (I.twoBatchCost A : ℝ) := by
    exact_mod_cast hmin
  exact hminr.trans hcost

end Cslib.Probability.StochasticOracle.TwoBatchIntegral
