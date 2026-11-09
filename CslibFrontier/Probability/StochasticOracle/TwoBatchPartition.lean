/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.RationalFullCover
public import CslibFrontier.Foundations.Data.Finset.BernoulliProduct
public import CslibFrontier.Probability.StochasticOracle.CutoffFamilies
import Mathlib.Tactic

/-!
# The partition gap in exact two-turn selection

[Wang2027], Theorem 3(1), PDF p. 9, Appendix A.2, pp. 14–15.
The input weights are positive integers summing to twice a positive integer `B`.
Calls have costs `a i`, probabilities `a i / (4 * B^3)`, and unit cutoffs.
The threshold separates balanced subsets from every unbalanced subset, including
empty and full batches. Policies may use arbitrary real private randomization.
The opportunities are indexed, so equal weights remain distinct calls.
## Main results

* `equal_parameters`: unit cutoffs and the common probability/cost ratio.
* `balanced_cost`, `unbalanced_cost`: the strict rational decision gap.
* `policy_threshold_iff`: equivalence against all real-randomized policies.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchPartition
open Finset Cslib.Optimization.OneConstraint

variable {ι : Type} [Fintype ι] (a : ι → ℕ) (B : ℕ)

/-- Denominator chosen in the paper's reduction; cubic in the half-total. -/
@[expose] def denominator : ℚ := 4 * (B : ℚ)^3

/-- Decision threshold for the actual expected token cost. -/
@[expose] def threshold : ℚ := 2 * B - ((B : ℚ)^2 - 1/2) / denominator B

/-- The concrete oracle instance in the reduction. -/
@[expose] def instanceOf (hB : 0 < B) (ha : ∀ i, 0 < a i)
    (htotal : ∑ i, a i = 2 * B) : FullCoverInstance ι ℚ where
  success i := a i / denominator B
  success_pos i := div_pos (by exact_mod_cast ha i) (by unfold denominator; positivity)
  success_lt_one i := by
    have hi : a i ≤ 2 * B :=
      (single_le_sum (fun j _ => Nat.zero_le (a j)) (mem_univ i)).trans_eq htotal
    have hBr : (1 : ℚ) ≤ B := by exact_mod_cast hB
    have hir : (a i : ℚ) ≤ 2 * B := by exact_mod_cast hi
    apply (div_lt_one (by unfold denominator; positivity)).mpr
    unfold denominator
    nlinarith [sq_nonneg ((B : ℚ) - 1), mul_nonneg (show (0 : ℚ) ≤ B by positivity)
      (show (0 : ℚ) ≤ (B : ℚ)^2 - 1 by nlinarith)]
  cost i := a i
  cost_pos i := by exact_mod_cast ha i
  cutoff _ := 1
  cutoff_pos _ := by norm_num

variable {a B}

/-- All calls have the same cutoff and the same success/cost ratio. -/
theorem equal_parameters (hB : 0 < B) (ha : ∀ i, 0 < a i) (ht : ∑ i, a i = 2 * B) (i : ι) :
    (instanceOf a B hB ha ht).cutoff i = 1 ∧
      (instanceOf a B hB ha ht).success i / (instanceOf a B hB ha ht).cost i =
        (denominator B)⁻¹ := by
  refine ⟨rfl,?_⟩
  change ((a i : ℚ) / denominator B) / a i = _
  have hi : (a i : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (ha i))
  field_simp

open scoped Classical in
private theorem batch_complement (hB : 0 < B) (ha : ∀ i, 0 < a i)
    (ht : ∑ i, a i = 2 * B) (A : Finset ι) :
    (instanceOf a B hB ha ht).batchCost Aᶜ = 2 * B - (∑ i ∈ A, a i : ℕ) := by
  have hh := sum_add_sum_compl A a
  have hh' : ((∑ i ∈ A, a i : ℕ) : ℚ) + (∑ i ∈ Aᶜ, (a i : ℚ)) = 2 * B := by
    exact_mod_cast hh.trans ht
  change (∑ i ∈ Aᶜ, (a i : ℚ)) = _
  linarith

/-- Unbalanced subsets have a strict cost gap above the decision threshold. -/
theorem unbalanced_cost (hB : 0 < B) (ha : ∀ i, 0 < a i)
    (ht : ∑ i, a i = 2 * B) (A : Finset ι) (hne : ∑ i ∈ A, a i ≠ B) :
    threshold B < (instanceOf a B hB ha ht).twoBatchCost A := by
  classical
  let I := instanceOf a B hB ha ht
  have hp (i : ι) (_ : i ∈ A) : 0 ≤ I.success i ∧ I.success i ≤ 1 :=
    ⟨(I.success_pos i).le,(I.success_lt_one i).le⟩
  have hb := (one_sub_prod_one_sub_bounds A I.success hp).2
  have hsum : (∑ i ∈ A, I.success i) = ((∑ i ∈ A, a i : ℕ) : ℚ) / denominator B := by
    simp [I, instanceOf, sum_div]
  change 1 - I.batchFailure A ≤ _ at hb
  rw [hsum] at hb
  have hmul := mul_le_mul_of_nonneg_right hb (show 0 ≤ I.batchCost Aᶜ from
    sum_nonneg (fun i _ => (I.cost_pos i).le))
  have hc := batch_complement hB ha ht A
  change I.batchCost Aᶜ = _ at hc
  rw [hc] at hmul
  have hgap : (1 : ℚ) ≤ (((∑ i ∈ A, a i : ℕ) : ℚ) - B)^2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((∑ i ∈ A, a i : ℕ) : ℚ) + 1 ≤ B := by exact_mod_cast h
      nlinarith
    · have : (B : ℚ) + 1 ≤ (∑ i ∈ A, a i : ℕ) := by exact_mod_cast h
      nlinarith
  have htq : I.batchCost univ = 2 * B := by
    change (∑ i, (a i : ℚ)) = _
    exact_mod_cast ht
  change threshold B < I.twoBatchCost A
  rw [twoBatchCost_eq_total_sub, htq, hc]
  have hd : 0 < denominator B := by unfold denominator; positivity
  unfold threshold
  have hupper : (((∑ i ∈ A, a i : ℕ) : ℚ) / denominator B) *
      (2 * B - (∑ i ∈ A, a i : ℕ)) ≤ ((B : ℚ)^2 - 1) / denominator B := by
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hd).mpr (by nlinarith)
  have hg := hmul.trans hupper
  have hstrict : ((B : ℚ)^2 - 1) / denominator B < ((B : ℚ)^2 - 1/2) / denominator B :=
    (div_lt_div_iff_of_pos_right hd).mpr (by linarith)
  linarith

/-- A balanced subset has a strict cost gap below the decision threshold. -/
theorem balanced_cost (hB : 0 < B) (ha : ∀ i, 0 < a i)
    (ht : ∑ i, a i = 2 * B) (A : Finset ι) (heq : ∑ i ∈ A, a i = B) :
    (instanceOf a B hB ha ht).twoBatchCost A < threshold B := by
  classical
  let I := instanceOf a B hB ha ht
  have hb := (one_sub_prod_one_sub_bounds A I.success (fun i _ =>
    ⟨(I.success_pos i).le,(I.success_lt_one i).le⟩)).1
  have hsum : (∑ i ∈ A, I.success i) = (B : ℚ) / denominator B := by
    simp [I, instanceOf, ← sum_div, ← Nat.cast_sum, heq]
  change _ ≤ 1 - I.batchFailure A at hb
  rw [hsum] at hb
  have hc : I.batchCost Aᶜ = B := by
    rw [show I.batchCost Aᶜ = 2 * B - (∑ i ∈ A, a i : ℕ) from batch_complement hB ha ht A, heq]
    ring
  have hmul := mul_le_mul_of_nonneg_right hb (show (0 : ℚ) ≤ B by positivity)
  have htq : I.batchCost univ = 2 * B := by
    change (∑ i, (a i : ℚ)) = _
    exact_mod_cast ht
  rw [twoBatchCost_eq_total_sub, htq, hc]
  have hd : 0 < denominator B := by unfold denominator; positivity
  have hBr : (1 : ℚ) ≤ B := by exact_mod_cast hB
  unfold threshold
  have hstrict : ((B : ℚ)^2 - 1/2) / denominator B <
      ((B : ℚ) / denominator B - ((B : ℚ) / denominator B)^2 / 2) * B := by
    unfold denominator
    field_simp
    nlinarith [show (0 : ℚ) ≤ (B : ℚ)^3 by positivity]
  nlinarith

/-- Exact decision correspondence, including every real-randomized competing policy.
The threshold is attained or beaten exactly when the integer weights have a
balanced subset. No optimum or reduction correctness is assumed. -/
theorem policy_threshold_iff [Nonempty ι] (hB : 0 < B) (ha : ∀ i, 0 < a i)
    (ht : ∑ i, a i = 2 * B) :
    (∃ π : Policy ι ℝ 2,
      π.Feasible (instanceOf a B hB ha ht).realify 2 ∧
      (π.execution (instanceOf a B hB ha ht).realify).mean executionSuccess =
        1 - (instanceOf a B hB ha ht).realify.batchFailure univ ∧
      (π.execution (instanceOf a B hB ha ht).realify).mean
        (executionCost (instanceOf a B hB ha ht).realify) ≤ (threshold B : ℝ)) ↔
    ∃ A : Finset ι, ∑ i ∈ A, a i = B := by
  classical
  let I := instanceOf a B hB ha ht
  have hcast (A : Finset ι) : I.realify.twoBatchCost A = (I.twoBatchCost A : ℝ) := by
    simp [FullCoverInstance.twoBatchCost, FullCoverInstance.batchCost_realify,
      FullCoverInstance.batchFailure_realify]
  constructor
  · rintro ⟨π,hπ,hp,hc⟩
    obtain ⟨A,_,hA⟩ := two_batch_reduction I.realify 2 π hπ hp
    refine ⟨A,?_⟩
    by_contra hn
    have hg : (threshold B : ℝ) < I.realify.twoBatchCost A := by
      rw [hcast]
      exact_mod_cast unbalanced_cost hB ha ht A hn
    linarith
  · rintro ⟨A,hA⟩
    have hAf : I.realify.TwoBatchFeasible 2 A := by
      constructor
      · by_contra hn
        have he : A = ∅ := not_nonempty_iff_eq_empty.mp hn
        simp [he] at hA
        omega
      · have hd (C : Finset ι) : I.realify.batchDuration C ≤ 1 := by
          exact (I.realify.batchDuration_le_iff C 1).mpr ⟨by norm_num,
            fun i _ => by simp [I, instanceOf, FullCoverInstance.realify]⟩
        linarith [hd A,hd Aᶜ]
    let π := followPlan (K := ℝ) (n := 2) (A,(Aᶜ,()))
    refine ⟨π,?_,?_,?_⟩
    · intro C hC
      rw [followPlan_law, Distribution.mem_support_pure] at hC
      subst C
      exact ⟨by simpa [Plan.NoReuse, Plan.used] using
        (show Disjoint A Aᶜ from disjoint_compl_right),by simpa [Plan.duration] using hAf.2⟩
    · rw [(execution_equivalence I.realify π).1, followPlan_law, Distribution.mean_pure]
      exact (two_batch_values I.realify A).1
    · rw [(execution_equivalence I.realify π).2, followPlan_law, Distribution.mean_pure]
      rw [(two_batch_values I.realify A).2]
      change I.realify.twoBatchCost A ≤ _
      rw [hcast]
      exact_mod_cast (balanced_cost hB ha ht A hA).le

end Cslib.Probability.StochasticOracle.TwoBatchPartition
