/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.TwoBatchApproximation
public import CslibFrontier.Probability.StochasticOracle.RationalFullCover
import Mathlib.Tactic

/-!
# Global savings approximation against real-randomized policies

[Wang2027], Theorem 2(2), PDF pp. 7–8: the actual rounded-product selector
approximates savings against every feasible maximum-success two-turn policy,
including arbitrary real private randomization on rational oracle inputs.
This supplies the approximation, success and deadline parts of the theorem;
`TwoBatchBinary` supplies the separate uniform binary running-time certificate.

## Main results

* `choose_real_policy_approximation`: savings and cost bounds against real competitors.
* `choose_optimum_guarantees`: the same bounds relative to an attained global optimum.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchApproximation

variable {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)

/-- The global approximation applies to arbitrary real-randomized competitors,
not only rational probability tables. The selector itself uses only the supplied
rational parameters and tolerance. Deadline feasibility is required of the
competitor; maximum success forces full use on its all-failure schedules. -/
theorem choose_real_policy_approximation {ε D : ℚ} (hk : 0 < k)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (π : Policy (Fin k) ℝ 2)
    (hπ : π.Feasible I.realify (D : ℝ))
    (hp : (π.execution I.realify).mean executionSuccess =
      1 - I.realify.batchFailure Finset.univ) :
    (1 - (ε : ℝ)) * ((I.batchCost Finset.univ : ℝ) -
      (π.execution I.realify).mean (executionCost I.realify)) ≤
        (gain I (choose I ε D) : ℝ) ∧
    ((Plan.expectedCost I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) : ℚ) : ℝ) ≤
      (π.execution I.realify).mean (executionCost I.realify) + (ε : ℝ) *
        ((I.batchCost Finset.univ : ℝ) -
          (π.execution I.realify).mean (executionCost I.realify)) := by
  classical
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  obtain ⟨A,hA,hcost⟩ := two_batch_reduction I.realify (D : ℝ) π hπ hp
  have hAq : I.TwoBatchFeasible D A := by
    refine ⟨hA.1,?_⟩
    have hd := hA.2
    rw [I.batchDuration_realify, I.batchDuration_realify] at hd
    exact_mod_cast hd
  have hs : I.realify.twoBatchCost A = (I.batchCost Finset.univ : ℝ) -
      (gain I A : ℝ) := by
    rw [twoBatchCost_eq_total_sub]
    simp only [FullCoverInstance.batchCost_realify, FullCoverInstance.batchFailure_realify]
    have hc : Finset.univ \ A = Aᶜ := by ext i; simp
    simp only [gain, hc, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
    congr 3
    apply congrArg I.batchCost
    ext i
    simp
  have hgain : (1 - (ε : ℝ)) * (gain I A : ℝ) ≤
      (gain I (choose I ε D) : ℝ) := by
    exact_mod_cast choose_approximation I hε₀ hAq
  have hε : 0 ≤ 1 - (ε : ℝ) := by exact_mod_cast sub_nonneg.mpr hε₁.le
  have hbound : (1 - (ε : ℝ)) * ((I.batchCost Finset.univ : ℝ) -
      (π.execution I.realify).mean (executionCost I.realify)) ≤
        (gain I (choose I ε D) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left (show (I.batchCost Finset.univ : ℝ) -
      (π.execution I.realify).mean (executionCost I.realify) ≤ (gain I A : ℝ) by
        linarith) hε
    exact hm.trans hgain
  refine ⟨hbound,?_⟩
  rw [choose_expectedCost]
  push_cast
  nlinarith

/-- There is an attained optimum over all real-randomized maximum-success
competitors, and the implemented schedule satisfies both of the source's
approximation inequalities relative to its value. The original deadline sums
prescribed cutoffs and excludes local selection time. This is an approximation
and policy-realization result; no binary runtime is claimed here. -/
theorem choose_optimum_guarantees {ε D : ℚ} (hk : 0 < k)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hD : I.batchDuration Finset.univ ≤ D) :
    ∃ cstar : ℝ,
      (∃ π : Policy (Fin k) ℝ 2, π.Feasible I.realify (D : ℝ) ∧
        (π.execution I.realify).mean executionSuccess =
          1 - I.realify.batchFailure Finset.univ ∧
        (π.execution I.realify).mean (executionCost I.realify) = cstar) ∧
      (∀ π : Policy (Fin k) ℝ 2, π.Feasible I.realify (D : ℝ) →
        (π.execution I.realify).mean executionSuccess =
          1 - I.realify.batchFailure Finset.univ →
        cstar ≤ (π.execution I.realify).mean (executionCost I.realify)) ∧
      Plan.Feasible I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) D ∧
      Plan.success I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) =
        1 - I.batchFailure Finset.univ ∧
      (1 - (ε : ℝ)) * ((I.batchCost Finset.univ : ℝ) - cstar) ≤
        (gain I (choose I ε D) : ℝ) ∧
      ((Plan.expectedCost I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) : ℚ) : ℝ) ≤
        cstar + (ε : ℝ) * ((I.batchCost Finset.univ : ℝ) - cstar) := by
  classical
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have hDr : I.realify.batchDuration Finset.univ ≤ (D : ℝ) := by
    rw [I.batchDuration_realify]
    exact_mod_cast hD
  obtain ⟨A,_,hf,hp,hc,hmin⟩ := minimum_two_batch I.realify (D : ℝ) hDr
  obtain ⟨hsave,happrox⟩ := choose_real_policy_approximation I hk hε₀ hε₁ _ hf hp
  refine ⟨I.realify.twoBatchCost A,⟨_,hf,hp,hc⟩,hmin,
    choose_schedule_feasible I hk hD,choose_success I ε D,?_,?_⟩
  · rwa [hc] at hsave
  · rwa [hc] at happrox

end Cslib.Probability.StochasticOracle.TwoBatchApproximation
