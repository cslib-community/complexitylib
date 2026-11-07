/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.OptimalStopping.Prophet
import Complexity.Probability.OptimalStopping.Secretary

/-! Checks for optimal stopping: exact secretary success probabilities for small `n`, the optimal
cutoff for three candidates and the resulting optimal success probability `1/2`, a rule that never
stops; the prophet inequality's Kleinberg–Weinberg threshold on the tight instance, Samuel-Cahn's
median hypotheses and theorem (a degenerate law, and a law with an atom at the median), a
concrete violation of every constant above `1/2`, and the backward-induction value of the tight
instance. -/

namespace ComplexityTests.OptimalStopping

open Cslib.Probability.OptimalStopping
open scoped ENNReal NNReal

/-! ### The secretary problem -/

namespace Secretary

open Cslib.Probability.OptimalStopping.Secretary

/-- With three candidates, skipping the first and hiring the next best-so-far wins with
probability `1/2`. -/
theorem successProb_cutoffRule_two_three : successProb (cutoffRule 2) 3 = 1 / 2 := by
  rw [successProb_cutoffRule (le_refl 2)]
  norm_num [Finset.sum_Icc_succ_top]

/-- With one candidate, hiring it always wins. -/
example : successProb (cutoffRule 1) 1 = 1 := by
  rw [successProb_cutoffRule_one]
  norm_num

/-- The optimal cutoff for three candidates is `2`: `1/2 ≤ 1 < 1 + 1/2`. -/
theorem optimalCutoff_three : optimalCutoff 3 = 2 := by
  refine le_antisymm (optimalCutoff_le (by norm_num) (by norm_num [Finset.sum_Ico_succ_top])) ?_
  by_contra hlt
  have h := sum_optimalCutoff_le 3
  rw [show optimalCutoff 3 = 1 by have := one_le_optimalCutoff 3; omega] at h
  norm_num [Finset.sum_Ico_succ_top] at h

/-- No rank-based rule hires the best of three candidates with probability more than `1/2`. -/
example (rule : Rule) : successProb rule 3 ≤ 1 / 2 := by
  have := successProb_le_successProb_optimalCutoff rule 3
  rwa [optimalCutoff_three, successProb_cutoffRule_two_three] at this

theorem stopIndex_never : ∀ past xs : List ℕ, stopIndex (fun _ => false) past xs = none
  | _, [] => rfl
  | past, x :: xs => by simp [stopIndex, stopIndex_never (x :: past) xs]

/-- A rule that never stops never wins. -/
example (n : ℕ) : successProb (fun _ => false) n = 0 := by
  simp [successProb, Wins, stopIndex_never]

/-- The optimal cutoff and `⌊n/e⌋ + 1` give nonvacuous two-sided bounds. -/
example (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-1) - 1 / n ≤ successProb (cutoffRule (optimalCutoff n)) n ∧
      successProb (cutoffRule (optimalCutoff n)) n ≤ Real.exp (-1) + 1 / n :=
  ⟨(exp_neg_one_sub_le_successProb_floor hn).trans
      (successProb_le_successProb_optimalCutoff _ n),
    successProb_le_exp_neg_one_add _ n⟩

end Secretary

/-! ### The prophet inequality -/

namespace Prophet

open Cslib.Probability.OptimalStopping.Prophet

theorem jointLaw_pure (a : ℝ≥0) : jointLaw [PMF.pure a] = PMF.pure [a] := by
  simp [jointLaw_cons, PMF.pure_bind, PMF.pure_map]

/-- A sure value `1` has median `1`, so Samuel-Cahn's median hypotheses are satisfiable. -/
example : (jointLaw [PMF.pure (1 : ℝ≥0)]).toOuterMeasure {xs | listMax xs < 1} ≤ 1 / 2 ∧
    1 / 2 ≤ (jointLaw [PMF.pure (1 : ℝ≥0)]).toOuterMeasure {xs | listMax xs ≤ 1} := by
  simp [jointLaw_pure, PMF.toOuterMeasure_pure_apply, listMax]

/-- `PMF.toOuterMeasure_apply` with the indicator written as a factor, the form taken by
`tsum_jointLaw_cons_mul`. -/
private theorem toOuterMeasure_eq_tsum {α : Type*} (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    p.toOuterMeasure s = ∑' x, p x * if x ∈ s then 1 else 0 := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

/-- On the tight instance with `k = 1`, `max` is never below `1` and is at most `1` with
probability `1/2`, so `1` is a median of `max` with an atom. -/
theorem median_tightLaws_one :
    (jointLaw (tightLaws 1)).toOuterMeasure {xs | listMax xs < 1} ≤ 1 / 2 ∧
      1 / 2 ≤ (jointLaw (tightLaws 1)).toOuterMeasure {xs | listMax xs ≤ 1} := by
  classical
  constructor <;>
  · rw [toOuterMeasure_eq_tsum, tightLaws_eq, tsum_jointLaw_cons_mul, tsum_pure_mul,
      tsum_jointLaw_cons_mul, tsum_longShot_mul]
    simp only [tsum_jointLaw_nil_mul, Set.mem_ofPred_eq, listMax]
    norm_num

/-- Samuel-Cahn's median theorem applies nondegenerately to the tight instance. -/
example : expectedMax (tightLaws 1) ≤ 2 * expectedReward (thresholdRule 1) (tightLaws 1) ∨
    expectedMax (tightLaws 1) ≤ 2 * expectedReward (strictThresholdRule 1) (tightLaws 1) :=
  expectedMax_le_two_mul_expectedReward_median _ median_tightLaws_one.1 median_tightLaws_one.2

/-- Here `E[max] = 3/2 ≤ 2 · 1`, the median is at or above `E[max]/2`, and the rule accepting
values of at least the median is the one that applies. -/
example : expectedMax (tightLaws 1) ≤ 2 * expectedReward (thresholdRule 1) (tightLaws 1) := by
  refine expectedMax_le_two_mul_expectedReward_thresholdRule_of_le _ median_tightLaws_one.1 ?_
  rw [expectedMax_tightLaws, ← ENNReal.toReal_le_toReal (by finiteness) (by simp)]
  norm_num [ENNReal.toReal_div]

/-- On the tight instance with `k = 1`, `E[max] = 3/2`. -/
theorem expectedMax_tightLaws_one : expectedMax (tightLaws 1) = 3 / 2 := by
  rw [expectedMax_tightLaws]
  norm_num

/-- With `k = 1`, every rule collects less than `3/4` of the prophet's `3/2`. -/
example (stop : List ℝ≥0 → Bool) :
    expectedReward stop (tightLaws 1) < 3 / 4 * expectedMax (tightLaws 1) := by
  refine (expectedReward_tightLaws_le 1 stop).trans_lt ?_
  rw [expectedMax_tightLaws_one, ← ENNReal.toReal_lt_toReal (by simp) (by finiteness)]
  norm_num [ENNReal.toReal_div]

/-- The Kleinberg–Weinberg threshold applies to every instance with finite `E[max]`; on the tight
instance it gives `3/2 ≤ 2 E[reward]`. -/
example : expectedMax (tightLaws 1) ≤
    2 * expectedReward (thresholdRule (expectedMax (tightLaws 1) / 2).toNNReal) (tightLaws 1) :=
  expectedMax_le_two_mul_expectedReward_half _ (by rw [expectedMax_tightLaws_one]; finiteness)

/-- The factor `1/2` cannot be improved to `0.51`. -/
example : ∃ k, ∀ stop, expectedReward stop (tightLaws k) < 51 / 100 * expectedMax (tightLaws k) :=
  exists_tightLaws_lt (by
    rw [← ENNReal.toReal_lt_toReal (by simp) (by finiteness)]
    norm_num [ENNReal.toReal_div])

/-- The backward-induction value of the tight instance is at most `1`, through the
characterization of the value as the best expected reward of any rule. -/
example (k : ℕ) : valueFrom reward (tightLaws k) [] ≤ 1 := by
  rw [valueFrom_eq_iSup]
  exact iSup_le fun stop => expectedReward_tightLaws_le k stop

/-- Taking the sure value `1` attains the bound, so the value of the tight instance is `1`. -/
example (k : ℕ) : valueFrom reward (tightLaws k) [] = 1 := by
  refine le_antisymm ?_ ?_
  · rw [valueFrom_eq_iSup]
    exact iSup_le fun stop => expectedReward_tightLaws_le k stop
  · rw [valueFrom_eq_iSup]
    refine le_iSup_of_le (fun _ => true) (le_of_eq ?_)
    rw [tightLaws_eq, tsum_jointLaw_cons_mul]
    simp only [payoff_cons, ite_true, reward]
    simp [tsum_pmf_mul_const]

end Prophet

end ComplexityTests.OptimalStopping
