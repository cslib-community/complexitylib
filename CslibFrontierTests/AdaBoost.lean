/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.Boosting.AdaBoost

/-! Checks for AdaBoost on the three-point sample `0 ↦ true, 1 ↦ false, 2 ↦ true` with decision
stumps on `ℕ`. No stump is consistent with the sample, but the stump that errs only on the lightest
point is a weak learner with edge `1/6`, so AdaBoost is consistent after `40` rounds. Also: the
uniform first round, the product bound after one round, and a learner without edge `1/4`. -/

namespace CslibFrontierTests.AdaBoost

open Finset Real Cslib.MachineLearning.Boosting Cslib.MachineLearning.PACLearning

/-- The sample `0 ↦ true, 1 ↦ false, 2 ↦ true`. -/
def S : Fin 3 → ℕ × Bool := ![(0, true), (1, false), (2, true)]

/-- The constant stump `true`, which errs only on point `1`. -/
def constTrue : ℕ → Bool := fun _ => true

/-- The stump `x < 1`, which errs only on point `2`. -/
def below1 : ℕ → Bool := fun x => decide (x < 1)

/-- The stump `1 < x`, which errs only on point `0`. -/
def above1 : ℕ → Bool := fun x => decide (1 < x)

theorem weightedError_constTrue (D : Fin 3 → ℝ) : weightedError S D constTrue = D 1 := by
  rw [weightedError, sum_filter, Fin.sum_univ_three]
  simp [S, constTrue]

theorem weightedError_below1 (D : Fin 3 → ℝ) : weightedError S D below1 = D 2 := by
  rw [weightedError, sum_filter, Fin.sum_univ_three]
  simp [S, below1]

theorem weightedError_above1 (D : Fin 3 → ℝ) : weightedError S D above1 = D 0 := by
  rw [weightedError, sum_filter, Fin.sum_univ_three]
  simp [S, above1]

/-- No one of the three stumps is consistent with the sample. -/
theorem stumps_err : constTrue (S 1).1 ≠ (S 1).2 ∧ below1 (S 2).1 ≠ (S 2).2 ∧
    above1 (S 0).1 ≠ (S 0).2 := by
  decide

/-- The weak learner: the stump that errs only on a point of least weight. -/
noncomputable def stump (D : Fin 3 → ℝ) : ℕ → Bool :=
  if D 1 ≤ D 0 ∧ D 1 ≤ D 2 then constTrue else if D 2 ≤ D 0 then below1 else above1

/-- The stump learner has edge `1/6`: the least of three weights summing to `1` is at most
`1/3`. -/
theorem isWeakLearner_stump : IsWeakLearner S stump (1 / 6) := by
  intro D _ hD
  rw [Fin.sum_univ_three] at hD
  unfold stump
  split_ifs with h1 h2
  · rw [weightedError_constTrue]
    linarith [h1.1, h1.2]
  · rw [weightedError_below1]
    by_cases h : D 2 ≤ D 1
    · linarith
    · exact absurd ⟨by linarith, by linarith⟩ h1
  · rw [weightedError_above1]
    by_cases h : D 0 ≤ D 1
    · linarith
    · exact absurd ⟨by linarith, by linarith⟩ h1

theorem log_three_lt : log (3 : ℕ) < 2 * (1 / 6 : ℝ) ^ 2 * (40 : ℕ) := by
  have h : log 3 < 2 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    linarith [quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  linarith

/-- AdaBoost with the stump learner is consistent with the sample after `40` rounds, although no
single stump is. -/
theorem adaBoost_forty (i : Fin 3) : adaBoost S stump 40 (S i).1 = (S i).2 :=
  isWeakLearner_stump.adaBoost_eq (by norm_num) log_three_lt i

/-! ### The first round -/

theorem rounds_zero_weights_eq (i : Fin 3) : (rounds S stump 0).weights i = 1 / 3 := by
  rw [rounds_zero_weights]
  norm_num

/-- On the uniform weights the learner returns `constTrue`, with weighted error `1/3`. -/
theorem rounds_zero_error : (rounds S stump 0).error S = 1 / 3 := by
  have hw := rounds_zero_weights_eq
  have hle : (rounds S stump 0).weights 1 ≤ (rounds S stump 0).weights 0 ∧
      (rounds S stump 0).weights 1 ≤ (rounds S stump 0).weights 2 := by
    rw [hw 0, hw 1, hw 2]
    exact ⟨le_rfl, le_rfl⟩
  have hhyp : (rounds S stump 0).hyp = constTrue := by
    rw [rounds_hyp, stump, ite_eq_left hle]
  rw [Round.error, hhyp, weightedError_constTrue, hw]

/-- After one round, the product bound gives training error at most `2 √(2/9) < 1`. -/
theorem adaBoost_one_le :
    (empiricalMiscount (adaBoost S stump 1) S : ℝ) / 3 ≤ 2 * √(1 / 3 * (1 - 1 / 3)) := by
  have h := empiricalMiscount_adaBoost_le_prod (T := 1) S stump fun t ht => by
    rw [Nat.lt_one_iff.mp ht, rounds_zero_error]
    norm_num
  rwa [prod_range_one, rounds_zero_error, Nat.cast_ofNat] at h

/-! ### A learner without edge `1/4` -/

/-- The learner that always returns `constTrue` has error `1/3` on the uniform weights, so it does
not have edge `1/4`. -/
theorem not_isWeakLearner_constTrue : ¬IsWeakLearner S (fun _ => constTrue) (1 / 4) := by
  intro h
  have := h (fun _ => 1 / 3) (fun _ => by norm_num) (by rw [Fin.sum_univ_three]; norm_num)
  rw [weightedError_constTrue] at this
  norm_num at this

end CslibFrontierTests.AdaBoost
