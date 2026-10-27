import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParameters

/-! Actual first-success outputs, exact source coefficients, rejected candidates and boundaries.
The evaluation control runs the executable `Nat.find` selector. Equality proofs separately use
its minimum specification and decidable tests of all smaller candidates. -/

open Cslib.Logic.PL.ClauseSet.Sparsification Finset

/-- info: [64, 128, 512, 1024, 2, 2, 2] -/
#guard_msgs in
#eval [(2, 1), (2, 2), (3, 1), (3, 2), (1, 1), (0, 1), (3, 0)].map
  fun (k, B) => countingThresholdBase k B

example : countingDepthCoeff 3 2 = 28 ∧ countingBChoiceCoeff 3 = 16 := by decide

private theorem width_two_budget_one : countingThresholdBase 2 1 = 64 :=
  countingThresholdBase_eq_two_pow (m := 6) (by decide) (by decide) (by decide) (by decide)

example : countingThresholdBase 2 2 = 128 :=
  countingThresholdBase_eq_two_pow (m := 7) (by decide) (by decide) (by decide) (by decide)

example : countingThresholdBase 3 1 = 512 :=
  countingThresholdBase_eq_two_pow (m := 9) (by decide) (by decide) (by decide) (by decide)

example : countingThresholdBase 3 2 = 1024 :=
  countingThresholdBase_eq_two_pow (m := 10) (by decide) (by decide) (by decide) (by decide)

-- M = 32 is large enough for Γ but fails the budget; the selector must continue to 64.
example : countingBChoiceCoeff 2 ≤ 32 ∧
    ¬ (1 * countingBChoiceCoeff 2 * Nat.clog 2 (4 * countingDepthCoeff 2 32 * 32) ≤ 32) := by
  decide

-- No branching remains at width zero or one. The numerical coefficients vanish, while the
-- separate total choice M = 2 remains compatible with consumers requiring a base at least two.
example : countingDepthCoeff 0 2 = 0 ∧ countingBChoiceCoeff 0 = 0 ∧
    countingThresholdBase 0 3 = 2 ∧ countingDepthCoeff 1 2 = 0 ∧ countingBChoiceCoeff 1 = 0 ∧
    countingThresholdBase 1 3 = 2 := by
  norm_num [countingDepthCoeff, countingBChoiceCoeff,
    countingThresholdBase_of_lt_two (k := 0) (by decide),
    countingThresholdBase_of_lt_two (k := 1) (by decide)]

example : countingThresholdBase 3 0 = 2 := countingThresholdBase_zero 3

-- The selected value feeds the numerical consumer, with positive radius one and tail 65.
example :
    (∑ j ∈ range (countingBChoiceCoeff 2 * 16 / countingThresholdBase 2 1 + 1),
      (countingDepthCoeff 2 (countingThresholdBase 2 1) * 16).choose j) = 65 ∧
    (∑ j ∈ range (countingBChoiceCoeff 2 * 16 / countingThresholdBase 2 1 + 1),
      (countingDepthCoeff 2 (countingThresholdBase 2 1) * 16).choose j) ≤ 2 ^ 17 := by
  constructor
  · rw [width_two_budget_one]
    norm_num [countingBChoiceCoeff, countingDepthCoeff, sum_range_succ]
  · exact sum_choose_le_countingThresholdBase (by decide) (by decide) 16

-- Variable budget N = 0 is still permitted by the selected-parameter tail theorem.
example :
    (∑ j ∈ range (countingBChoiceCoeff 3 * 0 / countingThresholdBase 3 2 + 1),
      (countingDepthCoeff 3 (countingThresholdBase 3 2) * 0).choose j) ≤ 2 := by
  exact sum_choose_le_countingThresholdBase (by decide) (by decide) 0
