import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParameters

/-! Actual first-success outputs, exact source coefficients, rejected candidates and boundaries.
The evaluation control runs the executable `Nat.find` selector. Equality proofs separately use
its minimum specification and decidable tests of all smaller candidates. -/

open Cslib.Logic.PL.ClauseSet.Sparsification Finset

/-- info: [64, 128, 512, 1024, 2, 2, 2] -/
#guard_msgs in
#eval [(2, 1), (2, 2), (3, 1), (3, 2), (1, 1), (0, 1), (3, 0)].map
  fun (k, B) => countingThresholdBase k B

private theorem width_two_budget_one : countingThresholdBase 2 1 = 64 :=
  countingThresholdBase_eq_two_pow (m := 6) (by decide) (by decide) (by decide) (by decide)

-- Exact source coefficients, selected power-of-two bases, rejected candidate M = 32, and
-- width-0/1 and budget-0 boundaries.
example :
    countingDepthCoeff 3 2 = 28 ∧
    countingBChoiceCoeff 3 = 16 ∧
    countingThresholdBase 2 2 = 128 ∧
    countingThresholdBase 3 1 = 512 ∧
    countingThresholdBase 3 2 = 1024 ∧
    countingBChoiceCoeff 2 ≤ 32 ∧
    ¬ (1 * countingBChoiceCoeff 2 * Nat.clog 2 (4 * countingDepthCoeff 2 32 * 32) ≤ 32) ∧
    countingDepthCoeff 0 2 = 0 ∧
    countingBChoiceCoeff 0 = 0 ∧
    countingThresholdBase 0 3 = 2 ∧
    countingDepthCoeff 1 2 = 0 ∧
    countingBChoiceCoeff 1 = 0 ∧
    countingThresholdBase 1 3 = 2 ∧
    countingThresholdBase 3 0 = 2 :=
  ⟨by decide, by decide,
    countingThresholdBase_eq_two_pow (m := 7) (by decide) (by decide) (by decide) (by decide),
    countingThresholdBase_eq_two_pow (m := 9) (by decide) (by decide) (by decide) (by decide),
    countingThresholdBase_eq_two_pow (m := 10) (by decide) (by decide) (by decide) (by decide),
    by decide, by decide, by decide, by decide,
    countingThresholdBase_of_lt_two (k := 0) (by decide) 3,
    by decide, by decide,
    countingThresholdBase_of_lt_two (k := 1) (by decide) 3,
    countingThresholdBase_zero 3⟩

-- The selected value feeds the numerical consumer at N = 16 (radius 1, tail 65) and N = 0.
example :
    (∑ j ∈ range (countingBChoiceCoeff 2 * 16 / countingThresholdBase 2 1 + 1),
      (countingDepthCoeff 2 (countingThresholdBase 2 1) * 16).choose j) = 65 ∧
    (∑ j ∈ range (countingBChoiceCoeff 2 * 16 / countingThresholdBase 2 1 + 1),
      (countingDepthCoeff 2 (countingThresholdBase 2 1) * 16).choose j) ≤ 2 ^ 17 ∧
    (∑ j ∈ range (countingBChoiceCoeff 3 * 0 / countingThresholdBase 3 2 + 1),
      (countingDepthCoeff 3 (countingThresholdBase 3 2) * 0).choose j) ≤ 2 :=
  ⟨by
      rw [width_two_budget_one]
      norm_num [countingBChoiceCoeff, countingDepthCoeff, sum_range_succ],
    sum_choose_le_countingThresholdBase (by decide) (by decide) 16,
    sum_choose_le_countingThresholdBase (by decide) (by decide) 0⟩
