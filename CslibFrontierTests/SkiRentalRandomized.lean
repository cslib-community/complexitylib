/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Online.SkiRental.Randomized

/-!
# Tests for randomized ski rental

Explicit `B = 2` and `B = 3` distributions with their exact rational ratios, the matching adversary
distributions, the point-mass embedding of deterministic strategies, and nonvacuity of the
competitive and lower-bound predicates for
`CslibFrontier.DataStructure.Online.SkiRental.Randomized`.
-/

@[expose] public section

namespace CslibFrontierTests.SkiRentalRandomized

open Cslib.DataStructure.Online Cslib.DataStructure.Online.SkiRental
open scoped ENNReal

/-! ### Exact ratios -/

/-- `B = 1`: buying at once is optimal and the ratio is `1`. -/
example : randomizedRatio 1 = 1 := by
  rw [randomizedRatio_eq le_rfl]
  norm_num

/-- `B = 2`: ratio `4 / (4 - 1) = 4/3`. -/
example : randomizedRatio 2 = 4 / 3 := by
  rw [randomizedRatio_eq (by norm_num)]
  norm_num

/-- `B = 3`: ratio `27 / (27 - 8) = 27/19`. -/
example : randomizedRatio 3 = 27 / 19 := by
  rw [randomizedRatio_eq (by norm_num)]
  norm_num

/-- `4/3 < 2 - 1/2`: randomization beats the deterministic break-even ratio at `B = 2`. -/
example : randomizedRatio 2 < 2 - 1 / 2 := by
  have := randomizedRatio_lt_two_sub (B := 2) le_rfl
  norm_num at this ⊢
  linarith

/-! ### The equalizing distributions -/

/-- `B = 2`: rent `0` days with weight `1`, rent `1` day with weight `2` (total `3`). -/
example : buyWeight 2 0 = 1 ∧ buyWeight 2 1 = 2 := by decide

/-- `B = 3`: weights `4, 6, 9` (total `27 - 8 = 19`). -/
example : buyWeight 3 0 = 4 ∧ buyWeight 3 1 = 6 ∧ buyWeight 3 2 = 9 := by decide

/-- So for `B = 2` the strategy buys on day `1` with probability `1/3` and on day `2` with
probability `2/3`. -/
example : rentDays 2 0 = 1 / 3 ∧ rentDays 2 1 = 2 / 3 := by
  simp only [rentDays_apply, buyWeight]
  constructor <;> norm_num

/-- For `B = 3` the strategy buys on days `1, 2, 3` with probabilities `4/19, 6/19, 9/19`. -/
example : rentDays 3 0 = 4 / 19 ∧ rentDays 3 1 = 6 / 19 ∧ rentDays 3 2 = 9 / 19 := by
  simp only [rentDays_apply, buyWeight]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- `B = 2`: on one ski day the expected cost is `(1/3) * 2 + (2/3) * 1 = 4/3 = ratio * OPT`. -/
example : RandStrategy.expectedCost (randomRentThenBuy 2) false [()] = ENNReal.ofReal (4 / 3) := by
  rw [expectedCost_randomRentThenBuy, randomizedRatio_eq (by norm_num)]
  norm_num

/-- `B = 3`: skiing ten days costs `27/19 * 3` in expectation. -/
example : RandStrategy.expectedCost (randomRentThenBuy 3) false (List.replicate 10 ()) =
    ENNReal.ofReal (27 / 19) * 3 := by
  rw [expectedCost_randomRentThenBuy, List.length_replicate, randomizedRatio_eq (by norm_num)]
  norm_num

/-! ### Competitiveness -/

example : RandStrategy.IsCompetitive (randomRentThenBuy 3) (ENNReal.ofReal (27 / 19)) 0 := by
  have h := randomRentThenBuy_isCompetitive 3
  rwa [randomizedRatio_eq (by norm_num), show ((3 : ℕ) : ℝ) ^ 3 / ((3 : ℕ) ^ 3 - ((3 : ℕ) - 1) ^ 3)
    = 27 / 19 by norm_num] at h

example : RandStrategy.IsCompetitive (randomRentThenBuy 10)
    (ENNReal.ofReal (Real.exp 1 / (Real.exp 1 - 1))) 0 :=
  randomRentThenBuy_isCompetitive_exp 10

/-- A deterministic strategy as a point mass: the break-even strategy is `(2, 0)`-competitive in
expectation. -/
example : RandStrategy.IsCompetitive (PMF.pure (breakEven 10)) (2 : ℕ) (0 : ℕ) :=
  (RandStrategy.isCompetitive_pure_iff _ 2 0).mpr (breakEven_isCompetitive_two 10)

/-! ### The adversary -/

/-- `B = 2`: ski `1` day or `3` days, each with weight `1`. -/
example : advWeight 2 none = 1 ∧ advWeight 2 (some 0) = 1 ∧
    advDays 2 none = 3 ∧ advDays 2 (some 0) = 1 := by decide

/-- `B = 3`: ski `1`, `2` or `5` days with weights `3`, `2`, `4` (total `9 = 3^2`). -/
example : advWeight 3 (some 0) = 3 ∧ advWeight 3 (some 1) = 2 ∧ advWeight 3 none = 4 ∧
    advDays 3 (some 0) = 1 ∧ advDays 3 (some 1) = 2 ∧ advDays 3 none = 5 := by decide

/-- For `B = 3` the weighted optimum is `3 * 1 + 2 * 2 + 4 * 3 = 19 = 27 - 8`. -/
example : ∑ o, advWeight 3 o * min (advDays 3 o) 3 = 19 := sum_advWeight_mul_min 3

/-- Against the `B = 3` adversary, the break-even strategy pays the weighted cost
`3 * 1 + 2 * 2 + 4 * 5 = 27 = 3^3`, matching the bound with equality. -/
example : ∑ o, advWeight 3 o * (breakEven 3).cost false (List.replicate (advDays 3 o) ()) = 27 := by
  simp only [Fintype.sum_option, cost_rentThenBuy, List.length_replicate]
  decide

/-! ### Lower bound -/

/-- No randomized strategy for `B = 2` is `(5/4, 0)`-competitive, since `5/4 < 4/3`. -/
example (μ : RandStrategy (problem 2)) :
    ¬ RandStrategy.IsCompetitive μ (ENNReal.ofReal (5 / 4)) 0 := by
  refine not_isCompetitive_of_lt μ ((ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_)
  · rw [randomizedRatio_eq (by norm_num)]
    norm_num
  · rw [randomizedRatio_eq (by norm_num)]
    norm_num

/-- In particular the equalizing strategy for `B = 2` is `4/3`- but not `5/4`-competitive. -/
example : ¬ RandStrategy.IsCompetitive (randomRentThenBuy 2) (ENNReal.ofReal (5 / 4)) 0 := by
  refine not_isCompetitive_of_lt _ ((ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_) <;>
    rw [randomizedRatio_eq (by norm_num)] <;> norm_num

end CslibFrontierTests.SkiRentalRandomized
