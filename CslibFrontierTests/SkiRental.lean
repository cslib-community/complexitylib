/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Online.SkiRental

/-!
# Tests for ski rental

Concrete costs, the tight break-even instance, the `B = 1` edge case, and nonvacuity of the
deterministic lower bound for `CslibFrontier.DataStructure.Online.SkiRental`.
-/

public section

namespace CslibFrontierTests.SkiRental

open Cslib.DataStructure.Online Cslib.DataStructure.Online.SkiRental

/-! ### Concrete costs -/

/-- With purchase price `10`, skiing `3` days costs the break-even strategy `3` (it only rents). -/
example : (breakEven 10).cost false (List.replicate 3 ()) = 3 := by decide

/-- Skiing `12` days costs the break-even strategy `9 + 10 = 19`. -/
example : (breakEven 10).cost false (List.replicate 12 ()) = 19 := by decide

/-- The strategy that buys immediately pays `10` even for a single day. -/
example : (rentThenBuy 10 0).cost false [()] = 10 := by decide

/-- Renting every day and buying on the first day as offline schedules. -/
example : (problem 10).scheduleCost false (List.replicate 4 ()) (List.replicate 4 false) = 4 := by
  decide

example : (problem 10).scheduleCost false (List.replicate 12 ()) (List.replicate 12 true) = 10 := by
  decide

/-- Buying cannot be undone. -/
example : ¬ (problem 10).ValidSchedule false [(), ()] [true, false] :=
  fun h => Bool.false_ne_true (h.2.1 rfl)

/-! ### The tight break-even instance -/

/-- On exactly `B` days the break-even strategy pays `2B - 1` while the optimum pays `B`, so the
bound `B * ALG ≤ (2B - 1) * OPT` holds with equality. -/
example : (breakEven 10).cost false (List.replicate 10 ()) = 19 := breakEven_cost_replicate 10

example : 10 * (breakEven 10).cost false (List.replicate 10 ()) =
    19 * (problem 10).scheduleCost false (List.replicate 10 ()) (List.replicate 10 true) := by
  decide

/-- The break-even ratio applied to a concrete schedule. -/
example : 10 * (breakEven 10).cost false (List.replicate 12 ()) ≤
    19 * (problem 10).scheduleCost false (List.replicate 12 ()) (List.replicate 12 true) :=
  breakEven_mul_cost_le (validSchedule_replicate (fun _ => rfl) _)

/-! ### Competitiveness and the `B = 1` edge case -/

example : (breakEven 10).IsCompetitive 2 0 := breakEven_isCompetitive_two 10

example : (breakEven 10).IsCompetitive 1 9 := breakEven_isCompetitive_one 10

/-- With purchase price `1`, buying immediately is optimal: ratio `2 - 1/1 = 1`. -/
example : (breakEven 1).IsCompetitive 1 0 := breakEven_isCompetitive_one 1

/-! ### Deterministic lower bound -/

/-- No deterministic strategy is `(1, 0)`-competitive for `B = 10`. -/
example (A : DetStrategy (problem 10)) : ¬ A.IsCompetitive 1 0 := not_isCompetitive_one (by omega) A

/-- The rational ratio `1.89 < 1.9 = 2 - 1/10` is violated by every deterministic strategy,
including the break-even strategy itself. -/
example : ∃ reqs states, (problem 10).ValidSchedule false reqs states ∧
    189 * (problem 10).scheduleCost false reqs states < 100 * (breakEven 10).cost false reqs :=
  exists_ratio_violation_of_lt (breakEven 10) (by omega)

/-- The lower-bound witness has positive offline cost. -/
example (A : DetStrategy (problem 10)) :
    ∃ reqs states, (problem 10).ValidSchedule false reqs states ∧
    1 ≤ (problem 10).scheduleCost false reqs states ∧
    19 * (problem 10).scheduleCost false reqs states ≤ 10 * A.cost false reqs :=
  exists_witness (by omega) A

end CslibFrontierTests.SkiRental
