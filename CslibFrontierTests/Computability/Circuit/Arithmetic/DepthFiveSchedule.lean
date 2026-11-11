/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Schedule

/-!
# The balanced layer schedule

For `n = 9`, `s = 3`, `k = 3` and `m = 6` the balanced schedule is the word `VUUVUUVUU`.
-/

@[expose] public section

namespace CslibFrontierTests.DepthFive

open Cslib.Circuits.DepthFive

/-- Parameters with nine layers, three of them differentiated. -/
def params₉ : Params := ⟨9, 3, 3, 6, 0, 0, rfl, rfl⟩

/-- The balanced schedule for nine layers is `VUUVUUVUU`. -/
theorem isV_params₉ : (List.finRange 9).map params₉.isV =
    [true, false, false, true, false, false, true, false, false] := by decide

end CslibFrontierTests.DepthFive
