/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native streamed schedule readers)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadPort

/-!
# Streamed schedule reader regressions

The two-head schedule has rows `(2,0)`, `(0,2)`, `(1,1)`. Zero schedule suffixes continue
with digit zero, which denotes negative movement rather than a stationary head.
-/

public section

namespace ComplexityTests.ScheduleRead

open Turing.MultiTapePTM.BlockComputation.ScheduleRead

example : read 1 0 2 (380, 3) = 1 := by decide
example : read 1 0 0 (380, 3) = 1 := by decide
example : read 1 1 2 (380, 3) = 1 := by decide
example : read 1 1 1 (380, 3) = 1 := by decide
example : read 1 0 0 (380, 5) = 3 := by decide
example : read 1 0 2 (380, 0) = 0 := rfl
example : read 0 0 0 (0, 100) = 100 := by decide
example : read 0 0 2 (0, 100) = 0 := by decide
example : inWindow 0 0 (0, 3, 0, 2) = false := by decide
example : inWindow 0 0 (0, 3, 1, 2) = true := by decide
example : inWindow 0 0 (0, 3, 2, 0) = false := by decide

example : search 0 0 (0, 0, 1) = none := rfl
example : search 0 0 (0, 3, 0) = none := by decide
example : search 0 0 (0, 3, 1) = some 2 := by decide
example : search 0 0 (0, 3, 2) = some 2 := by decide
example : search 1 0 (380, 3, 0) = some 2 := by decide

-- The latest interval misses this block; the preceding one is the provider.
example : search 0 0 (20, 3, 2) = some 1 := by decide
example : origin 0 0 (0, 100) = (0, 100) := by decide
example : providerPort 0 0 (0, 3, 0) = none := by decide
example : providerPort 0 0 (20, 3, 2) = some 2 := by decide

example : providerMap 1 (380, 3) 0 2 = some 2 := by decide
example : providerMap 1 (0, 3) 0 0 = none := by decide

end ComplexityTests.ScheduleRead
