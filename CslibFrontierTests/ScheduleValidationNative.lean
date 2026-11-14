/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleValidationNative

open Turing.MultiTapeTM Turing.MultiTapeTM.ScheduleValidation

-- Adjacent ones across the pair boundary are accepted by the actual finite machine.
example : (reader 1).toTM.ComputesInTimeAndSpace
    [false, true, true, false] [true] 11 0 := by
  simpa [ScheduleBits.validate, ScheduleBits.validPairs, ScheduleBits.decodePair] using
    computes_validate 1 [false, true, true, false]

-- The same machine rejects an aligned invalid pair in a complete row.
example : (reader 1).toTM.ComputesInTimeAndSpace
    [false, false, true, true] [false] 11 0 := by
  simpa [ScheduleBits.validate, ScheduleBits.validPairs, ScheduleBits.decodePair] using
    computes_validate 1 [false, false, true, true]

-- Valid pairs still fail if the final row is incomplete.
example : (reader 1).toTM.ComputesInTimeAndSpace [true, false] [false] 7 0 := by
  simpa [ScheduleBits.validate, ScheduleBits.validPairs, ScheduleBits.decodePair] using
    computes_validate 1 [true, false]

-- No work heads means one input-head pair per row, including an empty table.
example : (reader 0).toTM.ComputesInTimeAndSpace [] [true] 3 0 := by
  simpa [ScheduleBits.validate, ScheduleBits.validPairs] using computes_validate 0 []

-- Ending in the second-bit state rejects an incomplete movement pair.
example : (reader 0).toTM.ComputesInTimeAndSpace [false] [false] 5 0 := by
  simpa [ScheduleBits.validate, ScheduleBits.validPairs] using computes_validate 0 [false]
