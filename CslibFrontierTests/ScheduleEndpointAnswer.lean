/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointAnswer

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ScheduleEndpointAnswer

/- Invalid and exhausted requests leave a nonempty, unused counter untouched and preserve the
previous output. Their native clocks do not depend on that counter's length. -/
example : RunsBetween machine
    (tapesCfg [true] ![[false], [true, false, true]] 0 0 [false, true])
    (tapesCfg [true] ![[false], [true, false, true]] 0 ![1, 0] [false, true, false]) 1 4 := by
  simpa using runsBetween_invalid [true] [true, false, true] [false, true]

example : RunsBetween machine
    (tapesCfg [] ![[true, false], [true, false, true]] 0 0 [true, false])
    (tapesCfg [] ![[true, false], [true, false, true]] 0 ![2, 0]
      [true, false, true, false]) 2 6 := by
  simpa using runsBetween_exhausted [] [true, false, true] [true, false]

/- The successful index zero has an empty payload, but still emits both true tags. -/
example : RunsBetween machine
    (tapesCfg [] ![[true, true], []] 0 0 [false])
    (tapesCfg [] ![[true, true], []] 0 ![2, 0] [false, true, true]) 3 8 := by
  simpa using runsBetween_found [] [] [false]

/- A nonzero payload is copied once, with the final head and every output bit specified. -/
example : RunsBetween machine
    (tapesCfg [] ![[true, true], [true, false, true]] 0 0 [false])
    (tapesCfg [] ![[true, true], [true, false, true]] 0 ![2, 3]
      [false, true, true, true, false, true]) 6 14 := by
  simpa using runsBetween_found [] [true, false, true] [false]

example : encAnswer none = [false] := by decide
example : encAnswer (some none) = [true, false] := by decide
example : encAnswer (some (some 0)) = [true, true] := by decide
example : encAnswer (some (some 5)) = [true, true, true, false, true] := by decide
