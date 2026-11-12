/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendWord

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.AppendWord

-- Appending does not rescan or overwrite the existing destination prefix.
example (input out : List Bool) :
    (machine true).runFrom
      ((config input [false, true] [true, false, true] 0 out).withState (some none)) 5 =
        (config input [false, true]
          [true, false, true, true, false, true, true, false] 2 out).withState none := by
  simpa [clock, fragment, frame] using runFrom true input [] [false, true] [true, false, true] out

-- An empty framed field still emits its delimiter.
example (input out : List Bool) :
    (machine true).runFrom ((config input [] [true] 0 out).withState (some none)) 1 =
      (config input [] [true, false] 0 out).withState none := by
  simpa [clock, fragment, frame] using runFrom true input [] [] [true] out

-- An empty final raw field only performs its terminating blank test.
example (input out : List Bool) :
    (machine false).runFrom ((config input [] [true] 0 out).withState (some none)) 1 =
      (config input [] [true] 0 out).withState none := by
  simpa [clock, fragment] using runFrom false input [] [] [true] out
