/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameRound

/-! Native round preparation reads the move bit, discards the old player, and preserves output. -/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.WordGameRound

-- A true move is read from control cell one; the false player bit is discarded.
example (input out : List Bool) :
    (gatherOn 3).runFrom
      ((queryConfig 3 input [false, true] [false, true] [] out).withState
        (some (gatherOn 3).q₀)) 35 =
      (queryConfig 3 input [] [] [true, true, false, false, true] out).withState none := by
  simpa using (runsBetween_gatherOn 3 input [false, true] out false true).1

-- The opposite player/move pair changes the query bit, with the same concrete clock.
example (input out : List Bool) :
    (gatherOn 1).runFrom
      ((queryConfig 1 input [true, false] [true, false] [] out).withState
        (some (gatherOn 1).q₀)) 35 =
      (queryConfig 1 input [] [] [true, false, false, true, false] out).withState none := by
  simpa using (runsBetween_gatherOn 1 input [true, false] out true false).1

-- Empty metadata still writes the complete framed Boolean and clears both source tapes.
example (input out : List Bool) :
    (gatherOn 0).runFrom
      ((queryConfig 0 input [true, true] [] [] out).withState
        (some (gatherOn 0).q₀)) 23 =
      (queryConfig 0 input [] [] [true, true, false] out).withState none := by
  simpa using (runsBetween_gatherOn 0 input [] out true true).1

-- The charged host-head adapter restores position zero and the existing output prefix.
example (input : List Bool) :
    (gatherOn 2).fromLeftBlank.runFrom
      ((config 2 input [false, false] [] [true, false, true]).withState
        (some (gatherOn 2).fromLeftBlank.q₀)) 25 =
      ({ queryConfig 2 input [] [] [true, false, false] [true, false, true] with
        inputPos := 0 }).withState none := by
  exact ((runsBetween_gatherOn 2 input [] [true, false, true] false false).fromLeftBlank
    rfl rfl).1
