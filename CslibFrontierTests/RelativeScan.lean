/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScan

/-! Concrete native scanner runs, including both boundary signs, exhaustion, and blank markers. -/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.RelativeScan

-- The current candidate is tested before its outgoing move is applied.
example : evaluate [1] 1 = ⟨0, 1, true⟩ := by simp [evaluate]

-- Empty suffixes have no candidate, even if the carried displacement is in the window.
example : evaluate [] 0 = ⟨0, 0, false⟩ := by simp [evaluate]

-- Two negative moves bring the third candidate into the right boundary of the window.
example : machine.runFrom
    ((config [] (encode [-1, -1, 1]) 0 3 [false]).withState (some false)) 5 =
    (config [] (encode [-1, -1, 1]) 4 1 [false, true]).withState none := by
  simpa [evaluate] using runFrom_machine [] (encode [-1, -1, 1]) [] [-1, -1, 1]
    rfl 3 [false]

-- The opposite sign uses the same physical marker tape.
example : machine.runFrom
    ((config [] (encode [1, 1, 0]) 0 (-3) []).withState (some false)) 5 =
    (config [] (encode [1, 1, 0]) 4 (-1) [true]).withState none := by
  simpa [evaluate] using runFrom_machine [] (encode [1, 1, 0]) [] [1, 1, 0] rfl (-3) []

-- Exhaustion keeps the complete source and appends a false result.
example : machine.runFrom
    ((config [] (encode [0, 0]) 0 3 []).withState (some false)) 5 =
    (config [] (encode [0, 0]) 4 3 [false]).withState none := by
  simpa [evaluate] using runFrom_machine [] (encode [0, 0]) [] [0, 0] rfl 3 []

-- Marker creation is charged: distance 2 needs one pair, so the full run takes eight steps.
example : RunsBetween (initialized 4)
    (tapesCfg [] ![encode [-1, 1], []] 0 ![0, 0] [])
    (config [] (encode [-1, 1]) 2 1 [true]) 8 20 := by
  simpa [initialDistance, evaluate] using
    runsBetween_initialized [] (encode [-1, 1]) [] [-1, 1] rfl [] 4
