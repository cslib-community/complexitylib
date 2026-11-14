/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BinaryIncrement

/-! Growing counters and prefix-sensitive native clocks. -/

open Turing Turing.MultiTapeTM.BinaryIncrement

-- Growing an empty tape creates the canonical encoding of one in three transitions.
example : machine.runFrom
    (⟨some machine.q₀, 0, fun _ => tapeOfList [], fun _ => 0, [false]⟩ : Cfg 1 Bool _ []) 3 =
    ⟨none, 0, fun _ => tapeOfList [true], fun _ => 0, [false]⟩ := by
  simpa [initialOnes, Turing.MultiTapeTM.NatSucc.incr] using
    runFrom_machine (input := []) 0 [false] []

-- Overflow grows three one digits into four digits; rewinding is included.
example : machine.runFrom
    (⟨some machine.q₀, 1, fun _ => tapeOfList [true, true, true], fun _ => 0, []⟩ :
      Cfg 1 Bool _ []) 9 =
    ⟨none, 1, fun _ => tapeOfList [false, false, false, true], fun _ => 0, []⟩ := by
  simpa [initialOnes, Turing.MultiTapeTM.NatSucc.incr] using
    runFrom_machine (input := []) 1 [] [true, true, true]

-- A zero first digit stops carry immediately; high digits are preserved.
example : machine.runFrom
    (⟨some machine.q₀, 0, fun _ => tapeOfList [false, true, false, true], fun _ => 0, []⟩ :
      Cfg 1 Bool _ []) 3 =
    ⟨none, 0, fun _ => tapeOfList [true, true, false, true], fun _ => 0, []⟩ := by
  simpa [initialOnes, Turing.MultiTapeTM.NatSucc.incr] using
    runFrom_machine (input := []) 0 [] [false, true, false, true]

-- The exact clocks of eight growing increments sum to 38, below the aggregate budget 40.
example : totalClock 8 [] = 38 := by decide
