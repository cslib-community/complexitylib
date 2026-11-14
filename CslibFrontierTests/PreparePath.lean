/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PreparePath

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.PreparePath

-- The empty path is a real run, including input positioning and marker cleanup.
example (input out : List Bool) :
    machine.runFrom ((initial input [] out).withState (some machine.q₀)) 12 =
      (final input [] out).withState none := by
  simpa using (runsBetween input [] out).1

-- Leading-zero padding is retained, while the decoded candidate is still five.
example (input out : List Bool) :
    machine.runFrom
      ((initial input [false, true, false, true] out).withState (some machine.q₀)) 28 =
        (final input [false, true, false, true] out).withState none := by
  simpa using (runsBetween input [false, true, false, true] out).1

example : ofBits [true, false, true, false] = 5 := by decide

-- The source path is preserved and the query tape contains the little-endian digits.
example (input out : List Bool) :
    (final input [false, true, false, true] out).workTapes 0 =
      tapeOfList [true, false, true, false] ∧
    (final input [false, true, false, true] out).workTapes 1 =
      tapeOfList [false, true, false, true] := by
  simp [final, tapesCfg]

-- A nonempty ambient output is preserved; the host input is restored to its left blank.
example (input path : List Bool) :
    (machine.runFrom ((initial input path [true, false]).withState (some machine.q₀))
      (4 * path.length + 12)).output = [true, false] ∧
    (machine.runFrom ((initial input path [true, false]).withState (some machine.q₀))
      (4 * path.length + 12)).inputPos = 0 := by
  rw [(runsBetween input path [true, false]).1]
  simp [final, tapesCfg, Cfg.withState]
