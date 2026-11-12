/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySavePath

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open CarrySavePath

-- A concrete phase starts amid nonempty counters, a persistent path, and a drifting frontier.
example (input : List Bool) :
    let cfg := CarrySaveStream.config (k := 2) (input := input) [true, true] [false, true]
      [false, true, false, true] [true, true, true] 2 true
    machine.runFrom (cfg.withState (some machine.q₀)) 28 =
      (prepared cfg [false, true, false, true]).withState none := by
  exact (runsBetween [true, true] [false, true] [false, true, false, true]
    [true, true, true] 2 true).1

-- Every controller tape's contents are preserved, including the source path itself.
example {input : List Bool} (cfg : Cfg 8 Bool Unit input) (path : List Bool) (i : Fin 6) :
    (prepared cfg path).workTapes (CarrySaveStream.coreEmb 2 i) =
      cfg.workTapes (CarrySaveStream.coreEmb 2 i) := by
  have hne : CarrySaveStream.coreEmb 2 i ≠ (6 : Fin 8) := by
    intro h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    change i.val = 6 at hv
    omega
  simp [prepared, hne]

-- Only the source head changes; the unary frontier is unchanged.
example {input : List Bool} (cfg : Cfg 8 Bool Unit input) (path : List Bool) :
    (prepared cfg path).workTapePos 2 = 0 ∧
    (prepared cfg path).workTapePos 4 = cfg.workTapePos 4 ∧
    (prepared cfg path).inputPos = cfg.inputPos := by
  simp [prepared]

-- Destination carries the reversed path; marker cleanup restores the second private tape.
example {input : List Bool} (height bits path unary : List Bool) (frontier : ℤ) (status : Bool) :
    let cfg := CarrySaveStream.config (k := 2) (input := input)
      height bits path unary frontier status
    (prepared cfg path).workTapes 6 = tapeOfList path.reverse ∧
    (prepared cfg path).workTapes 7 = fun _ => none := by
  simp [prepared, CarrySaveStream.config_extra_tape, CarrySaveStream.Scratch.blank]
