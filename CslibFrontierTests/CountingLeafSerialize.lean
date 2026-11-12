/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.CountingLeaf.Serialize

open Turing Turing.MultiTapeTM Cslib.CountingLeaf Cslib.CountingLeaf.Serialize

private def emptyFields : RawInput := ⟨[], [], [], [], true, []⟩
private def padded : RawInput := ⟨[], [true, false, false], [true, false],
  [false, true], false, [false, false]⟩

-- Empty physical fields retain every delimiter and the singleton carry frame.
example : encRawInput emptyFields = [false, false, false, false, true, true, false] := by
  simp [emptyFields, frame]

-- This includes serialization, final destination rewind, and both host-input moves.
example (input out : List Bool) :
    machine.runFrom ((initial input emptyFields out).withState (some machine.q₀)) 19 =
      (final input emptyFields out).withState none := by
  simpa [emptyFields] using (runsBetween input emptyFields out).1

-- Noncanonical zero padding is copied physically, without free normalization.
example (input out : List Bool) :
    machine.runFrom ((initial input padded out).withState (some machine.q₀)) 51 =
      (final input padded out).withState none := by
  simpa [padded] using (runsBetween input padded out).1

example (input out : List Bool) :
    (final input padded out).workTapes (1 : Fin 6).castSucc = tapeOfList [true, false, false] ∧
    (final input padded out).workTapePos (1 : Fin 6).castSucc = 3 ∧
    (final input padded out).workTapePos (Fin.last 6) = 0 ∧
    (final input padded out).inputPos = 0 ∧
    (final input padded out).output = out := by
  simp only [final, finished, tapesCfg, Fin.lastCases_castSucc, Fin.lastCases_last]
  simp [fields, padded]

-- The destination contains precisely the decoder's encoding, not an uncharged abstract record.
example (input : List Bool) (q : RawInput) :
    (final input q []).workTapes (Fin.last 6) = tapeOfList (encRawInput q) := by
  simp [final, finished, tapesCfg]
