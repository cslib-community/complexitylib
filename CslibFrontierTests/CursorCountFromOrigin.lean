/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.CursorCountFromOrigin

open Turing.MultiTapeTM Turing.MultiTapeTM.CursorCount

-- The empty word returns the canonical zero counter and preserves prior output.
example : RunsBetween fromOrigin (config [] [] [] 0 [true])
    (config [] [] [] 0 [true]) 4 10 := by
  simpa using runsBetween_fromOrigin [] [] [true] 0 rfl

-- Both source cells survive and both heads return to zero, including with a nonempty host input.
example : RunsBetween fromOrigin (config [true, false] [true, false] [] 0 [false, true])
    (config [true, false] [true, false] [true] 0 [false, true]) 14 30 := by
  simpa using runsBetween_fromOrigin [true, false] [true, false] [false, true] 1 rfl

-- Four increments cross a binary-width boundary. Cell values do not affect counting.
example : RunsBetween fromOrigin
    (config [] [false, true, true, true, false, false, true, false] [] 0 [])
    (config [] [false, true, true, true, false, false, true, false] [false, false, true] 0 [])
    44 90 := by
  have hb : Nat.bits 4 = [false, false, true] := by decide
  simpa [hb] using runsBetween_fromOrigin []
    [false, true, true, true, false, false, true, false] [] 4 rfl

-- A caller can count every pair of an input-first schedule before dividing by its fixed row width.
example (input raw out : List Bool) (k q : ℕ) (hraw : raw.length = 2 * (k + 1) * q) :
    RunsBetween fromOrigin (config input raw [] 0 out)
      (config input raw ((k + 1) * q).bits 0 out)
      (10 * ((k + 1) * q) + 4) (2 * (10 * ((k + 1) * q) + 5)) := by
  apply runsBetween_fromOrigin
  simpa only [Nat.mul_assoc] using hraw
