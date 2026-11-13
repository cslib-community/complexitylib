/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.CursorCount

/-! Native cursor recovery preserves source suffixes and pre-existing output. -/

open Turing.MultiTapeTM Turing.MultiTapeTM.CursorCount

-- The empty prefix needs only the initial move, failed loop test, and final restoration.
example : RunsBetween machine (config [] [true, false] [] 0 [true])
    (config [] [true, false] [] 0 [true]) 3 8 := by
  simpa using runsBetween [] [true, false] [true] 0 (by decide)

-- Three pairs become canonical binary 3; the two untraversed high source cells survive.
example : RunsBetween machine
    (config [] [false, true, false, false, true, true, false, true] [] 6 [false, true])
    (config [] [false, true, false, false, true, true, false, true]
      [true, true] 0 [false, true]) 27 56 := by
  have hbits : Nat.bits 3 = [true, true] := by decide
  simpa [hbits] using runsBetween [] [false, true, false, false, true, true, false, true]
    [false, true] 3 (by decide)
