/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BinaryDecrement

open Cslib.BitString

example : decrement [false, false, true, true] = [true, true, false, true] := rfl
example : decrement [false, false, false] = [true, true, true] := rfl
example : decrementVisits [true, false, false, false, false] = 1 := rfl
example : decrementCost 8 [false, false, false] = 14 := rfl
example : lsbValue (decrement^[5] [false, true, true]) = 1 := by
  simpa [lsbValue] using lsbValue_iterate_decrement 5 [false, true, true] (by decide)
example (levels q : ℕ) (w : List Bool) (h : q ≤ 2 * levels) :
    decrementCost q w ≤ 4 * levels + w.length :=
  decrementCost_le_of_le_two_mul h w

open Turing Turing.MultiTapeTM

-- A low one-bit counter takes three native steps irrespective of the suffix length.
example {input : List Bool} (ip : Fin (input.length + 2)) (out suffix : List Bool) :
    binaryDecrement.runFrom
      ⟨some binaryDecrement.q₀, ip, fun _ => tapeOfList (true :: suffix), fun _ => 0, out⟩ 3 =
      ⟨none, ip, fun _ => tapeOfList (false :: suffix), fun _ => 0, out ++ [false]⟩ := by
  simpa [BinaryDecrement.zeros, decrement] using runFrom_binaryDecrement ip out (true :: suffix)

-- Underflow is reported by the same native scan, including on an empty counter.
example {input : List Bool} (ip : Fin (input.length + 2)) (out : List Bool) :
    binaryDecrement.runFrom
      ⟨some binaryDecrement.q₀, ip, fun _ => tapeOfList [], fun _ => 0, out⟩ 3 =
      ⟨none, ip, fun _ => tapeOfList [], fun _ => 0, out ++ [true]⟩ := by
  simpa [BinaryDecrement.zeros, decrement] using runFrom_binaryDecrement ip out []
