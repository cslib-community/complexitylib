/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.CopyBlock

/-!
# Local block transfers on nonempty tapes

The source contains a physical blank inside the payload. Source, target and counter heads
start at different nonzero positions; surrounding cells, the input cursor and earlier output
must survive both copying and source erasure. Counter marks need not have the same value.
-/

namespace ComplexityTests.CopyBlock

open Turing Turing.MultiTapeTM

private def tapes (i : Fin 3) (z : ℤ) : Option Bool :=
  if i = 0 then
    if z = -3 ∨ z = 0 then some false else if z = -2 ∨ z = 1 then some true else none
  else if i = 1 then
    if 3 ≤ z ∧ z ≤ 7 then some false else none
  else
    if z = -2 ∨ z = 0 then some false else if z = -1 ∨ z = 1 ∨ z = 3 then some true else none

private def initial : Cfg 3 Bool Unit [true, false] :=
  ⟨some (), 2, tapes, fun i => if i = 0 then -2 else if i = 1 then 4 else -1, [false, true]⟩

private noncomputable def result (erase : Bool) : Cfg 3 Bool Unit [true, false] :=
  (copyBlock erase).runFrom initial 4

private theorem counter_nonblank (j : ℕ) (hj : j < 3) :
    initial.workTapes 2 (initial.workTapePos 2 + j) ≠ none := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide

private theorem result_eq (erase : Bool) :
    result erase = Turing.MultiTapeTM.CopyBlock.finish erase initial 3 :=
  Turing.MultiTapeTM.CopyBlock.runFrom_copyBlock erase initial 3 rfl counter_nonblank (by decide)

-- A blank payload is copied as a blank, rather than ending the transfer or preserving the
-- previous destination symbol. The exterior cells at 3 and 7 retain their values.
example :
    ([3, 4, 5, 6, 7] : List ℤ).map ((result false).workTapes 1) =
      [some false, some true, none, some false, some false] ∧
    ([-3, -2, -1, 0, 1] : List ℤ).map ((result false).workTapes 0) =
      [some false, some true, none, some false, some true] := by
  rw [result_eq]
  decide

-- Erasure touches exactly the source interval. An extra mark beyond the counter terminator
-- remains in place, so the transfer length is controlled by the first counter blank.
example :
    ([-3, -2, -1, 0, 1] : List ℤ).map ((result true).workTapes 0) =
      [some false, none, none, none, some true] ∧
    ([3, 4, 5, 6, 7] : List ℤ).map ((result true).workTapes 1) =
      [some false, some true, none, some false, some false] ∧
    ([-2, -1, 0, 1, 2, 3] : List ℤ).map ((result true).workTapes 2) =
      [some false, none, none, none, none, some true] := by
  rw [result_eq]
  decide

-- Three copied cells require a fourth transition to halt; the input head and output stay put.
example :
    ((copyBlock false).runFrom initial 3).state = some () ∧
    (result false).state = none ∧
    (result true).state = none ∧
    ([0, 1, 2] : List (Fin 3)).map ((result true).workTapePos) = [1, 7, 2] ∧
    (result false).inputPos = 2 ∧ (result true).inputPos = 2 ∧
    (result false).output = [false, true] ∧ (result true).output = [false, true] := by
  rw [Turing.MultiTapeTM.CopyBlock.runFrom_progress false initial 3 rfl counter_nonblank,
    result_eq false, result_eq true]
  decide

private def zeroCount : Cfg 3 Bool Unit [true, false] :=
  { initial with workTapePos := fun i => if i = 2 then 2 else initial.workTapePos i }

-- A blank initial counter halts immediately, even with nonblank source and destination cells.
example :
    (let c := (copyBlock true).runFrom zeroCount 1;
      c.state = none ∧ c.workTapes 0 (-2) = some true ∧
      c.workTapes 1 4 = some false ∧ c.workTapes 2 3 = some true ∧
      ([0, 1, 2] : List (Fin 3)).map c.workTapePos = [-2, 4, 2] ∧
      c.inputPos = 2 ∧ c.output = [false, true]) := by
  rw [Turing.MultiTapeTM.CopyBlock.runFrom_copyBlock true zeroCount 0 rfl
    (by intro j hj; omega) (by decide)]
  decide

-- The native contract preserves every exterior target cell, including those not listed above.
example (z : ℤ) (hz : z < 4 ∨ 7 ≤ z) :
    (result true).workTapes 1 z = initial.workTapes 1 z := by
  rw [result, Turing.MultiTapeTM.CopyBlock.runFrom_copyBlock true initial 3 rfl
    counter_nonblank (by decide)]
  change Turing.MultiTapeTM.CopyBlock.writeBlock (initial.workTapes 1) 4
    (fun j => initial.workTapes 0 (-2 + j)) 3 z = initial.workTapes 1 z
  exact Turing.MultiTapeTM.CopyBlock.writeBlock_apply_of_outside _ _ _ _ (by omega)

example :
    (MultiTapeNTM.RunPath.ofDeterministic (copyBlock true) initial 4).space ≤ 12 := by
  exact Turing.MultiTapeTM.CopyBlock.space_copyBlock_le true initial 3 rfl
    counter_nonblank (by decide)

end ComplexityTests.CopyBlock
