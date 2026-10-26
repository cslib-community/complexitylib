/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
import Complexity.Tactic.PolyTime

/-! Tape programs over infinite and empty alphabets, using the ordinary functional API. -/

namespace ComplexityTests.TapePolyTime

open Cslib.Turing Turing.MultiTapeTM

-- Symbols themselves may be arbitrarily long words. Their encodings are charged in full.
private def writeWordAndMove (input : BiTape (List Bool) × List Bool) : BiTape (List Bool) :=
  (input.1.write (some input.2)).moveRight

example : ComputableTidilyInPolyTime writeWordAndMove
    (encPair (encBiTape encBits) encBits) (encBiTape encBits) := by
  unfold writeWordAndMove
  fun_prop

-- Construction and projections compose through a discarded first input element.
example : ComputableTidilyInPolyTime (fun values : List ℕ => (BiTape.mk₁ values.tail).head)
    (encList encUnary) (encOption encUnary) := by fun_prop

-- A framed tail must determine its element encoding without annotations inside the program.
example {Symbol : Type} (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime (fun values : List Symbol => StackTape.mapSome values.tail)
      (encList enc) (encStackTape enc) := by fun_prop

-- A computed cell and a computed stack use the same encoding, even over an infinite alphabet.
example : ComputableTidilyInPolyTime
    (fun pair : Option (List Bool) × StackTape (List Bool) => StackTape.cons pair.1 pair.2)
    (encPair (encOption encBits) (encStackTape encBits)) (encStackTape encBits) := by polytime

private def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun value => value.elim⟩

-- No inhabitant of the alphabet is needed: the only cell value is blank.
example : ComputableTidilyInPolyTime (fun tape : BiTape Empty => tape.step (some none, .neg))
    (encBiTape encEmpty) (encBiTape encEmpty) := by fun_prop

-- Interior blanks consume framed storage, whereas a blank beyond all stored cells is omitted.
example : encStackTape encBool (StackTape.cons none StackTape.nil) = [] ∧
    (encStackTape encBool (StackTape.cons none (StackTape.mapSome [true]))).length = 6 := by
  decide

-- The global bit-symbol bound gives a linear bound on each complete stored tape.
example (tape : BiTape Bool) : (encBiTape encBool tape).length ≤ 12 * tape.spaceUsed :=
  length_encBiTape_le encBool tape (bound := 1) (by simp)

-- The same inspection API works for an empty element type.
example : ComputableTidilyInPolyTime (List.head? (α := Empty))
    (encList encEmpty) (encOption encEmpty) := by fun_prop

-- The generic capability theorem alone leaves the element encoding undetermined in proof search.
example {Symbol : Type} (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime (List.isEmpty (α := Symbol)) (encList enc) encBool := by fun_prop

example : ComputableTidilyInPolyTime (List.isEmpty (α := Bool)) encBits encBool := by fun_prop

example : ComputableTidilyInPolyTime (fun values : List ℕ => values.isEmpty)
    (encList encUnary) encBool := by polytime

example : ComputableTidilyInPolyTime
    (fun tape : BiTape (List Bool) =>
      if tape.left.toList.isEmpty then tape.moveRight else tape.moveLeft)
    (encBiTape encBits) (encBiTape encBits) := by fun_prop

end ComplexityTests.TapePolyTime
