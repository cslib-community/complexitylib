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

private def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun value => value.elim⟩

-- Tape and list operations over infinite, generic, and empty alphabets.
example {Symbol : Type} (enc : Symbol ↪ List Bool) (tape : BiTape Bool) :
    ComputableInPolyTime writeWordAndMove
      (encPair (encBiTape encBits) encBits) (encBiTape encBits) ∧
    ComputableInPolyTime (fun values : List ℕ => (BiTape.mk₁ values.tail).head)
      (encList encUnary) (encOption encUnary) ∧
    ComputableInPolyTime (fun values : List Symbol => StackTape.mapSome values.tail)
      (encList enc) (encStackTape enc) ∧
    ComputableInPolyTime
      (fun pair : Option (List Bool) × StackTape (List Bool) => StackTape.cons pair.1 pair.2)
      (encPair (encOption encBits) (encStackTape encBits)) (encStackTape encBits) ∧
    ComputableInPolyTime (fun tape : BiTape Empty => tape.step (some none, .neg))
      (encBiTape encEmpty) (encBiTape encEmpty) ∧
    encStackTape encBool (StackTape.cons none StackTape.nil) = [] ∧
    (encStackTape encBool (StackTape.cons none (StackTape.mapSome [true]))).length = 6 ∧
    (encBiTape encBool tape).length ≤ 12 * tape.spaceUsed ∧
    ComputableInPolyTime (List.head? (α := Empty))
      (encList encEmpty) (encOption encEmpty) ∧
    ComputableInPolyTime (List.isEmpty (α := Symbol)) (encList enc) encBool ∧
    ComputableInPolyTime (List.isEmpty (α := Bool)) encBits encBool ∧
    ComputableInPolyTime (fun values : List ℕ => values.isEmpty)
      (encList encUnary) encBool ∧
    ComputableInPolyTime
      (fun tape : BiTape (List Bool) =>
        if tape.left.toList.isEmpty then tape.moveRight else tape.moveLeft)
      (encBiTape encBits) (encBiTape encBits) :=
  ⟨by unfold writeWordAndMove; fun_prop, by fun_prop, by fun_prop, .of_tidy (by polytime),
    by fun_prop, by decide, by decide, length_encBiTape_le encBool tape (bound := 1) (by simp),
    by fun_prop, by fun_prop, by fun_prop, .of_tidy (by polytime), by fun_prop⟩

end ComplexityTests.TapePolyTime
