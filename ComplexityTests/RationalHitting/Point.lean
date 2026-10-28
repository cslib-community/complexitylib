/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime.Point

/-!
# Regression tests for the per-point normalization and encoding program

Concrete column replacements, normalized matrix entries, matrix words, tuple words, and point
words, checked by the kernel and compiled, agreeing with `ExecutableGenerator.atPoint` and
`encodeTuple` on both singular and nonsingular inputs. Axiom guards cover the headline theorems.
-/

namespace ComplexityTests.RationalHitting.Point

open Cslib.Circuits Cslib.Circuits.Rational
open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Column replacement and Cramer normalization -/

example : cramerRows [[2, 0], [0, 2]] [[4, 2], [0, 6]] 0 1 = [[2, 0], [6, 2]] := by
  decide +kernel

example : cramerRows [[2, 0], [0, 2]] [[4, 2], [0, 6]] 1 0 = [[2, 4], [0, 0]] := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 0 0 = encodeRat 2 := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 0 1 = encodeRat 1 := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 1 0 = encodeRat 0 := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 1 1 = encodeRat 3 := by
  decide +kernel

example :
    matrixWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 =
      encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3 := by
  decide +kernel

example :
    pointWordOfTables [[[2, 0], [0, 2]], [[4, 2], [0, 6]]] =
      encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3 := by
  decide +kernel

example :
    pointWordsOfTables [[[2, 0], [0, 2]], [[4, 2], [0, 6]]] =
      [encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3] := by
  decide +kernel

-- Singular `U₀` produces `[]` for both `pointWordOfTables` and `pointWordsOfTables`.
example : pointWordOfTables [[[0, 0], [2, 0]], [[4, 2], [0, 6]]] = [] := by
  decide +kernel

example : pointWordsOfTables [[[0, 0], [2, 0]], [[4, 2], [0, 6]]] = [] := by
  decide +kernel

/-! ### Agreement with the executable generator at grid points -/

example : pointWord 0 1 2 1 1 1 1 = [] := by decide +kernel
example : pointWords 0 1 2 1 1 1 1 = [] := by decide +kernel

example : (ExecutableGenerator.atPoint 0 1 0 ![1, 1, 1]).elim [] encodeTuple = [] := by
  rw [← pointWord_eq 0 1 0 ![1, 1, 1]]
  decide +kernel

example : ((ExecutableGenerator.atPoint 0 1 0 ![1, 1, 1]).map encodeTuple).toList = [] := by
  rw [← pointWords_eq 0 1 0 ![1, 1, 1]]
  decide +kernel

/-- info: true -/
#guard_msgs in
#eval pointWord 1 2 4 2 1 2 3 ==
  (ExecutableGenerator.atPoint 1 2 1 ![1, 2, 3]).elim [] encodeTuple

/-! ### Polynomial-time certificates -/

example :
    ComputableInPolyTime (fun p : ℕ × ℕ => pointWordOfTables (liftRows p.1 p.2 p.1 p.2 p.1 p.2 p.1))
      (encPair encUnary encUnary) encBits := by
  fun_prop

example :
    ComputableInPolyTime
      (fun p : ℕ × ℕ => pointWordsOfTables (liftRows p.1 p.2 p.1 p.2 p.1 p.2 p.1))
      (encPair encUnary encUnary) (encList encBits) := by
  fun_prop

example :
    ComputableInPolyTime
      (fun p : ℕ × ℕ => pointWord p.1 p.2 p.1 p.2 p.1 p.2 p.1)
      (encPair encUnary encUnary) encBits := by
  fun_prop

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Rational.cramerRows_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cramerRows_eq

end ComplexityTests.RationalHitting.Point
