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

/-! ### Column replacement, Cramer normalization, grid agreement, and certificates -/

/-- info: true -/
#guard_msgs in
#eval pointWord 1 2 4 2 1 2 3 ==
  (ExecutableGenerator.atPoint 1 2 1 ![1, 2, 3]).elim [] encodeTuple

example :
    (cramerRows [[2, 0], [0, 2]] [[4, 2], [0, 6]] 0 1 = [[2, 0], [6, 2]] ∧
      cramerRows [[2, 0], [0, 2]] [[4, 2], [0, 6]] 1 0 = [[2, 4], [0, 0]] ∧
      matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 0 0 = encodeRat 2 ∧
      matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 0 1 = encodeRat 1 ∧
      matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 1 0 = encodeRat 0 ∧
      matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 1 1 = encodeRat 3 ∧
      matrixWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 =
        encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3 ∧
      pointWordOfTables [[[2, 0], [0, 2]], [[4, 2], [0, 6]]] =
        encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3 ∧
      pointWordsOfTables [[[2, 0], [0, 2]], [[4, 2], [0, 6]]] =
        [encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3] ∧
      pointWordOfTables [[[0, 0], [2, 0]], [[4, 2], [0, 6]]] = [] ∧
      pointWordsOfTables [[[0, 0], [2, 0]], [[4, 2], [0, 6]]] = []) ∧
    (pointWord 0 1 2 1 1 1 1 = [] ∧ pointWords 0 1 2 1 1 1 1 = [] ∧
      pointWord 0 1 (CyclotomicRing.dimension 0) (CyclotomicRing.degree 0) 1 1 1 =
        (ExecutableGenerator.atPoint 0 1 0 ![1, 1, 1]).elim [] encodeTuple ∧
      pointWords 1 2 (CyclotomicRing.dimension 1) (CyclotomicRing.degree 1) 1 2 3 =
        ((ExecutableGenerator.atPoint 1 2 1 ![1, 2, 3]).map encodeTuple).toList) ∧
    ComputableInPolyTime pointWordOfTables (encList (encList (encList encIntBin))) encBits ∧
    ComputableInPolyTime pointWordsOfTables
      (encList (encList (encList encIntBin))) (encList encBits) ∧
    ComputableInPolyTime
      (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
        pointWord q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair encUnary encUnary))))))
      encBits :=
  ⟨by decide +kernel,
    ⟨by decide +kernel, by decide +kernel, pointWord_eq 0 1 0 ![1, 1, 1],
      pointWords_eq 1 2 1 ![1, 2, 3]⟩,
    pointWordOfTables_polytime, pointWordsOfTables_polytime, pointWord_polytime⟩

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Rational.cramerRows_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cramerRows_eq

end ComplexityTests.RationalHitting.Point
