/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Computability.PolyTime.CNF.WeightedNormalization

/-! # Binary original normalization and backend composition clients -/

open Cslib.Logic.PL.WeightedRow Cslib.Logic.PL.WeightedRow.BinaryNormalization
open Turing.MultiTapeTM

namespace WeightedBinaryNormalizationTests

/-- Repeated opposite polarities, with a declared unused variable. -/
def mixed : Input := ([(0, true, 3), (0, false, 1), (1, true, 2)], 2)

example : constant 3 mixed = 1 := by decide
example : total 3 mixed = 4 := by decide
example : materialize 3 [mixed] = ([[2, 2, 0]], [1]) := by decide
example : analyze 3 [mixed] = (false, [0], true, false) := by decide

/-- A large binary weight is capped directly, without enumerating its magnitude. -/
def large : Input := ([(0, true, 2 ^ 80)], 2 ^ 80)

example : materialize 2 [large] = ([[-1, 0]], [-1]) := by decide
example : analyze 2 [large] = (false, [0], true, false) := by decide

example : analyze 1 [([(0, true, 2)], 1)] = (false, [0], true, false) := by decide
example : analyze 1 [([(0, true, 2)], 2)] = (false, [0], true, true) := by decide
example : analyze 2 [([(0, true, 1)], 0), ([(0, true, 1)], 1)] =
    (false, [0], false, false) := by decide

/-- True rows are deleted; rejected rows set the separate flag. -/
example : materialize 2 [([(0, true, 7), (0, false, 7)], 7)] = ([], []) := by decide
example : analyze 2 [([(0, true, 7), (0, false, 7)], 8)] =
    (true, [], true, false) := by decide
example : analyze 0 [] = (false, [], true, true) := by decide

/-- The same repeated-occurrence input in the reviewed finite representation. -/
def original : Occurrences 3 3 where
  var := ![0, 0, 1]
  sign := ![true, false, true]
  weight := ![3, 1, 2]
  positive := by decide
  target := 2

example : ofOccurrences original = mixed := by decide
example : materialize 3 [ofOccurrences original] =
    (Cslib.Logic.PL.WeightedRow.cappedMatrix [original.normalize 1 (by decide)],
      Cslib.Logic.PL.WeightedRow.cappedRhs [original.normalize 1 (by decide)]) := by
  simpa [List.finRange_succ] using
    materialize_ofOccurrences (fun _ : Fin 1 => original) (d := 1) (by decide)

example : ComputableInPolyTime (fun p : ℕ × List Input => analyze p.1 p.2)
    (encPair encUnary (encList encInput))
    (encPair encBool (encPair (encList encUnary) (encPair encBool encBool))) := analyze_polytime

example (k : ℕ) :
    (((mixed.1.map fun (j, (s, w)) =>
      if j = 0 ∧ s = true then (w : ℤ) else 0).take k).sum).natAbs.size ≤
       (encInput mixed).length + mixed.1.length :=
  aggregate_prefix_bits mixed 0 k true

end WeightedBinaryNormalizationTests
