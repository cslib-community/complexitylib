/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (integrated sorted full-state matching regression tests)

public import CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORDecision
import all CslibFrontier.Cryptanalysis.AddXNORChain
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration

/-!
These clients execute the original input route, including actual inverse generation,
full-state collisions, sorting, cross-side scanning and original-order readback.
The route stores both half spaces; these examples do not assert smaller-class space.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

example : SortedMatch.run (0, ([], [])) = none := by decide +kernel
example : SortedMatch.run (3, ([(1, 0), (1, 0)], [(2, 0)])) = none := by decide +kernel
example : SortedMatch.run (0, ([(0, 4), (0, 4)], [(0, 7), (0, 8)])) = some (4, 7) := by
  decide +kernel
example : SortedMatch.run (3, ([], [(0, 0), (0, 1)])) = none := by decide +kernel
example : SortedMatch.run (3, ([(2, 9)], [(1, 3), (2, 8)])) = some (9, 8) := by
  decide +kernel

-- Addition by one is not self-inverse. The generated inverse states are seven and six.
example : SortedMeet.inverse ((3, 0), [1]) = [(7, 0), (6, 1)] := by decide +kernel
example : SortedMeet.run ((3, 0), [7, 1]) = some [false] := by decide +kernel
example : SortedMeet.run ((3, 0), [6, 1]) = some [true] := by decide +kernel
example : SortedMeet.run ((3, 0), [0, 1]) = none := by decide +kernel
example : SortedMeet.run ((3, 0), [0]) = some [] := by decide +kernel
example : SortedMeet.run ((3, 0), [1]) = none := by decide +kernel
example : SortedMeet.run ((0, 0), [0, 0, 0, 0]) = some [false, false, false] := by
  decide +kernel

-- Nonempty halves, collisions and all residues of the consecutive quarter cut.
example : (SortedMeet.run ((3, 1), [0, 1, 1, 1, 1])).isSome = true := by decide +kernel
example : (SortedMeet.run ((3, 1), [0, 1, 1, 1, 1, 1, 1, 1])).isSome = true := by
  decide +kernel
example : (SortedMeet.run ((3, 5), [0, 1, 1])).isSome = true := by decide +kernel
example : (SortedMeet.run ((3, 5), [7, 1, 0, 0])).isSome = true := by decide +kernel

-- Both branch directions are checked without assuming the packed words are witnesses.
example {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) :=
  SortedMeet.solve_none_iff as bs s
example {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (ops : List Bool)
    (hit : SortedMeet.solve ((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)) =
      some ops) := SortedMeet.solve_sound as bs s ops hit
example {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :=
  SortedMeet.original_correct p a tail

-- Actual certificates compose the generated arrays with the sorter/scan and decoder.
example := SortedMatch.scan_computable
example := SortedMatch.runCertificate.computes
example := SortedMeet.inverseCertificate.computes
example := SortedMeet.sourceCertificate.computes
example := SortedMeet.original_machine
