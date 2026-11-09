/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (original-input class retention and reuse regression tests)

public import CslibFrontier.Cryptanalysis.AddXNORClassStreaming
import all CslibFrontier.Cryptanalysis.AddXNORClassStreaming
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORDecision
import all CslibFrontier.Cryptanalysis.AddXNORChain
import all CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
Actual passes compute both occurrence counts, choose either retaining orientation,
sort one class, stream the opposite packed words, release between classes and
read back original-order operators. These are not supplied semantic list fixtures.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- Two colliding forward records and one inverse occurrence force inverse retention. -/
def inverseClassFixture : ClassStreaming.Input := (((3, 0), ([1, 1], [1])), (1, 1))

/-- One forward occurrence and two inverse occurrences force forward retention. -/
def forwardClassFixture : ClassStreaming.Input := (((3, 0), ([1], [1, 1])), (1, 1))

example : ClassStreaming.count inverseClassFixture false = 2 := by decide +kernel
example : ClassStreaming.count inverseClassFixture true = 1 := by decide +kernel
example : ClassStreaming.retainRight inverseClassFixture = true := by decide +kernel
example : ClassStreaming.retain inverseClassFixture true = [(7, 0)] := by decide +kernel
example : ClassStreaming.search inverseClassFixture = some (1, 0) := by decide +kernel
example : ClassStreaming.count forwardClassFixture false = 1 := by decide +kernel
example : ClassStreaming.count forwardClassFixture true = 2 := by decide +kernel
example : ClassStreaming.retainRight forwardClassFixture = false := by decide +kernel
example : ClassStreaming.retain forwardClassFixture false = [(1, 0)] := by decide +kernel
example : ClassStreaming.search forwardClassFixture = some (0, 2) := by decide +kernel

-- Every occurrence is counted, including equal full states and leading zero packed operators.
example : ClassStreaming.retain inverseClassFixture false = [(7, 2), (7, 1)] := by
  decide +kernel
example : ClassStreaming.search (((3, 0), ([1, 1], [1])), (1, 2)) = none := by decide +kernel
example : ClassStreaming.solve (((3, 0), ([1, 1], [1])), 1) =
    some [true, false, false] := by decide +kernel
example : ClassStreaming.solve (((3, 0), ([1], [1, 1])), 1) =
    some [true, false, false] := by decide +kernel
example : (ClassStreaming.search forwardClassFixture).map
    (SortedMeet.decodeWitness forwardClassFixture.1) = some [false, true, false] := by
  decide +kernel

-- The count-only maximum prepass and original-source readback are executed together.
example : ClassStreaming.run ((3, 1), [0, 1, 1, 1, 1]) =
    (2, some [true, true, true, true]) := by decide +kernel
example : ClassStreaming.run ((3, 0), [7, 1]) = (1, some [false]) := by decide +kernel
example : ClassStreaming.run ((3, 0), [0, 1, 1]) = (1, some [true, true]) := by
  decide +kernel
example : ClassStreaming.run ((3, 0), [0, 1]) = (1, none) := by decide +kernel
example : ClassStreaming.run ((3, 0), [0]) = (1, some []) := by decide +kernel
example : ClassStreaming.run ((3, 0), [1]) = (1, none) := by decide +kernel
example : ClassStreaming.run ((0, 0), [0, 0, 0, 0]) =
    (1, some [false, false, false]) := by decide +kernel
example : (ClassStreaming.run ((3, 1), [0, 1, 1, 1, 1, 1, 1, 1])).2.isSome = true := by
  decide +kernel

example (input : ClassStreaming.Input) (right : Bool) := ClassStreaming.count_eq input right
example (input : ClassStreaming.Input) := ClassStreaming.retained_length input
example (input : ClassStreaming.Input) (j : ℕ)
    (hj : j ≤ ClassStreaming.limit input (ClassStreaming.retainRight input)) :=
  ClassStreaming.retained_prefix_length input j hj
example (input : SortedMeet.Input × ℕ) := ClassStreaming.balance_eq input
example (input : SortedMeet.Input × ℕ) (g : ℕ) (hg : g < 2 ^ input.2) (j : ℕ)
    (hj : j ≤ ClassStreaming.limit (input.1, (input.2, g))
      (ClassStreaming.retainRight (input.1, (input.2, g)))) :=
  ClassStreaming.global_retained_prefix input g hg j hj
example {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p g j : ℕ)
    (hj : j ≤ ClassStreaming.limit
      ((((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g)))
      (ClassStreaming.retainRight
        ((((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g))))) :=
  ClassStreaming.retaining_prefix_wire as bs s p g j hj
example {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :=
  ClassStreaming.original_correct p a tail
example := ClassStreaming.countCertificate.computes
example := ClassStreaming.retainCertificate.computes
example := ClassStreaming.probeCertificate.computes
example := ClassStreaming.allCertificate.computes
example := ClassStreaming.balanceCertificate.computes
example := ClassStreaming.sourceCertificate.computes
example := ClassStreaming.original_machine
