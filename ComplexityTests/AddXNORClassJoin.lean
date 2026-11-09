/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (original-input quarter-query class join regression tests)

public import Complexity.Cryptanalysis.AddXNORClassJoin
import all Complexity.Cryptanalysis.AddXNORClassJoin
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORDecision
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
The client executes actual original input, quarter projections, inverse queries,
tagging/sorting/grouping, occurrence counts, full-width state production and the
fixed all-class counter loop. Collision and non-self-inverse addition cases are
checked by kernel reduction, independently of the uniform machine certificates.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

example : KeyJoin.count [] = 0 := by decide +kernel
example : KeyJoin.pairs [(2, 0), (2, 0), (2, 1), (2, 1)] =
    [(0, 0), (0, 0), (0, 0), (0, 0)] := by decide +kernel
example : KeyJoin.count [[(2, 0), (2, 0), (2, 1), (2, 1)]] = 4 := by decide +kernel
example : KeyJoin.count [[(2, 0), (2, 2)], [(3, 1), (3, 3)]] = 0 := by decide +kernel

/-- Full-width addition by one at width three is not its own inverse. -/
def classJoinFixture : Source.Input := ((3, 1), [0, 1, 1, 2, 3, 4, 5, 6, 7])

example : ClassJoin.table classJoinFixture = [8, 8] := by decide +kernel
example : ClassJoin.fullStates (classJoinFixture, 0) =
    [(0, (0, 1)), (2, (0, 2)), (6, (3, 1)), (0, (3, 2)),
      (4, (1, 0)), (6, (1, 3)), (4, (2, 0)), (6, (2, 3))] := by decide +kernel
example : ClassJoin.table ((3, 2), [0, 0, 0, 0, 0, 0, 0, 0, 0]) =
    [8, 0, 0, 8] := by decide +kernel
example : ClassJoin.table ((0, 0), []) = [1] := by decide +kernel
example : ClassJoin.fullStates (((0, 0), []), 0) = [(0, (0, 0))] := by decide +kernel
example : ClassJoin.table ((0, 8), [0, 0, 0, 0, 0, 0, 0, 0, 0]) = [16] := by decide +kernel
example : ClassJoin.table ((3, 8), [2, 1, 2, 3]) = [1] := by decide +kernel

example (input : ClassJoin.Input) := ClassJoin.count_eq_length input
example (input : ClassJoin.Input) := ClassJoin.count_le_quarters input
example (input : ClassJoin.SourceInput) := ClassJoin.fullStates_length input
example (input : Source.Input) := ClassJoin.table_eq input
example (input : Source.Input) := ClassJoin.table_length input
example (input : Source.Input) := ClassJoin.table_wire input

example {p : ℕ} (as bs : List (BitVec p)) (s g : BitVec p) (uv : ℕ × ℕ) :=
  ClassJoin.mem_witnesses as bs s g uv
example {p : ℕ} (as bs : List (BitVec p)) (s g : BitVec p) :=
  ClassJoin.count_zero_iff as bs s g
example {m p : ℕ} (hm : p ≤ m) (s : BitVec m) (tail : List (BitVec m))
    (hk : p ≤ tail.length / 4) (g : BitVec p) (uv : ℕ × ℕ) :=
  ClassJoin.original_witnesses hm s tail hk g uv
example {m p : ℕ} (hm : p ≤ m) (s : BitVec m) (tail : List (BitVec m))
    (hk : p ≤ tail.length / 4) (g : BitVec p) (state u v : ℕ) :=
  ClassJoin.mem_fullStates hm s tail hk g state u v
example {m p : ℕ} (hm : p ≤ m) (s : BitVec m) (tail : List (BitVec m))
    (hk : p ≤ tail.length / 4) (g : BitVec p) :=
  ClassJoin.original_table_zero_iff hm s tail hk g

-- These are actual machines composed from preparation/generation/inverse execution and
-- the one-pass writer. Their profiles retain all generic consumer and loop-copying overhead.
example := ClassJoin.sourceCertificate.computes
example := ClassJoin.fullStatesCertificate.computes
example := ClassJoin.tableCertificate.computes
example := ClassJoin.fullRecords_computable

example (input : ClassJoin.Input) := ClassJoin.count_streaming input
example := ClassJoin.sortedCertificate.computes
