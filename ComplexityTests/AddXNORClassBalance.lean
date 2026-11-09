/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (generated forward/backward class balance regression tests)

public import Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORClassJoin
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORDecision
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyCount
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
Real quarter generation/inverse queries and counted orientation are executed by
kernel reduction. Colliding full states retain distinct packed words. Fixtures
exercise strict backward retention, forward retention, empty classes and residue.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- Forward zero operands concentrate two classes; the backward half uses real additions. -/
def backwardSmallerFixture : Source.Input := ((3, 2), [0, 0, 0, 0, 0, 1, 2, 3, 4])

example : ClassBalance.table (Source.prepare backwardSmallerFixture) =
    [(8, 6), (0, 4), (0, 2), (8, 4)] := by decide +kernel
example : ClassBalance.retainRight (Source.prepare backwardSmallerFixture) 0 = true := by
  decide +kernel
example : ClassBalance.retainRight (Source.prepare backwardSmallerFixture) 1 = false := by
  decide +kernel
example : ClassBalance.balance (Source.prepare backwardSmallerFixture) = 6 := by decide +kernel
example : (ClassBalance.retain (Source.prepare backwardSmallerFixture) 0).length = 6 := by
  decide +kernel
example : (ClassBalance.retain (Source.prepare backwardSmallerFixture) 1).length = 0 := by
  decide +kernel

/-- The backward class can be empty despite a nonempty forward class. -/
def backwardEmptyFixture : Source.Input := ((3, 2), [0, 1, 2, 3, 4, 0, 0, 0, 0])

example : ClassBalance.retainRight (Source.prepare backwardEmptyFixture) 1 = true := by
  decide +kernel
example : ClassBalance.retain (Source.prepare backwardEmptyFixture) 1 = [] := by decide +kernel
example : ClassBalance.table (Source.prepare ((3, 2), [0, 0, 0, 0, 0, 0, 0, 0, 2])) =
    [(8, 0), (0, 8), (0, 8), (8, 0)] := by decide +kernel
example : ClassBalance.table (Source.prepare ((0, 8), [0, 0, 0, 0, 0, 0, 0, 0, 0])) =
    [(16, 16)] := by decide +kernel
example : ClassBalance.table (Source.prepare ((3, 1), [0, 1, 2, 3, 4, 5])) =
    [(2, 4), (2, 4)] := by decide +kernel

-- No duplicate quarter pairs are introduced by collisions in a generated class.
example (input : ClassJoin.Input) := ClassJoin.witnesses_nodup input
example (input : ClassBalance.Input) (g : ℕ) := ClassBalance.retained_length input g
example (input : ClassBalance.Input) (g j : ℕ) (hg : g < 2 ^ ClassBalance.depth input) :=
  ClassBalance.retained_prefix input g j hg
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (right : Bool) (g : BitVec p) (r : ℕ × ℕ) :=
  ClassBalance.original_records hp as bs cs ds s t right g r
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m)
    (right : Bool) (g : BitVec p) := ClassBalance.count_eq_counter hp as bs cs ds s right g
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :=
  ClassBalance.balance_eq_counter hp as bs cs ds s
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m)
    (g : BitVec p) (j : ℕ) := ClassBalance.retained_prefix_wire hp as bs cs ds s g j
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m)
    (n : ℕ) (hn : n ≤ 2 ^ p) := ClassBalance.table_prefix_wire hp as bs cs ds s n hn

example := ClassBalance.countCertificate.computes
example := ClassBalance.recordsCertificate.computes
example := ClassBalance.retainCertificate.computes
example := ClassBalance.tableCertificate.computes
example := ClassBalance.balanceCertificate.computes

-- The actual new counter consumes generated sorted quarter rows in both orientations.
-- These are not precomputed class sizes supplied to the machine.
example : (List.range 4).map (fun g =>
    let input := Source.prepare backwardSmallerFixture
    (KeyCount.run (ClassJoin.sortedRecords (ClassBalance.queryInput input false g)),
      KeyCount.run (ClassJoin.sortedRecords (ClassBalance.queryInput input true g)))) =
    [(8, 6), (0, 4), (0, 2), (8, 4)] := by decide +kernel

example (input : ClassBalance.Input) (right : Bool) (g : ℕ) :
    KeyCount.run (ClassJoin.sortedRecords (ClassBalance.queryInput input right g)) =
      ClassBalance.count input right g :=
  (ClassJoin.count_streaming _).symm
