/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (integrated batched source-class access regression tests)

public import Complexity.Cryptanalysis.AddXNORBatchedAccess
import all Complexity.Cryptanalysis.AddXNORBatchedAccess
import all Complexity.Cryptanalysis.AddXNORClassStreaming
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORDecision
import all Complexity.Cryptanalysis.AddXNORChain
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
These clients execute actual full/partial sorted batches, release/reuse, collision
payloads, both computed retaining orientations, structural insertion and the
complete original-input balance/search/readback route. Record-work examples do
not assert a bit-time bound for copying or class generation.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- Two retained occurrences with one colliding full state. -/
def retainedBatchFixture : BatchedAccess.Parameter := (3, (false, [(2, 4), (2, 8)]))

example : BatchedAccess.Valid 3 ((2, [(2, 6), (1, 7)]), none) := by
  simp [BatchedAccess.Valid]
example : ¬ BatchedAccess.Valid 2 ((2, [(2, 6), (1, 7)]), none) := by
  simp [BatchedAccess.Valid]

example : BatchedAccess.feed retainedBatchFixture 3 ((0, []), none) (1, 7) =
    ((1, [(1, 7)]), none) := by decide +kernel
example : BatchedAccess.feed retainedBatchFixture 3 ((2, [(2, 6), (1, 7)]), none) (2, 5) =
    ((0, []), some (8, 5)) := by decide +kernel
example : BatchedAccess.feed retainedBatchFixture 3 ((0, []), some (8, 5)) (2, 9) =
    ((0, []), some (8, 5)) := by decide +kernel

-- A missed full batch is cleared; the next hit is found only by final partial-batch flushing.
example : ([(0, 1), (1, 2), (3, 3)].foldl
    (BatchedAccess.feed retainedBatchFixture 3) ((0, []), none)) = ((0, []), none) := by
  decide +kernel
example : BatchedAccess.finish retainedBatchFixture
    ([(0, 1), (1, 2), (3, 3), (2, 9)].foldl
      (BatchedAccess.feed retainedBatchFixture 3) ((0, []), none)) = some (8, 9) := by
  decide +kernel
example : BatchedAccess.matchBatch (3, (true, [(2, 8)])) [(2, 9)] = some (9, 8) := by
  decide +kernel
example : BatchedAccess.finish (0, (false, []))
    ([(0, 0), (0, 1)].foldl (BatchedAccess.feed (0, (false, [])) 1) ((0, []), none)) = none := by
  decide +kernel

-- Counts and original operands determine each side and capacity, rather than supplied lists.
example : BatchedAccess.search (((3, 0), ([1, 1], [1])), (1, 1)) = some (1, 0) := by
  decide +kernel
example : BatchedAccess.search (((3, 0), ([1], [1, 1])), (1, 1)) = some (0, 2) := by
  decide +kernel
example : BatchedAccess.search (((3, 0), ([1, 1], [1])), (1, 2)) = none := by decide +kernel
example : BatchedAccess.run ((3, 1), [0, 1, 1, 1, 1]) =
    (2, some [true, true, true, true]) := by decide +kernel
example : BatchedAccess.run ((3, 0), [7, 1]) = (1, some [false]) := by decide +kernel
example : BatchedAccess.run ((3, 0), [0, 1]) = (1, none) := by decide +kernel
example : BatchedAccess.run ((3, 0), [0, 1, 1]) = (1, some [true, true]) := by decide +kernel
example : BatchedAccess.run ((3, 0), [0]) = (1, some []) := by decide +kernel
example : BatchedAccess.run ((3, 0), [1]) = (1, none) := by decide +kernel
example : BatchedAccess.run ((0, 0), [0, 0, 0, 0]) =
    (1, some [false, false, true]) := by decide +kernel
example : (BatchedAccess.run ((3, 1), [0, 1, 1, 1, 1, 1, 1, 1])).2.isSome = true := by
  decide +kernel

example (input : ClassStreaming.Input) (n : ℕ) := BatchedAccess.source_buffer_bound input n
example (input : ClassStreaming.Input) (rows : List (ℕ × ℕ)) :=
  BatchedAccess.source_recordWork input rows
example (parameter : BatchedAccess.Parameter) (capacity : ℕ) (rows : List (ℕ × ℕ))
    (hc : 0 < capacity) (hk : let (_, (_, kept)) := parameter; kept.length ≤ capacity) :=
  BatchedAccess.total_recordWork parameter capacity rows hc hk
example {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :=
  BatchedAccess.original_correct p a tail
example := BatchedAccess.feedCertificate.computes
example := BatchedAccess.retainCertificate.computes
example := BatchedAccess.probeCertificate.computes
example := BatchedAccess.allCertificate.computes
example := BatchedAccess.sourceCertificate.computes
example := BatchedAccess.original_machine
