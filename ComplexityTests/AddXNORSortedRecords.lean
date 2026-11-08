/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests for source sorting components)

import all Complexity.Cryptanalysis.AddXNORSortedRecords
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all Complexity.Computability.GenericRAM.SparseMemory.StreamingCompact
import all Complexity.Computability.GenericRAM.SparseMemory.Compact
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORNativeClassRetain
import all Complexity.Cryptanalysis.AddXNORNativeForwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeRetain
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
public import Complexity.Computability.GenericRAM.SparseMemory.Basic

/-! Uniform source sorting clients: arbitrary widths, exact stable collisions,
zero/empty records, physical payload width and genuine non-self-inverse addition. -/

public section

open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

example : RadixSort.sort (3, [(5, 0), (1, 7), (5, 2), (0, 0), (1, 3)]) =
    [(0, 0), (1, 7), (1, 3), (5, 0), (5, 2)] := by decide +kernel

example : RadixSort.sort (0, [(0, 7), (0, 0)]) = [(0, 7), (0, 0)] := rfl
example : RadixSort.sort (12, []) = [] := by decide +kernel

-- A zero-width input with a nonzero key is preserved, but cannot meet the sorting precondition.
example : ¬ (∀ row ∈ ([(1, 0), (0, 0)] : List (ℕ × ℕ)), row.1 < 2 ^ 0) := by decide +kernel

example (input : ℕ × List (ℕ × ℕ))
    (fits : ∀ row ∈ input.2, row.1 < 2 ^ input.1) :
    (RadixSort.sort input).Perm input.2 ∧
      (RadixSort.sort input).Pairwise (fun a b => a.1 ≤ b.1) := RadixSort.correct input fits

-- A fixed machine precedes every runtime width/list, with explicit time and peak-space budgets.
example : ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
    ComputableInO RadixSort.sort RadixPartition.inputEncoding
      (encList RadixPartition.recordEncoding)
      (fun input => (input.1 + 1) * ((RadixPartition.inputEncoding input).length +
        (input.2.length + 1) *
          Q (streamFilterWidth encUnary RadixPartition.recordEncoding input)))
      (fun input => (RadixPartition.inputEncoding input).length +
        Q (streamFilterWidth encUnary RadixPartition.recordEncoding input)) := RadixSort.computable
example := RadixSort.wire_bounds
example := Cslib.GenericRAM.SparseMemory.compact_streaming encNat encNat

example {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) :=
  SortedRecords.retainedClass_correct hp as bs s g
example {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s : BitVec m) :=
  SortedRecords.projectedQuarter_wires p as s
example {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) :=
  SortedRecords.retainedClass_wires hp as bs s g

-- Addition by one modulo eight is not its own inverse. Both low-bit buckets have collisions.
example : SortedRecords.projectedQuarter 1 [1#3, 1#3] 0#3 =
    [(0, 0), (1, 1), (1, 2), (0, 3)] := by decide +kernel
example : RadixSort.sort (3, SortedRecords.projectedQuarter 3 [1#3, 1#3] 0#3) =
    [(0, 3), (2, 0), (7, 1), (7, 2)] := by decide +kernel
example : eval [(false, 1#3), (false, 1#3)] 0#3 = 2#3 := by decide +kernel
example : backward [(false, 1#3), (false, 1#3)] 0#3 = 6#3 := by decide +kernel

-- A full class retains the two distinct witnesses of each colliding state.
example : RadixSort.sort (3, SortedRecords.retainedClass [1#3] [1#3] 0#3 1#1) =
    [(7, 1), (7, 2)] := by decide +kernel
example : SortedRecords.packedEntry 1 ⟨0, 0, 1⟩ = (0, 2) := rfl
example : (2 % 2 ^ 1, 2 / 2 ^ 1) = (0, 1) := by decide +kernel
example (u v : ℕ) (hu : u < 2 ^ 9) := SortedRecords.unpack_payload (v := v) hu

-- Actual normalization preserves order, removes a nonzero default and keeps index zero.
/-- Nonzero-default fixture with one surviving zero-valued binding. -/
def store : Cslib.GenericRAM.SparseMemory ℕ ℕ :=
  AList.insert 2 7 (AList.insert 1 0 (AList.insert 0 7 ∅))

example : Cslib.GenericRAM.SparseMemory.entries
    (Cslib.GenericRAM.SparseMemory.compact 7 store) = [(1, 0)] := by decide +kernel

-- Source cut convention: every residual-quarter record/index width remains charged.
example : Source.quarters ([1, 2, 3, 4, 5, 6, 7] : List ℕ) =
    (([1], [2]), ([3], [4, 5, 6, 7])) := by decide +kernel
