/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (streamed equal-key grouping and original-quarter regression tests)

public import Complexity.Cryptanalysis.AddXNORGroupedQuarter
import all Complexity.Cryptanalysis.AddXNORGroupedQuarter
import all Complexity.Cryptanalysis.AddXNORSourceQuarter
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSortedRecords
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORDecision
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
The client starts with original operands and executes quarter generation/sorting
and nested-frame group output. Large collisions, duplicate payloads, empty input
and zero-width controls do not become growing groups in the grouping machine state.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

example : KeyGrouping.run [] = [] := by decide +kernel
example : KeyGrouping.run [(1, 4), (1, 4), (1, 7)] =
    [[(1, 4), (1, 4), (1, 7)]] := by decide +kernel
example : KeyGrouping.run [(0, 1), (1, 2), (0, 3)] =
    [[(0, 1)], [(1, 2)], [(0, 3)]] := by decide +kernel
example : KeyGrouping.run (List.replicate 32 (0, 0)) = [List.replicate 32 (0, 0)] := by
  decide +kernel

/-- A real original-input first quarter with two colliding keys and nonempty other quarters. -/
def groupedSourceFixture : Source.Input := ((3, 1), [0, 1, 1, 2, 3, 4, 5, 6, 7])

example : GroupedQuarter.run groupedSourceFixture =
    [[(0, 0), (0, 3)], [(1, 1), (1, 2)]] := by decide +kernel
example : GroupedQuarter.run ((0, 0), [0, 0, 0, 0, 0, 0, 0, 0, 0]) =
    [[(0, 0), (0, 1), (0, 2), (0, 3)]] := by decide +kernel
example : GroupedQuarter.run ((3, 8), [0, 1, 1, 2, 3, 4, 5, 6, 7]) =
    [[(0, 3)], [(2, 0)], [(3, 1), (3, 2)]] := by decide +kernel
example : GroupedQuarter.run ((3, 1), [2, 1, 2, 3]) = [[(0, 0)]] := by decide +kernel
example : GroupedQuarter.run ((0, 0), []) = [[(0, 0)]] := by decide +kernel

-- The emitted bytes are the real nested encoding, not an assumed grouping decoder.
example (rows : List (ℕ × ℕ)) :
    KeyGrouping.outputEncoding (KeyGrouping.run rows) =
      streamEmit KeyGrouping.next KeyGrouping.emit none rows ++
        KeyGrouping.close (streamState none KeyGrouping.next rows rows.length) :=
  KeyGrouping.encoded_run rows
example (rows : List (ℕ × ℕ)) := KeyGrouping.flatten_run rows
example (rows : List (ℕ × ℕ)) := KeyGrouping.wire_length rows
example (rows : List (ℕ × ℕ)) := KeyGrouping.wire_le rows
example (input : Source.Input) := GroupedQuarter.flatten_run input
example (input : Source.Input) (group : List (ℕ × ℕ)) (hg : group ∈ GroupedQuarter.run input) :=
  GroupedQuarter.groups_correct input group hg
example {m p : ℕ} (hm : p ≤ m) (a : BitVec m) (tail : List (BitVec m))
    (hk : p ≤ tail.length / 4) := GroupedQuarter.original_correct hm a tail hk

-- One machine/polynomial precedes all runtime quarter sizes and source widths.
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO KeyGrouping.run (encList RadixPartition.recordEncoding) KeyGrouping.outputEncoding
      (fun rows => (encList RadixPartition.recordEncoding rows).length +
        (rows.length + 1) * P (streamRecordLength RadixPartition.recordEncoding rows + 1))
      (fun rows => (encList RadixPartition.recordEncoding rows).length +
        P (streamRecordLength RadixPartition.recordEncoding rows + 1)) := KeyGrouping.run_computable
example : ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
    ComputableInO GroupedQuarter.run Source.encoding KeyGrouping.outputEncoding
      (fun input => (2 ^ (input.2.tail.length / 4) + 1) * Q ((Source.encoding input).length + 1))
      (fun input => (2 ^ (input.2.tail.length / 4) + 1) * Q ((Source.encoding input).length + 1)) :=
  GroupedQuarter.run_computable
