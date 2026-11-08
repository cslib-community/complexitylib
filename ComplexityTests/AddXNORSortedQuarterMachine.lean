/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (integrated source-quarter execution regression tests)

public import Complexity.Cryptanalysis.AddXNORSourceQuarter
import all Complexity.Cryptanalysis.AddXNORSourceQuarter
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORSortedRecords
import all Complexity.Cryptanalysis.AddXNORDecision
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration

/-! These clients execute generation and sorting from original operands, rather
than supplying an already materialized semantic record list. -/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- An original source input with a colliding first quarter and nonempty other quarters. -/
def sourceFixture : Source.Input := ((3, 1), [0, 1, 1, 2, 3, 4, 5, 6, 7])

example : SortedQuarterMachine.indices 3 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide +kernel
example : SortedQuarterMachine.run ((3, 0), [1, 1]) =
    [(0, 3), (2, 0), (7, 1), (7, 2)] := by decide +kernel
example : SortedQuarterMachine.run ((3, 2), [1]) = [(3, 0), (4, 1)] := by decide +kernel
example : backward [(false, 1#3)] 2#3 = 1#3 := by decide +kernel
example : SortedQuarterMachine.run ((0, 0), [0, 0]) =
    [(0, 0), (0, 1), (0, 2), (0, 3)] := by decide +kernel
example : SortedQuarterMachine.run ((3, 5), []) = [(5, 0)] := by decide +kernel

-- The seed, quarter length, projected operands and capped depth are computed from one input.
example : SourceQuarter.prepare sourceFixture = ((1, 0), [1, 1]) := by decide +kernel
example : SourceQuarter.run sourceFixture =
    [(0, 0), (0, 3), (1, 1), (1, 2)] := by decide +kernel
example : SourceQuarter.run ((3, 8), [0, 1, 1, 2, 3, 4, 5, 6, 7]) =
    [(0, 3), (2, 0), (3, 1), (3, 2)] := by decide +kernel
example : SourceQuarter.run ((3, 8), [2, 1, 1, 2, 3, 4, 5, 6, 7]) =
    [(0, 0), (1, 1), (1, 2), (2, 3)] := by decide +kernel
example : SourceQuarter.run ((3, 1), [2, 1, 2, 3]) = [(0, 0)] := by decide +kernel
example : SourceQuarter.run ((0, 0), []) = [(0, 0)] := by decide +kernel
example : SourceQuarter.run ((0, 0), [0, 0, 0, 0, 0, 0, 0, 0, 0]) =
    [(0, 0), (0, 1), (0, 2), (0, 3)] := by decide +kernel

example (k : ℕ) := SortedQuarterMachine.indices_eq_range k
example (k : ℕ) := SortedQuarterMachine.indices_wire k
example {m : ℕ} (as : List (BitVec m)) (s : BitVec m) := SortedQuarterMachine.correct as s
example (input : Source.Input) := SourceQuarter.correct input
example (input : Source.Input) := SourceQuarter.prepare_length input
example {m p : ℕ} (hp : p ≤ m) (a : BitVec m) (tail : List (BitVec m))
    (hk : p ≤ tail.length / 4) := SourceQuarter.original_correct hp a tail hk
example {m p : ℕ} (hp : p ≤ m) (a : BitVec m) (tail : List (BitVec m)) :=
  SourceQuarter.original_input_length hp a tail

-- A uniform machine/resource polynomial precedes all runtime source widths and operands.
example : ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
    ComputableInO SourceQuarter.run Source.encoding (encList RadixPartition.recordEncoding)
      (fun input => (2 ^ (input.2.tail.length / 4) + 1) * Q ((Source.encoding input).length + 1))
      (fun input => (2 ^ (input.2.tail.length / 4) + 1) * Q ((Source.encoding input).length + 1)) :=
  SourceQuarter.run_computable

example : SourceQuarter.run sourceFixture ≠
    [(0, 0), (1, 1), (1, 2), (0, 3)] := by decide +kernel
