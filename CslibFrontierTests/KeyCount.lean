/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (streamed occurrence counter regression tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyCount
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyCount
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping

/-!
The real small-state counter handles empty input, one-sided runs, duplicate
occurrences, alternating sides and key changes. Unsorted repeated keys illustrate
why global key-class interpretation additionally needs the producer's sorting.
The general uniform resource theorem is applied with no supplied cost bounds.
-/

public section
open Turing.MultiTapeTM

example : KeyCount.run [] = 0 := by decide +kernel
example : KeyCount.run [(0, 0), (0, 2), (0, 4)] = 0 := by decide +kernel
example : KeyCount.run [(0, 1), (0, 3), (0, 5)] = 0 := by decide +kernel
example : KeyCount.run [(2, 0), (2, 0), (2, 1), (2, 1)] = 4 := by decide +kernel
example : KeyCount.run [(2, 0), (2, 1), (2, 0), (2, 1)] = 4 := by decide +kernel
example : KeyCount.run [(2, 0), (2, 1), (3, 0), (3, 1), (3, 1)] = 3 := by decide +kernel
example : KeyCount.run [(2, 0), (3, 0), (2, 1)] = 0 := by decide +kernel
example : KeyCount.run [(0, 0), (0, 1), (0, 3), (1, 0), (2, 1)] = 2 := by decide +kernel

example (rows : List SortedMatch.Record) :
    KeyCount.run rows = KeyJoin.count (KeyGrouping.run rows) := KeyCount.run_eq_count rows

example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO KeyCount.run (encList RadixPartition.recordEncoding) encNat
      (fun rows => (encList RadixPartition.recordEncoding rows).length +
        (rows.length + 1) * P (KeyCount.width rows))
      (fun rows => (encList RadixPartition.recordEncoding rows).length + P (KeyCount.width rows)) :=
  KeyCount.run_computable
