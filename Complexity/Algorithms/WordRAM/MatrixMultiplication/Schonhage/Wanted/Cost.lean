/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Memory
import Mathlib.Tactic.Linarith

/-!
# Charged bound for native wanted-query grouping

## Main definitions

* `Wanted.timeBound`: sum of actual parameter/table, zero/count, prefix and scatter charges.

## Main results

* `Wanted.timeBound_add_one_le`: a bound polynomial in depth times query, tile and mask counts.

These are original instruction bounds for the native implementation. Actual executions are
proved separately; no execution or complexity certificate is an input to the program.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Prefix instruction budget, before the final flat halt. All initialization and loops count. -/
def timeBound (L m N Q : ℕ) : ℕ :=
  16 * L + (12 * L + 33) * 2 ^ L + 15 * numBands L m N ^ 2 + (15 * L + 57) * Q + 100

/-- Including halt, routing is polynomial in depth times the original query, tile and
subset-table sizes. In particular it does not scan `10^L` cells per query or tile. -/
theorem timeBound_add_one_le (L m N Q : ℕ) :
    timeBound L m N Q + 1 ≤
      128 * (L + 1) * (Q + numBands L m N ^ 2 + 2 ^ L + 1) := by
  unfold timeBound
  nlinarith only [Nat.zero_le (L * Q), Nat.zero_le (L * numBands L m N ^ 2),
    Nat.zero_le (L * 2 ^ L), Nat.zero_le Q, Nat.zero_le (numBands L m N ^ 2),
    Nat.zero_le (2 ^ L), Nat.zero_le L]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
