/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Program

/-!
# Concrete input and scratch layout for native pruned queries

## Main definitions

* `PrunedQuery.input`: two ordinary headers, two encoded leaf arrays and an explicit query list.
* `PrunedQuery.outputBase`, `PrunedQuery.scratchBase`, `PrunedQuery.memoryEnd`: the output and
  the complete explicit-stack workspace.

The standard `State.init` length cell precedes this list. Query codes and the two source arrays
are read-only. The timestamp region is initially zero because it lies beyond the supplied input.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Flat initialized input: depth, query count, both signed arrays, then explicit query codes. -/
def input (L : ℕ) (a b : Fin (10 ^ L) → ℤ) (qs : List (Fin (10 ^ L))) : List ℕ :=
  [L, qs.length] ++ List.ofFn (fun i => encode (a i)) ++
    List.ofFn (fun i => encode (b i)) ++ qs.map Fin.val

/-- Start of the returned values, in the original query-list order. -/
def outputBase (L Q : ℕ) : ℕ := 3 + 2 * 10 ^ L + Q

/-- First stack-frame cell, immediately after the returned values. -/
def scratchBase (L Q : ℕ) : ℕ := outputBase L Q + Q

/-- Query lists occupy one `10^L` block per possible stack depth. -/
def listsBase (L Q : ℕ) : ℕ := scratchBase L Q + 4 * (L + 1)

/-- Values occupy a separate `10^L` block per depth. -/
def valuesBase (L Q : ℕ) : ℕ := listsBase L Q + (L + 1) * 10 ^ L

/-- One shared timestamp directory suffices for all child-set constructions. -/
def stampsBase (L Q : ℕ) : ℕ := valuesBase L Q + (L + 1) * 10 ^ L

/-- One-past-end address of the complete output and scratch footprint. -/
def memoryEnd (L Q : ℕ) : ℕ := stampsBase L Q + 10 ^ L

/-- A scalar budget for the concrete addresses, counters, powers and timestamp generations. -/
def addressBound (L Q : ℕ) : ℕ := 256 * (L + 1) * 10 ^ L + 32 * Q + 512

/-- The initialized payload includes no precomputed child requests or recursion certificate. -/
theorem length_input (L : ℕ) (a b : Fin (10 ^ L) → ℤ) (qs : List (Fin (10 ^ L))) :
    (input L a b qs).length = 2 + 2 * 10 ^ L + qs.length := by
  simp only [input, List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
    List.length_map]
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
