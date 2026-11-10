/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.FrontProgram
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-!
# Original-input instruction ledger for one-geometry box products

One geometry construction is charged before the tile loop. Each tile pays for its
actual retained values, every wanted occurrence, result copying and loop control.
Routing, shared encodings, reconstruction and input restoration remain explicit terms.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open scoped BigOperators

/-- Uniform sparse-batch charge for one original wanted-code occurrence. -/
@[expose] def batchUnit (L m t : ℕ) : ℕ :=
  258 * (L + 1) * (∑ d ∈ Finset.range (t + 1), alpha m d) + 34

/-- Actual retained table, sparse queries, result copying and outer control for one tile. -/
@[expose] def tileCharge {N : ℕ} (L m t : ℕ) (qs : List (Fin N × Fin N)) (j : ℕ) : ℕ :=
  328 * (boxes L m t).card +
    Nat.count (fun i => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i = j) qs.length *
      (batchUnit L m t + 7) + 65

/-- Actual frontend, one shared geometry, all tile calls, reconstruction and input restoration.
The final halt is charged separately. Every query occurrence contributes to its own tile. -/
@[expose] def timeBound {N : ℕ} (L m t : ℕ) (qs : List (Fin N × Fin N)) : ℕ :=
  frontTime L m N qs.length + (BoxTable.geometryTime L m t + 17) +
    ((∑ j ∈ Finset.range (numBands L m N ^ 2), tileCharge L m t qs j) + 2) +
    (9 * qs.length + 3) + (7 * QueriedProduct.inputEnd m N qs.length + 12)

/-- Every original occurrence is charged exactly once, even when coordinates repeat. -/
theorem sum_tileCharge {L m N : ℕ} (hm : m ≤ L) (t : ℕ)
    (qs : List (Fin N × Fin N)) :
    (∑ j ∈ Finset.range (numBands L m N ^ 2), tileCharge L m t qs j) =
      numBands L m N ^ 2 * (328 * (boxes L m t).card + 65) +
        qs.length * (batchUnit L m t + 7) := by
  have hkey (i : ℕ) (hi : i < qs.length) :
      (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i < numBands L m N ^ 2 :=
    Wanted.tileKey_lt hm _ (Wanted.inputPairs_lt qs i hi).1 (Wanted.inputPairs_lt qs i hi).2
  have hcount := CountingSort.sum_count_eq_count_lt
    (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length (numBands L m N ^ 2)
  rw [Nat.count_of_forall hkey] at hcount
  simp only [tileCharge, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, ← Finset.sum_mul, hcount]
  ring

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
