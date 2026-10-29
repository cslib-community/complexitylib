/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Padding
public import Complexity.Algorithms.ThreeSum.ChanHe.FromNumbers

/-!
# Disjoint memory layout for complete native Chan–He node construction

Three supplied signed input arrays precede `base`. The allocated block consists of three
count-prefixed heavy arrays (capacities `n₀,n₁,n₂`), the `4N` packed cells, a reusable residue
array of capacity `n₀+n₁+n₂`, and `M` histogram cells. Empty arrays still have a count cell.

## Main definitions

* `NodePacking.Layout`: concrete bases and a polynomial resource envelope.

## References

This memory layout is an original implementation choice.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Runtime sizes and the fresh allocation base for one complete node. -/
structure Layout where
  /-- The input arrays end no later than this address. -/
  base : ℕ
  /-- The three supplied input lengths. -/
  n : Fin 3 → ℕ
  /-- Common number of groups; the packed output has `4N` cells. -/
  N : ℕ
  /-- Positive modulus, supplied by the parent prime search. -/
  M : ℕ
  /-- Bound on the magnitudes of this node's inputs. -/
  U : ℕ

/-- Total input capacity, shared by the reusable residue workspace. -/
def Layout.total (L : Layout) : ℕ := L.n 0 + L.n 1 + L.n 2

/-- Count cell immediately preceding a compact heavy array. -/
def Layout.descriptor (L : Layout) (j : Fin 3) : ℕ :=
  L.base + j.val + if j = 0 then 0 else if j = 1 then L.n 0 else L.n 0 + L.n 1

/-- Compact heavy output data starts one cell after its count. -/
def Layout.heavy (L : Layout) (j : Fin 3) : ℕ := L.descriptor j + 1

/-- All three compact output capacities precede the packed array. -/
def Layout.packed (L : Layout) : ℕ := L.base + 3 + L.total

/-- A reusable residue array, after every permanent output. -/
def Layout.scratch (L : Layout) : ℕ := L.packed + 4 * L.N

/-- A reusable histogram, after the full residue capacity. -/
def Layout.hist (L : Layout) : ℕ := L.scratch + L.total

/-- One-past-end address of the complete allocated block. -/
def Layout.endpoint (L : Layout) : ℕ := L.hist + L.M

/-- The ordinary one-array tag, `3(2U+1)+1`. -/
def Layout.gap (L : Layout) : ℕ := 6 * L.U + 4

/-- Positive tag for the selected packed column. -/
def Layout.tag (L : Layout) (j : Fin 3) : ℕ :=
  if j = 0 then L.gap else if j = 1 then 3 * L.gap else 4 * L.gap

/-- Polynomial envelope for all addresses, signed values, encodings and histogram counters.
Its fixed constant also covers code labels and all setup constants. -/
def Layout.budget (L : Layout) : ℕ :=
  4096 * (L.base + L.total + L.M + L.N + L.U + 1) ^ 2

/-- Each input fits the reusable residue capacity. -/
theorem Layout.n_le_total (L : Layout) (j : Fin 3) : L.n j ≤ L.total := by
  fin_cases j <;> simp +decide [Layout.total] <;> omega

/-- All three compact arrays and their count cells are disjoint, with the packed array next. -/
theorem Layout.heavy_end_le_packed (L : Layout) (j : Fin 3) :
    L.heavy j + L.n j ≤ L.packed := by
  fin_cases j <;> simp +decide [Layout.heavy, Layout.descriptor, Layout.packed, Layout.total] <;>
    omega

/-- Every descriptor is inside its allocated output prefix. -/
theorem Layout.base_le_descriptor (L : Layout) (j : Fin 3) : L.base ≤ L.descriptor j := by
  dsimp only [Layout.descriptor]
  omega

/-- Every descriptor precedes the packed array, including for empty inputs. -/
theorem Layout.descriptor_lt_packed (L : Layout) (j : Fin 3) : L.descriptor j < L.packed := by
  have := L.heavy_end_le_packed j
  dsimp only [Layout.heavy] at this
  omega

/-- The allocated endpoint has a linear size formula. -/
theorem Layout.endpoint_eq (L : Layout) :
    L.endpoint = L.base + 3 + 2 * L.total + 4 * L.N + L.M := by
  dsimp only [Layout.endpoint, Layout.hist, Layout.scratch, Layout.packed]
  omega

/-- Descriptor/capacity blocks end where the next one begins. -/
theorem Layout.next_descriptor (L : Layout) :
    L.heavy 0 + L.n 0 = L.descriptor 1 ∧
      L.heavy 1 + L.n 1 = L.descriptor 2 ∧ L.heavy 2 + L.n 2 = L.packed := by
  norm_num [Layout.heavy, Layout.descriptor, Layout.packed, Layout.total]
  omega

/-- Every address and padding/tag value is covered by one polynomial envelope. -/
theorem Layout.bounds (L : Layout) :
    L.endpoint ≤ L.budget ∧ 120 * L.U + 80 ≤ L.budget ∧
      L.base + L.total + L.M + L.N + L.U + 16 ≤ L.budget := by
  let S := L.base + L.total + L.M + L.N + L.U + 1
  have hs : 1 ≤ S := by dsimp only [S]; omega
  have hsq : S ≤ S ^ 2 := by nlinarith
  have hb : L.base ≤ S := by dsimp only [S]; omega
  have hn : L.total ≤ S := by dsimp only [S]; omega
  have hm : L.M ≤ S := by dsimp only [S]; omega
  have hN : L.N ≤ S := by dsimp only [S]; omega
  have hU : L.U ≤ S := by dsimp only [S]; omega
  rw [Layout.endpoint_eq]
  change _ ≤ 4096 * S ^ 2 ∧ _ ≤ 4096 * S ^ 2 ∧ _ ≤ 4096 * S ^ 2
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The complete counting/placement call's budget is derived from the concrete node layout. -/
theorem Layout.count_budget_le (L : Layout) (j : Fin 3) (src t : ℕ)
    (hs : src ≤ L.base) (ht : t ≤ 4 * L.gap) :
    src + L.scratch + L.hist + L.heavy j + L.packed + L.n j * L.n j +
        2 * L.n j + L.M + 4 * L.N + 2 * t + 2 * L.U + 64 ≤ L.budget := by
  let S := L.base + L.total + L.M + L.N + L.U + 1
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hsq : S ≤ S ^ 2 := by nlinarith
  have hb : L.base ≤ S := by dsimp only [S]; omega
  have hn : L.total ≤ S := by dsimp only [S]; omega
  have hm : L.M ≤ S := by dsimp only [S]; omega
  have hN : L.N ≤ S := by dsimp only [S]; omega
  have hU : L.U ≤ S := by dsimp only [S]; omega
  have hj := L.n_le_total j
  have hjsq : L.n j * L.n j ≤ S ^ 2 := by nlinarith
  have ho := L.heavy_end_le_packed j
  dsimp only [Layout.gap] at ht
  dsimp only [Layout.hist, Layout.scratch, Layout.packed]
  change _ ≤ 4096 * S ^ 2
  dsimp only [Layout.packed] at ho
  nlinarith

/-- All three tags are positive, dominate the input magnitude, and fit the common tag bound. -/
theorem Layout.tag_bounds (L : Layout) (j : Fin 3) :
    L.U ≤ L.tag j ∧ L.tag j ≤ 4 * L.gap := by
  fin_cases j <;> simp +decide [Layout.tag, Layout.gap] <;> omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
