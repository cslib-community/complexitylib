/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.EmptyChild

/-!
# Frames for the recursive controller proof

## Main results

* `PrunedQuery.nodeWrites_child_subset`: a recursive child's writes stay in its parent's frame.
* `PrunedQuery.notMem_nodeWrites_list`: a node's request list remains read-only.
* `PrunedQuery.notMem_nodeWrites_ancestor_values`: a child preserves its parent's accumulators.

The footprints are the concrete intervals used by the native program. These facts impose no
execution or fit hypotheses; they provide the spatial part of the node induction.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Normalize every row interval to its fixed workspace endpoint. -/
theorem mem_nodeWrites_iff {L f d c : ℕ} (hd : d ≤ L) : c ∈ nodeWrites L f d ↔
    (((f + 4 * d ≤ c ∧ c < f + 4 * (L + 1)) ∨
      (f + 4 * (L + 1) + (d + 1) * 10 ^ L ≤ c ∧
        c < f + 4 * (L + 1) + (L + 1) * 10 ^ L)) ∨
      (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L ≤ c ∧
        c < f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L)) ∨
      (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L ≤ c ∧
        c < f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + 10 ^ L) := by
  have hf : f + 4 * d + 4 * (L + 1 - d) = f + 4 * (L + 1) := by omega
  have hl : f + 4 * (L + 1) + (d + 1) * 10 ^ L + (L - d) * 10 ^ L =
      f + 4 * (L + 1) + (L + 1) * 10 ^ L := by
    calc
      _ = f + 4 * (L + 1) + (d + 1 + (L - d)) * 10 ^ L := by ring
      _ = _ := by rw [show d + 1 + (L - d) = L + 1 by omega]
  have hv : f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L +
      (L + 1 - d) * 10 ^ L = f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L := by
    calc
      _ = f + 4 * (L + 1) + ((L + 1) + (d + (L + 1 - d))) * 10 ^ L := by ring
      _ = _ := by rw [show d + (L + 1 - d) = L + 1 by omega]; ring
  simp only [nodeWrites, Finset.mem_union, Block.mem_footprint, Block.Owns, hf, hl, hv]

/-- The recursive child's full writable frame is contained in the parent's frame. -/
theorem nodeWrites_child_subset {L f d : ℕ} (hd : d < L) :
    nodeWrites L f (d + 1) ⊆ nodeWrites L f d := by
  intro c hc
  rw [mem_nodeWrites_iff (by omega : d + 1 ≤ L)] at hc
  rw [mem_nodeWrites_iff hd.le]
  have hv := Nat.mul_le_mul_right (10 ^ L) (by omega : d ≤ d + 1)
  have hl := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 1 ≤ d + 1 + 1)
  omega

/-- The scan-and-push transition changes only cells in the current node's frame. -/
theorem childWrites_subset_nodeWrites {L f d : ℕ} (hd : d < L) :
    childWrites L f d ⊆ nodeWrites L f d := by
  intro c hc
  simp only [childWrites, Finset.mem_union, Block.mem_footprint, Block.Owns] at hc
  rw [mem_nodeWrites_iff hd.le]
  have hprod := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 2 ≤ L + 1)
  have hstep : (d + 1) * 10 ^ L + 10 ^ L = (d + 2) * 10 ^ L := by ring
  rcases hc with (hc | hc) | hc
  · left; left; right
    exact ⟨hc.1, by omega⟩
  · right
    exact hc
  · left; left; left
    omega

/-- The scan-and-skip transition also stays inside the current node's frame. -/
theorem emptyChildWrites_subset_nodeWrites {L f d : ℕ} (hd : d < L) :
    emptyChildWrites L f d ⊆ nodeWrites L f d := by
  intro c hc
  simp only [emptyChildWrites, Finset.mem_union, Block.mem_footprint, Block.Owns] at hc
  rw [mem_nodeWrites_iff hd.le]
  have hprod := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 2 ≤ L + 1)
  have hstep : (d + 1) * 10 ^ L + 10 ^ L = (d + 2) * 10 ^ L := by ring
  rcases hc with (hc | hc) | hc
  · left; left; right
    exact ⟨hc.1, by omega⟩
  · right
    exact hc
  · left; left; left
    omega

/-- No node changes the original input or any other cell below the workspace. -/
theorem notMem_nodeWrites_before {L f d c : ℕ} (hd : d ≤ L) (hc : c < f) :
    c ∉ nodeWrites L f d := by
  rw [mem_nodeWrites_iff hd]
  omega

/-- A node preserves every occupied or unoccupied cell of its own request row. -/
theorem notMem_nodeWrites_list {L f d q : ℕ} (hd : d ≤ L) (hq : q < 10 ^ L) :
    f + 4 * (L + 1) + d * 10 ^ L + q ∉ nodeWrites L f d := by
  rw [mem_nodeWrites_iff hd]
  have hprod := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 1 ≤ L + 1)
  have hnext : d * 10 ^ L + q < (d + 1) * 10 ^ L := by nlinarith only [hq]
  have hvals : d * 10 ^ L + q < (L + 1) * 10 ^ L := hnext.trans_le hprod
  have hsplit : (L + 1) * 10 ^ L ≤ 2 * (L + 1) * 10 ^ L := by
    rw [Nat.mul_assoc]
    omega
  omega

/-- Returning from a child preserves all four words of every ancestor frame. -/
theorem notMem_nodeWrites_ancestor_frame {L f d e j : ℕ} (hd : d ≤ L) (he : e < d)
    (hj : j < 4) : f + 4 * e + j ∉ nodeWrites L f d := by
  rw [mem_nodeWrites_iff hd]
  omega

/-- Returning from a child preserves every value-directory cell in an ancestor's row. -/
theorem notMem_nodeWrites_ancestor_values {L f d e q : ℕ} (hd : d ≤ L) (he : e < d)
    (hq : q < 10 ^ L) :
    f + 4 * (L + 1) + (L + 1) * 10 ^ L + e * 10 ^ L + q ∉ nodeWrites L f d := by
  rw [mem_nodeWrites_iff hd]
  have hprod := Nat.mul_le_mul_right (10 ^ L) (by omega : e + 1 ≤ d)
  have hprodL := Nat.mul_le_mul_right (10 ^ L) (by omega : d ≤ L + 1)
  have hnext : e * 10 ^ L + q < (e + 1) * 10 ^ L := by nlinarith only [hq]
  have hlt : e * 10 ^ L + q < d * 10 ^ L := hnext.trans_le hprod
  have hts : (L + 1) * 10 ^ L + e * 10 ^ L + q < 2 * (L + 1) * 10 ^ L := by
    nlinarith only [hlt, hprodL]
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
