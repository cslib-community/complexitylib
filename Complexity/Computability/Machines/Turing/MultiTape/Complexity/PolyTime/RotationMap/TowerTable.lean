/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.TowerFamily
import Mathlib.Data.List.GetD

/-!
# Complete rotation tables for the zig-zag tower

Build a table one level at a time using two previous-table lookups and two fixed-base rotations.
Each row stores the neighboring vertex and return label for every fixed edge label. Arithmetic
numbering agrees with the existing mathematical tower. Resource certificates live separately
in `Computability/Machines/Turing/MultiTape/Complexity/PolyTime/RotationMap/Tower`.

## Main definitions

* `Cslib.RotationMap.TowerTable`: complete rotation tables with fixed edge labels.
* `Cslib.RotationMap.TowerTable.lookup`: read a rotation from a table, defaulting out of range.
* `Cslib.RotationMap.TowerTable.Valid`: every stored neighbor is a row of the table.
* `Cslib.RotationMap.TowerTable.initial`: the table of the squared fixed base.
* `Cslib.RotationMap.TowerTable.nextRow`: a row of the next square-and-zig-zag level.
* `Cslib.RotationMap.TowerTable.next`: construct the next square-and-zig-zag level.
* `Cslib.RotationMap.TowerTable.build`: build the first level large enough for a requested size.

## Main results

* `Cslib.RotationMap.TowerTable.Valid.lookup_lt`,
  `Cslib.RotationMap.TowerTable.lookup_iterate_numbered`: neighbor range preservation and numbered
  tower agreement.
* `Cslib.RotationMap.TowerTable.valid_iterate`: every stored neighbor remains in range.
* `Cslib.RotationMap.TowerTable.lookup_build`: exact agreement with the numbered tower.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002], Section 1.2.
-/

@[expose] public section

namespace Cslib.RotationMap

/-- A complete rotation table: a row for each numbered vertex and each fixed edge label. -/
abbrev TowerTable (D : Type) := List ((D × D) → ℕ × (D × D))

namespace TowerTable

variable {D : Type} {b : ℕ}

/-- Read a rotation, returning vertex zero with the same label for an out-of-range row. -/
def lookup (table : TowerTable D) (vertex : ℕ) (label : D × D) : ℕ × (D × D) :=
  (table.getD vertex (fun label => (0, label))) label

/-- Every stored neighbor is a valid vertex of the table. -/
def Valid (table : TowerTable D) : Prop :=
  ∀ row ∈ table, ∀ label, (row label).1 < table.length

/-- The fixed base, squared, gives the initial rotation table. -/
def initial (H : RotationMap (Fin b) D) : TowerTable D :=
  List.ofFn fun vertex : Fin b => fun label =>
    let first := H.rot (vertex, label.1)
    let last := H.rot (first.1, label.2)
    (last.1.val, (last.2, first.2))

/-- A row of the next square-and-zig-zag level, with arithmetic vertex numbering. -/
def nextRow (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (table : TowerTable D) (vertex : ℕ) (label : D × D) : ℕ × (D × D) :=
  let first := H.rot (⟨vertex % b, Nat.mod_lt _ hb⟩, label.1)
  let middle₁ := table.lookup (vertex / b) (e first.1 0)
  let middle₂ := table.lookup middle₁.1 (e first.1 1)
  let last := H.rot (e.symm ![middle₂.2, middle₁.2], label.2)
  (middle₂.1 * b + last.1.val, (last.2, first.2))

/-- Construct every row of the next level from the preceding table. -/
def next (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (table : TowerTable D) : TowerTable D :=
  (List.range (table.length * b)).map (nextRow H e hb table)

/-- Construct the tower level selected by the ceiling logarithm of the requested size. -/
def build (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (size : ℕ) : TowerTable D :=
  (next H e hb)^[Nat.clog b size - 1] (initial H)

/-- The initial table has one row for each of the `b` base vertices. -/
@[simp] theorem length_initial (H : RotationMap (Fin b) D) : (initial H).length = b :=
  List.length_ofFn

/-- The next level has `b` rows for each row of the table. -/
@[simp] theorem length_next (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (table : TowerTable D) : (next H e hb table).length = table.length * b := by
  simp [next]

/-- The initial table stores valid neighbors. -/
theorem valid_initial (H : RotationMap (Fin b) D) : (initial H).Valid := by
  intro row hrow label
  obtain ⟨vertex, rfl⟩ := List.mem_ofFn.mp hrow
  simpa only [length_initial] using (H.rot ((H.rot (vertex, label.1)).1, label.2)).1.isLt

/-- Lookup at a valid row returns a valid neighbor. -/
theorem Valid.lookup_lt {table : TowerTable D} (h : table.Valid) {vertex : ℕ}
    (hv : vertex < table.length) (label : D × D) :
    (table.lookup vertex label).1 < table.length := by
  unfold lookup
  rw [List.getD_eq_getElem _ _ hv]
  exact h _ (List.getElem_mem hv) label

/-- One complete level preserves the range of every neighbor. -/
theorem Valid.next {table : TowerTable D} (h : table.Valid)
    (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D)) (hb : 0 < b) :
    (next H e hb table).Valid := by
  intro row hrow label
  obtain ⟨vertex, hvertex, rfl⟩ := List.mem_map.mp hrow
  have hv : vertex / b < table.length := Nat.div_lt_iff_lt_mul hb |>.mpr
    (List.mem_range.mp hvertex)
  have h₁ := h.lookup_lt hv (e (H.rot (⟨vertex % b, Nat.mod_lt _ hb⟩, label.1)).1 0)
  have h₂ := h.lookup_lt h₁ (e (H.rot (⟨vertex % b, Nat.mod_lt _ hb⟩, label.1)).1 1)
  dsimp only [nextRow]
  rw [length_next]
  generalize H.rot (e.symm
    ![(table.lookup (table.lookup (vertex / b)
      (e (H.rot (⟨vertex % b, Nat.mod_lt _ hb⟩, label.1)).1 0)).1
      (e (H.rot (⟨vertex % b, Nat.mod_lt _ hb⟩, label.1)).1 1)).2,
      (table.lookup (vertex / b)
      (e (H.rot (⟨vertex % b, Nat.mod_lt _ hb⟩, label.1)).1 0)).2], label.2) = last
  have hlast := last.1.isLt
  nlinarith

/-- The complete table after `level` rounds has exactly the tower's vertex count. -/
theorem length_iterate (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (level : ℕ) :
    ((next H e hb)^[level] (initial H)).length = b ^ (level + 1) := by
  induction level with
  | zero => simp
  | succ level ih => rw [Function.iterate_succ_apply', length_next, ih, pow_succ b (level + 1)]

/-- Every intermediate level stores valid neighbor indices. -/
theorem valid_iterate (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (level : ℕ) : ((next H e hb)^[level] (initial H)).Valid := by
  induction level with
  | zero => exact valid_initial H
  | succ level ih =>
    simpa only [Function.iterate_succ_apply'] using ih.next H e hb

private theorem square_relabel_rotation {V E B : Type*} (G : RotationMap V E)
    (e : B ≃ (Fin 2 → E)) (vertex : V) (label : B) :
    ((G.pow 2).relabel e.symm).rot (vertex, label) =
      let step₁ := G.rot (vertex, e label 0)
      let step₂ := G.rot (step₁.1, e label 1)
      (step₂.1, e.symm ![step₂.2, step₁.2]) := by
  apply Prod.ext
  · rfl
  · apply congrArg e.symm
    ext i
    fin_cases i <;> rfl

private theorem lookup_initial (H : RotationMap (Fin b) D) (vertex : Fin b) (label : D × D) :
    (initial H).lookup vertex.val label =
      let step₁ := H.rot (vertex, label.1)
      let step₂ := H.rot (step₁.1, label.2)
      (step₂.1.val, (step₂.2, step₁.2)) := by
  simp [lookup, initial, vertex.isLt]

private theorem lookup_next (H : RotationMap (Fin b) D)
    (e : Fin b ≃ (Fin 2 → D × D)) (hb : 0 < b) (table : TowerTable D)
    {vertex : ℕ} (hv : vertex < table.length * b) (label : D × D) :
    (next H e hb table).lookup vertex label = nextRow H e hb table vertex label := by
  simp [lookup, next, hv]

/-- A table built from a numbered base retains the original tower's exact rotation. -/
theorem lookup_iterate_numbered {B : Type*} (H : RotationMap B D)
    (e : B ≃ (Fin 2 → D × D)) (numbering : B ≃ Fin b) (hb : 0 < b)
    (level : ℕ) (vertex : ZigzagTowerVertex B level) (label : D × D) :
    ((next (H.reindex numbering) (numbering.symm.trans e) hb)^[level]
      (initial (H.reindex numbering))).lookup
        (ZigzagTowerVertex.equivFin numbering level vertex).val label =
      ((ZigzagTowerVertex.equivFin numbering level
          ((zigzagTower H e level).rot (vertex, label)).1).val,
        ((zigzagTower H e level).rot (vertex, label)).2) := by
  induction level generalizing label with
  | zero =>
    change B at vertex
    rw [Function.iterate_zero_apply]
    change (initial (H.reindex numbering)).lookup (numbering vertex).val label = _
    rw [lookup_initial]
    simp only [reindexRot, Equiv.symm_apply_apply]
    rfl
  | succ level ih =>
    rcases vertex with ⟨vertex, cloud⟩
    rcases label with ⟨first, second⟩
    have hstep (u : ZigzagTowerVertex B level) (c : B) :
        (ZigzagTowerVertex.equivFin numbering (level + 1) (u, c)).val =
          (ZigzagTowerVertex.equivFin numbering level u).val * b + (numbering c).val := by
      change (numbering c).val + b * (ZigzagTowerVertex.equivFin numbering level u).val = _
      ring
    have hindex : (ZigzagTowerVertex.equivFin numbering (level + 1) (vertex, cloud)).val <
        ((next (H.reindex numbering) (numbering.symm.trans e) hb)^[level]
          (initial (H.reindex numbering))).length * b := by
      rw [length_iterate, ← pow_succ]
      exact (ZigzagTowerVertex.equivFin numbering (level + 1) (vertex, cloud)).isLt
    rw [Function.iterate_succ_apply', lookup_next _ _ _ _ hindex, hstep]
    have hmod :
        ((ZigzagTowerVertex.equivFin numbering level vertex).val * b + (numbering cloud).val) % b =
          (numbering cloud).val := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt (numbering cloud).isLt]
    have hdiv :
        ((ZigzagTowerVertex.equivFin numbering level vertex).val * b + (numbering cloud).val) / b =
          (ZigzagTowerVertex.equivFin numbering level vertex).val := by
      rw [Nat.mul_comm (ZigzagTowerVertex.equivFin numbering level vertex).val,
        Nat.mul_add_div hb, Nat.div_eq_of_lt (numbering cloud).isLt, Nat.add_zero]
    simp only [nextRow, hmod, hdiv, reindexRot, Equiv.trans_apply, Fin.eta,
      Equiv.symm_apply_apply, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
    rw [ih, ih]
    simp only [rot_zigzagTower_succ, zigzagRot, square_relabel_rotation, hstep]

/-- The selected complete table has the exact cardinality used by the tower family. -/
theorem length_build (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (size : ℕ) :
    (build H e hb size).length = b ^ (Nat.clog b size - 1 + 1) :=
  length_iterate H e hb _

/-- Reading a selected table agrees with the numbered tower, including its return label. -/
theorem lookup_build {B : Type*} (H : RotationMap B D) (e : B ≃ (Fin 2 → D × D))
    (numbering : B ≃ Fin b) (hb : 0 < b) (size : ℕ)
    (vertex : Fin (b ^ (Nat.clog b size - 1 + 1))) (label : D × D) :
    (build (H.reindex numbering) (numbering.symm.trans e) hb size).lookup vertex.val label =
      let target := ((zigzagTower H e (Nat.clog b size - 1)).reindex
        (ZigzagTowerVertex.equivFin numbering (Nat.clog b size - 1))).rot (vertex, label)
      (target.1.val, target.2) := by
  simpa only [build, Equiv.apply_symm_apply, reindexRot] using
    lookup_iterate_numbered H e numbering hb (Nat.clog b size - 1)
      ((ZigzagTowerVertex.equivFin numbering (Nat.clog b size - 1)).symm vertex) label

end TowerTable

end Cslib.RotationMap
