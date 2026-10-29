/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.TowerTable
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Tactic.PolyTime

/-!
# Polynomial-time construction of zig-zag tower tables

The input size is unary: construction is polynomial in the number of vertices, rather than in
its bit length. The invariant charges every entry of every intermediate table, including its
unary neighbor, finite return label and framing. Fixed base rotations use finite case analysis.

## Main results

* `Cslib.RotationMap.TowerTable.polytime_next`,
  `Cslib.RotationMap.TowerTable.polytime_nextRow`: constructing next level and rows in polytime.
* `Cslib.RotationMap.TowerTable.polytime_build`: a uniform certificate for the complete table.
* `Cslib.RotationMap.TowerTable.polytime_lookup`: read both components of a stored rotation.
* `Cslib.RotationMap.TowerTable.length_encoding_le`: bound all rows and encoded entries.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002], Section 1.2.
-/

@[expose] public section

namespace Cslib.RotationMap

open Turing.MultiTapeTM

namespace TowerTable

variable {D : Type} {b : ℕ}

variable [Fintype D]

/-- Encode complete tables, including every unary neighbor and finite return label. -/
noncomputable abbrev encoding (label : D ↪ List Bool) : TowerTable D ↪ List Bool :=
  encList (encPi (encPair encUnary (encPair label label)))

private def vertexEncoding : Fin b ↪ List Bool :=
  ⟨fun vertex => encUnary vertex.val, fun _ _ h => Fin.val_injective (encUnary.injective h)⟩

/-- A table lookup charges its complete stored prefix and its returned entry. -/
@[fun_prop]
theorem polytime_lookup (label : D ↪ List Bool) :
    ComputableInPolyTime (fun p : TowerTable D × (ℕ × (D × D)) =>
      p.1.lookup p.2.1 p.2.2)
      (encPair (encoding label) (encPair encUnary (encPair label label)))
      (encPair encUnary (encPair label label)) := by
  let row : ((D × D) → ℕ × (D × D)) ↪ List Bool :=
    encPi (encPair encUnary (encPair label label))
  let rows := encList row
  have htail : ComputableInPolyTime List.tail rows rows := by
    obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.tail (enc₁ := row) (enc := rows)
    exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
      k, Q, hfin, tm, fun l => htm l⟩
  have heq (l : List ((D × D) → ℕ × (D × D))) (n : ℕ) :
      (List.replicate n true).foldl (fun acc _ => acc.tail) l = l.drop n := by
    simp [List.foldl_const, List.tail_iterate]
  have hdrop : ComputableInPolyTime
      (fun p : List ((D × D) → ℕ × (D × D)) × ℕ => p.1.drop p.2)
      (encPair rows encUnary) rows := by
    have hfold := ComputableInPolyTime.foldl' (encA := encBool) (encL := encBits)
      (list := fun p : List ((D × D) → ℕ × (D × D)) × ℕ => List.replicate p.2 true)
      (step := fun acc _ => acc.tail)
      ((ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits)
        (fun _ => rfl)).comp (ComputableInPolyTime.snd rows encUnary))
      (ComputableInPolyTime.fst rows encUnary)
      (htail.comp (ComputableInPolyTime.fst rows encBool))
      (B := fun p => (encPair rows encUnary p).length) .self (fun p i _ => by
        rw [List.take_replicate, heq]
        have := SizedListEncoding.length_drop_le (encA := row) (encL := rows) p.1 (min i p.2)
        simp only [length_encPair]
        omega)
    simpa only [heq] using hfold
  have hhead : ComputableInPolyTime
      (fun l : List ((D × D) → ℕ × (D × D)) => l.headD (fun label => (0, label))) rows row := by
    obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.headD
      (enc₁ := row) (enc := rows) (fun label => (0, label))
    exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
      k, Q, hfin, tm, fun l => htm l⟩
  have htable := ComputableInPolyTime.fst rows (encPair encUnary (encPair label label))
  have hargs := ComputableInPolyTime.snd rows (encPair encUnary (encPair label label))
  have hrow := hhead.comp (hdrop.comp (htable.prod hargs.fst'))
  have hp := ComputableInPolyTime.pi_apply' hrow hargs.snd'
  simpa only [lookup, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD, Function.comp_def, encoding, rows, row] using hp

/-- Each new row uses two stored rotations and fixed finite base operations. -/
@[fun_prop]
theorem polytime_nextRow (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (label : D ↪ List Bool) :
    ComputableInPolyTime (fun p : TowerTable D × ℕ => nextRow H e hb p.1 p.2)
      (encPair (encoding label) encUnary)
      (encPi (encPair encUnary (encPair label label))) := by
  have hbase : ComputableInPolyTime H.rot
      (encPair vertexEncoding label) (encPair vertexEncoding label) := .of_finite _
  have hencode : ComputableInPolyTime (fun p : (D × D) × (D × D) =>
      e.symm ![p.1, p.2]) (encPair (encPair label label) (encPair label label))
      vertexEncoding := .of_finite _
  have hleft : ComputableInPolyTime (fun vertex => e vertex 0) vertexEncoding
      (encPair label label) := .of_finite _
  have hright : ComputableInPolyTime (fun vertex => e vertex 1) vertexEncoding
      (encPair label label) := .of_finite _
  have hval : ComputableInPolyTime (Fin.val : Fin b → ℕ) vertexEncoding encUnary :=
    .of_eq (fun _ => rfl)
  apply ComputableInPolyTime.pi
  intro edge
  have htable := ComputableInPolyTime.fst (encoding label) encUnary
  have hvertex := ComputableInPolyTime.snd (encoding label) encUnary
  have hfirst := hbase.comp
    (((ComputableInPolyTime.unary_finMod hb vertexEncoding).comp hvertex).prod
    (ComputableInPolyTime.const edge.1))
  have hmiddle₁ := (polytime_lookup label).comp (htable.prod
    (((ComputableInPolyTime.unary_div_const b).comp hvertex).prod
      (hleft.comp hfirst.fst')))
  have hmiddle₂ := (polytime_lookup label).comp
    (htable.prod (hmiddle₁.fst'.prod (hright.comp hfirst.fst')))
  have hlast := hbase.comp ((hencode.comp (hmiddle₂.snd'.prod hmiddle₁.snd')).prod
    (ComputableInPolyTime.const edge.2))
  unfold nextRow
  exact ((ComputableInPolyTime.unary_add).comp
    (((ComputableInPolyTime.unary_mul).comp
      (hmiddle₂.fst'.prod (ComputableInPolyTime.const b))).prod
      (hval.comp hlast.fst'))).prod (hlast.snd'.prod hfirst.snd')

/-- Construct the complete next level, accounting for every row and label. -/
@[fun_prop]
theorem polytime_next (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 0 < b) (label : D ↪ List Bool) :
    ComputableInPolyTime (next H e hb) (encoding label) (encoding label) := by
  unfold next
  have hrow := polytime_nextRow H e hb label
  unfold encoding at hrow ⊢
  exact ComputableInPolyTime.mapWithInput (by fun_prop) hrow

/-- Every stored word, finite table, and row delimiter contributes to the size bound. -/
theorem length_encoding_le (label : D ↪ List Bool) {table : TowerTable D} (h : table.Valid)
    {size : ℕ} (hsize : table.length ≤ size) :
    (encoding label table).length ≤
      size * (2 * Fintype.card (D × D) *
        (2 * (2 * size + 3 * Finset.univ.sup (fun d => (label d).length) + 2) + 1) + 1) := by
  let bound := Finset.univ.sup fun d => (label d).length
  have hlabel (d : D) : (label d).length ≤ bound :=
    Finset.le_sup (f := fun d => (label d).length) (Finset.mem_univ d)
  have hrows (row : (D × D) → ℕ × (D × D)) (hrow : row ∈ table) :
      (encPi (encPair encUnary (encPair label label)) row).length ≤
        Fintype.card (D × D) * (2 * (2 * size + 3 * bound + 2) + 1) := by
    apply length_encPi_le
    intro edge
    rw [length_encPair, length_encPair]
    simp only [encUnary_apply, List.length_replicate]
    have := h row hrow edge
    have := hlabel (row edge).2.1
    have := hlabel (row edge).2.2
    lia
  apply (length_encList_le _ table hrows).trans
  simpa only [bound, Nat.mul_assoc] using Nat.mul_le_mul_right
    (2 * (Fintype.card (D × D) * (2 * (2 * size + 3 * bound + 2) + 1)) + 1) hsize

omit [Fintype D] in
private theorem length_iterate_le (H : RotationMap (Fin b) D)
    (e : Fin b ≃ (Fin 2 → D × D)) (hb : 1 < b) {size level : ℕ}
    (hlevel : level ≤ Nat.clog b size - 1) :
    ((next H e (by lia))^[level] (initial H)).length ≤ b * (size + 1) := by
  rw [length_iterate]
  by_cases hsize : 2 ≤ size
  · exact (Nat.pow_le_pow_right (by lia) (Nat.add_le_add_right hlevel 1)).trans
      ((zigzagTower_size_bounds hb hsize).2.trans (Nat.mul_le_mul_left b (by lia)))
  · have hclog : Nat.clog b size = 0 := Nat.clog_of_right_le_one (show size ≤ 1 by lia) b
    have : level = 0 := by lia
    simp only [this, zero_add, pow_one]
    nlinarith

/-- Building the selected tower table is polynomial in the unary requested vertex count.
The invariant bounds complete intermediate tables, not only their numbers of rows. -/
@[fun_prop]
theorem polytime_build (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D))
    (hb : 1 < b) (label : D ↪ List Bool) :
    ComputableInPolyTime (build H e (by lia)) encUnary (encoding label) := by
  apply ComputableInPolyTime.iterate
    (count := fun size => Nat.clog b size - 1) (init := fun _ => initial H)
    (step := next H e (by lia)) (by fun_prop) (by fun_prop) (polytime_next H e (by lia) label)
    (bound := fun size => (b * (size + 1)) * (2 * Fintype.card (D × D) *
      (2 * (2 * (b * (size + 1)) + 3 * Finset.univ.sup (fun d => (label d).length) + 2) + 1) + 1))
  · exact ComputableInPolyTime.polyBounded (by fun_prop)
  · intro size level hlevel
    exact length_encoding_le label (valid_iterate H e (by lia) level)
      (length_iterate_le H e hb hlevel)

end TowerTable

end Cslib.RotationMap
