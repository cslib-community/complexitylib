/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Complexity.Problems.Graph

/-!
# Reduced-Laplacian determinant tables for polynomial-time graph counting

Shared bridge between list-tabulated integer matrices evaluated by
`Cslib.Circuits.Rational.detRows` and submatrix determinants over declared vertex sets of
`Cslib.Complexity.Graph`.

## Main results

* `Cslib.Complexity.detRows_map_eq`: `detRows` of a vertex-list table equals the determinant of a
  matrix indexed by any type in bijection with the vertex list.
* `Cslib.Complexity.detRows_filter_ne_eq`: `detRows` after filtering out a root vertex `r` equals
  the reduced submatrix determinant at `r`.
* `Cslib.Complexity.Graph.vertexEquiv_getElem`: `G.vertexEquiv` indexing equation.
* `Cslib.Complexity.computableInPolyTime_filter_ne`: filtering a vertex list to omit a computed
  vertex runs in polynomial time.
* `Cslib.Complexity.computableInPolyTime_detRows_map`: building a vertex-indexed integer table and
  taking `detRows` runs in polynomial time.
-/

public section

namespace Cslib.Complexity

open Turing MultiTapeTM

/-- Evaluating `Cslib.Circuits.Rational.detRows` on a table indexed by a vertex list `vs` gives
the determinant of any matrix `M` in bijection with `vs` whose entries match `entry`. -/
theorem detRows_map_eq {vs : List ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (e : Fin vs.length ≃ V) (M : Matrix V V ℤ) (entry : ℕ → ℕ → ℤ)
    (hM : ∀ i j : Fin vs.length, entry vs[i] vs[j] = M (e i) (e j)) :
    Cslib.Circuits.Rational.detRows (vs.map fun u => vs.map fun v => entry u v) = M.det := by
  rw [Cslib.Circuits.Rational.detRows_eq_det_of_rowEntry (M.submatrix e e) (List.length_map _)]
  · exact Matrix.det_submatrix_equiv_self e M
  · intro i j
    have hi : (i : ℕ) < (vs.map fun u => vs.map fun v => entry u v).length := by
      simpa only [List.length_map] using i.isLt
    have hj : (j : ℕ) < (vs.map fun v => entry vs[(i : ℕ)] v).length := by
      simpa only [List.length_map] using j.isLt
    simp only [Cslib.rowEntry, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_map,
      List.getElem?_eq_getElem hj, Option.getD_some, List.getElem_map, Matrix.submatrix_apply]
    exact hM i j

/-- Evaluating `Cslib.Circuits.Rational.detRows` after deleting vertex `r` from a duplicate-free
vertex list `vs` equals the determinant of the `(r, r)` minor of `M`. -/
theorem detRows_filter_ne_eq {vs : List ℕ} (hnd : vs.Nodup) {r : ℕ} (hr : r ∈ vs)
    [Fintype {v // v ∈ vs}]
    (M : Matrix {v // v ∈ vs} {v // v ∈ vs} ℤ) (entry : ℕ → ℕ → ℤ)
    (hM : ∀ u v : {v // v ∈ vs}, u ≠ ⟨r, hr⟩ → v ≠ ⟨r, hr⟩ → entry u.1 v.1 = M u v) :
    Cslib.Circuits.Rational.detRows
        ((vs.filter fun v => decide (v ≠ r)).map fun u =>
          (vs.filter fun v => decide (v ≠ r)).map fun v => entry u v) =
      (M.submatrix (Subtype.val : {x : {v // v ∈ vs} // x ≠ ⟨r, hr⟩} → {v // v ∈ vs})
        Subtype.val).det := by
  let rest := vs.filter fun v => decide (v ≠ r)
  have hmem : ∀ v, v ∈ rest ↔ v ∈ vs ∧ v ≠ r := by
    intro v
    simp [rest]
  have hrest_nd : rest.Nodup := hnd.filter _
  let e : Fin rest.length ≃ {x : {v // v ∈ vs} // x ≠ ⟨r, hr⟩} :=
    (hrest_nd.getEquiv rest).trans
      { toFun := fun v =>
          ⟨⟨v.1, ((hmem v.1).1 v.2).1⟩, fun h => ((hmem v.1).1 v.2).2 (congrArg Subtype.val h)⟩
        invFun := fun ⟨⟨v, hv⟩, hne⟩ => ⟨v, (hmem v).2 ⟨hv, fun h => hne (Subtype.ext h)⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  exact detRows_map_eq e (M.submatrix Subtype.val Subtype.val) entry fun i j =>
    hM (e i).1 (e j).1 (e i).2 (e j).2

/-- Variant of `detRows_filter_ne_eq` transported along a bijection `e : {v // v ∈ vs} ≃ V` to
match matrices already indexed by `V` (such as `{v // v ∈ G.1}`). -/
theorem detRows_filter_ne_equiv_eq {vs : List ℕ} (hnd : vs.Nodup)
    {V : Type*} [Fintype V] [DecidableEq V] (e : {v // v ∈ vs} ≃ V)
    {r : ℕ} (hr : r ∈ vs) (M : Matrix V V ℤ) (entry : ℕ → ℕ → ℤ)
    (hM : ∀ u v : {x // x ∈ vs}, u ≠ ⟨r, hr⟩ → v ≠ ⟨r, hr⟩ → entry u.1 v.1 = M (e u) (e v)) :
    Cslib.Circuits.Rational.detRows
        ((vs.filter fun v => decide (v ≠ r)).map fun u =>
          (vs.filter fun v => decide (v ≠ r)).map fun v => entry u v) =
      (M.submatrix (Subtype.val : {y : V // y ≠ e ⟨r, hr⟩} → V) Subtype.val).det := by
  have : Fintype {v // v ∈ vs} := Fintype.ofEquiv V e.symm
  let eSub : {x : {v // v ∈ vs} // x ≠ ⟨r, hr⟩} ≃ {y : V // y ≠ e ⟨r, hr⟩} :=
    Equiv.subtypeEquiv e fun x => by simp
  rw [detRows_filter_ne_eq hnd hr (M.submatrix e e) entry fun u v hu hv => by
    simpa only [Matrix.submatrix_apply] using hM u v hu hv]
  exact Matrix.det_submatrix_equiv_self eSub (M.submatrix Subtype.val Subtype.val)

/-- Indexing equivalence `G.vertexEquiv` evaluates to `G.distinctVertices[i]`. -/
theorem Graph.vertexEquiv_getElem (G : Graph) (i : Fin G.distinctVertices.length) :
    (G.vertexEquiv i : ℕ) = G.distinctVertices[i] := by
  rw [Graph.vertexEquiv_apply, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem i.isLt, Option.getD_some]
  rfl

/-- Filtering a vertex list to remove a computed vertex runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_filter_ne {γ : Type} {encIn : γ ↪ List Bool}
    {vs : γ → List ℕ} {r : γ → ℕ}
    (hvs : ComputableInPolyTime vs encIn (encList encNat))
    (hr : ComputableInPolyTime r encIn encNat) :
    ComputableInPolyTime (fun x => (vs x).filter fun v => decide (v ≠ r x))
      encIn (encList encNat) := by
  refine ComputableInPolyTime.filterWithInput hvs ?_
  have heq : ComputableInPolyTime (fun p : γ × ℕ => decide (p.2 = r p.1))
      (encPair encIn encNat) encBool :=
    (ComputableInPolyTime.snd encIn encNat).decide_eq'
      (hr.comp (ComputableInPolyTime.fst encIn encNat))
  simpa only [Function.comp_def, decide_not] using ComputableInPolyTime.bool_not.comp heq

/-- Tabulating an integer matrix over a computed vertex list and computing its determinant with
`Cslib.Circuits.Rational.detRows` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_detRows_map {γ : Type} {encIn : γ ↪ List Bool}
    {verts : γ → List ℕ} {entry : γ → ℕ → ℕ → ℤ}
    (hverts : ComputableInPolyTime verts encIn (encList encNat))
    (hentry : ComputableInPolyTime (fun p : (γ × ℕ) × ℕ => entry p.1.1 p.1.2 p.2)
      (encPair (encPair encIn encNat) encNat) encIntBin) :
    ComputableInPolyTime
      (fun x => Cslib.Circuits.Rational.detRows
        ((verts x).map fun u => (verts x).map fun v => entry x u v))
      encIn encIntBin := by
  refine Cslib.Circuits.Rational.detRows_polytime.comp (ComputableInPolyTime.mapWithInput hverts ?_)
  exact ComputableInPolyTime.mapWithInput (hverts.comp (ComputableInPolyTime.fst encIn encNat))
    hentry

end Cslib.Complexity
