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
  have hbij : Function.Bijective (fun i : Fin rest.length =>
      (⟨⟨rest[i], ((hmem _).1 (List.getElem_mem _)).1⟩,
        fun h => ((hmem _).1 (List.getElem_mem _)).2
          (congrArg Subtype.val h)⟩ : {x : {v // v ∈ vs} // x ≠ ⟨r, hr⟩})) := by
    refine ⟨fun i j h => Fin.ext (hrest_nd.getElem_inj_iff.1 (congrArg (fun x => x.1.1) h)), ?_⟩
    rintro ⟨⟨v, hv⟩, hne⟩
    have hv_rest : v ∈ rest := (hmem v).2 ⟨hv, fun h => hne (Subtype.ext h)⟩
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hv_rest
    exact ⟨⟨i, hi⟩, Subtype.ext (Subtype.ext hget)⟩
  let e : Fin rest.length ≃ {x : {v // v ∈ vs} // x ≠ ⟨r, hr⟩} := Equiv.ofBijective _ hbij
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

/-- Bijection between indices `Fin G.distinctVertices.length` and the declared vertices
`{v // v ∈ G.1}` of a `Graph`. -/
noncomputable def Graph.distinctEquiv (G : Graph) :
    Fin G.distinctVertices.length ≃ {v // v ∈ G.1} :=
  Equiv.ofBijective
    (fun i : Fin G.distinctVertices.length =>
      ⟨G.distinctVertices[i], Graph.mem_distinctVertices.1 (List.getElem_mem _)⟩)
    ⟨fun i j h => Fin.ext (G.nodup_distinctVertices.getElem_inj_iff.1 (congrArg Subtype.val h)),
      fun ⟨x, hx⟩ =>
        let ⟨i, hi, hg⟩ := List.mem_iff_getElem.1 (Graph.mem_distinctVertices.2 hx)
        ⟨⟨i, hi⟩, Subtype.ext hg⟩⟩

@[simp]
theorem Graph.distinctEquiv_val (G : Graph) (i : Fin G.distinctVertices.length) :
    (G.distinctEquiv i : ℕ) = G.distinctVertices[i] := by
  unfold Graph.distinctEquiv
  rfl

/-- Rewrite the sum of a function mapped over a list as a `Finset.sum` over `Fin xs.length`. -/
theorem sum_map_eq_sum_fin {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i] := by
  conv_lhs => rw [← List.ofFn_getElem (xs := xs)]
  rw [List.map_ofFn, List.sum_ofFn]
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
