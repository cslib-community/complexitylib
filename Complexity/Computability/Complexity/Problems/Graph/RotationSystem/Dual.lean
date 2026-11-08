/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
public import Complexity.Foundations.GroupTheory.Perm.Doubled
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD

/-!
# The indexed dual of a rotation system

The dual retains every edge-list position. Its vertices are the least dart indices of all
source face orbits, including singleton orbits. Its rotation is the source face successor.
Declared isolated source vertices have no darts and hence contribute no dual vertex.

This is an original finite permutation construction. It does not assert geometric realization
or give a native certificate compiler.

## Main definitions

* `Cslib.Complexity.Graph.RotationSystem.faceId`: canonical least-index face name.
* `Cslib.Complexity.Graph.RotationSystem.dualGraph`: listed dual with the same edge positions.
* `Cslib.Complexity.Graph.RotationSystem.dualRotation`: the actual dual rotation.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- Finite dart indices in an actual face orbit, including its least index. -/
@[expose] def faceDartIndices (d : Dart G) : Finset (Fin (2 * G.2.length)) :=
  Finset.univ.filter fun i => r.faceNext.SameCycle d ((Dart.indexEquiv G).symm i)

/-- Every dart belongs to its own face orbit. -/
theorem faceDartIndices_nonempty (d : Dart G) : (r.faceDartIndices d).Nonempty :=
  ⟨Dart.indexEquiv G d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.Perm.SameCycle.rfl (f := r.faceNext) (x := d))⟩⟩

/-- The least dart index in the actual face orbit, including a singleton orbit. It is computed
over the finite dart universe, independently of the magnitudes of source vertex names. -/
@[expose] def faceId (d : Dart G) : ℕ :=
  ((r.faceDartIndices d).min' (r.faceDartIndices_nonempty d)).val

/-- The canonical name is attained by a least-index dart in the same actual face orbit. -/
theorem faceId_spec (d : Dart G) :
    ∃ e : Dart G, e.index = r.faceId d ∧ r.faceNext.SameCycle d e ∧
      r.IsFaceRepresentative e := by
  let i := (r.faceDartIndices d).min' (r.faceDartIndices_nonempty d)
  have hi : i ∈ r.faceDartIndices d := Finset.min'_mem _ _
  have hdi := (Finset.mem_filter.mp hi).2
  refine ⟨(Dart.indexEquiv G).symm i, ?_, hdi, ?_⟩
  · exact congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply i)
  · intro e he
    have hm : Dart.indexEquiv G e ∈ r.faceDartIndices d :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [Equiv.symm_apply_apply] using hdi.trans he⟩
    have := Finset.min'_le _ _ hm
    change i.val ≤ e.index at this
    simpa only [← show ((Dart.indexEquiv G).symm i).index = i.val from
      congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply i)] using this

/-- Canonical face names agree exactly on source face orbits. -/
theorem faceId_eq_iff (d e : Dart G) :
    r.faceId d = r.faceId e ↔ r.faceNext.SameCycle d e := by
  obtain ⟨d', hd', hdd', -⟩ := r.faceId_spec d
  obtain ⟨e', he', hee', -⟩ := r.faceId_spec e
  constructor
  · intro h
    have heq : d' = e' := (Dart.indexEquiv G).injective (Fin.ext (hd'.trans (h.trans he'.symm)))
    exact hdd'.trans (heq ▸ hee'.symm)
  · intro h
    have hs : r.faceDartIndices d = r.faceDartIndices e := by
      ext i
      simp only [faceDartIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi => h.symm.trans hi, fun hi => h.trans hi⟩
    simp only [faceId, hs]

/-- A dart is the canonical representative exactly when its index is its face's name. -/
theorem faceId_eq_index_iff (d : Dart G) :
    r.faceId d = d.index ↔ r.IsFaceRepresentative d := by
  obtain ⟨e, he, hde, hre⟩ := r.faceId_spec d
  constructor
  · intro h
    have hed : e = d := (Dart.indexEquiv G).injective (Fin.ext (he.trans h))
    exact hed ▸ hre
  · intro h
    have hed := (r.existsUnique_faceRepresentative d).unique ⟨hde, hre⟩ ⟨.rfl, h⟩
    exact he.symm.trans (congrArg Dart.index hed)

/-- The canonical face name is bounded by the number of darts, even for huge vertex labels. -/
theorem faceId_lt (d : Dart G) : r.faceId d < 2 * G.2.length :=
  ((r.faceDartIndices d).min' (r.faceDartIndices_nonempty d)).isLt

/-- Canonical dual vertex equality is exactly the existing executable face-table orbit test.
This links the abstract construction to `faceTable (ofRotation r)` without another face
enumeration or an existentially chosen relabeling. -/
theorem faceId_eq_iff_faceTable
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d e : Dart G) :
    r.faceId d = r.faceId e ↔
      RotationCertificate.orbitBool (2 * G.2.length)
        (RotationCertificate.faceTable G (RotationCertificate.ofRotation r)) d.index e.index =
        true := by
  rw [r.faceId_eq_iff]
  have ht (a : Dart G) :
      (RotationCertificate.faceTable G (RotationCertificate.ofRotation r)).getD a.index 0 =
        (r.faceNext a).index := by
    have h := RotationCertificate.getD_faceTable
      (RotationCertificate.verifyRotation_ofRotation r hG) a
    rwa [RotationCertificate.decode_ofRotation r hG] at h
  exact (RotationCertificate.orbitBool_eq_true_iff r.faceNext _ ht d e).symm

/-- The listed dual has one vertex per actual face and one edge per source edge occurrence.
The first/second ends of edge `i` are the faces of darts `(i,false)` and `(i,true)`. -/
@[expose] def dualGraph : Graph :=
  (((List.finRange (2 * G.2.length)).map fun i =>
      r.faceId ((Dart.indexEquiv G).symm i)).dedup,
    List.ofFn fun i : Fin G.2.length => (r.faceId (i, false), r.faceId (i, true)))

/-- Dualization preserves the number of listed edges, including loops and parallel edges. -/
@[simp] theorem dualGraph_length : r.dualGraph.2.length = G.2.length := by
  simp [dualGraph]

/-- Identification of source and dual darts preserves edge positions and endpoint bits. -/
@[expose] def dualDartEquiv : Dart G ≃ Dart r.dualGraph :=
  { toFun := fun (i, b) => (⟨i.val, by simpa only [dualGraph_length] using i.isLt⟩, b)
    invFun := fun (i, b) => (⟨i.val, by simpa only [dualGraph_length] using i.isLt⟩, b)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Dart reversal commutes with the source/dual identification. -/
@[simp] theorem dualDartEquiv_reverse (d : Dart G) :
    r.dualDartEquiv d.reverse = (r.dualDartEquiv d).reverse := rfl

/-- The endpoint of a dual dart is exactly the canonical name of its source face. -/
@[simp] theorem vertex_dualDartEquiv (d : Dart G) :
    (r.dualDartEquiv d).vertex = r.faceId d := by
  rcases d with ⟨i, b⟩
  change (if b then (r.dualGraph.2.getD i.val (0, 0)).2
    else (r.dualGraph.2.getD i.val (0, 0)).1) = r.faceId (i, b)
  have he : r.dualGraph.2.getD i.val (0, 0) =
      (r.faceId (i, false), r.faceId (i, true)) := by
    rw [List.getD_eq_getElem _ _ (by simpa only [dualGraph_length] using i.isLt)]
    simp [dualGraph]
  cases b <;> simp only [he, Bool.false_eq_true, ite_false, ite_true]

/-- Every dual dart endpoint is declared, with no assumption on source endpoint declarations. -/
theorem dual_vertex_mem (d : Dart r.dualGraph) : d.vertex ∈ r.dualGraph.1 := by
  obtain ⟨e, rfl⟩ := r.dualDartEquiv.surjective d
  rw [vertex_dualDartEquiv]
  apply List.mem_dedup.mpr
  exact List.mem_map.mpr ⟨Dart.indexEquiv G e, List.mem_finRange _, by simp⟩

/-- Each declared dual vertex is incident to a dual dart. Source isolated vertices are omitted. -/
theorem dualGraph_no_isolates (v : ℕ) (hv : v ∈ r.dualGraph.1) :
    ∃ d : Dart r.dualGraph, d.vertex = v := by
  obtain ⟨i, -, hi⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
  exact ⟨r.dualDartEquiv ((Dart.indexEquiv G).symm i), by
    rw [vertex_dualDartEquiv]; exact hi⟩

/-- Every endpoint in the dual's flattened incidence list is declared. -/
theorem dualGraph_endpoints_declared :
    ∀ v ∈ r.dualGraph.incidenceVertices, v ∈ r.dualGraph.1 := by
  intro v hv
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  let j : Fin (2 * r.dualGraph.2.length) :=
    ⟨i.val, i.isLt.trans_eq (incidenceVertices_length _)⟩
  have h := r.dual_vertex_mem ((Dart.indexEquiv r.dualGraph).symm j)
  have hj : ((Dart.indexEquiv r.dualGraph).symm j).index = i.val :=
    congrArg Fin.val ((Dart.indexEquiv r.dualGraph).apply_symm_apply j)
  have hi' : r.dualGraph.incidenceVertices[i.val] = v := hi
  rwa [← Dart.vertex_index, hj, List.getD_eq_getElem _ _ i.isLt, hi'] at h

/-- The dual rotation is the source face permutation, transported along the indexed dart
identification. Its cycles are exactly the dual endpoint fibers. -/
@[expose] def dualRotation : RotationSystem r.dualGraph where
  rotate := (r.dualDartEquiv.symm.trans r.faceNext).trans r.dualDartEquiv
  sameCycle_iff d e := by
    obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
    obtain ⟨e, rfl⟩ := r.dualDartEquiv.surjective e
    rw [vertex_dualDartEquiv, vertex_dualDartEquiv, r.faceId_eq_iff]
    apply Equiv.Perm.sameCycle_equiv_iff
    intro d
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

/-- Exact dual vertex successor: `sigma_D = phi`. -/
@[simp] theorem dualRotation_rotate (d : Dart G) :
    r.dualRotation.rotate (r.dualDartEquiv d) = r.dualDartEquiv (r.faceNext d) := by
  simp only [dualRotation, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- Exact dual face successor: `phi_D = alpha sigma alpha` on identified darts. -/
@[simp] theorem dualRotation_faceNext (d : Dart G) :
    r.dualRotation.faceNext (r.dualDartEquiv d) =
      r.dualDartEquiv ((r.rotate d.reverse).reverse) := by
  apply r.dualRotation.rotate.injective
  change r.dualRotation.rotate (r.dualRotation.rotate.symm (r.dualDartEquiv d).reverse) =
    r.dualRotation.rotate (r.dualDartEquiv ((r.rotate d.reverse).reverse))
  rw [Equiv.apply_symm_apply]
  rw [← dualDartEquiv_reverse, dualRotation_rotate]
  congr 1
  change d.reverse = r.rotate.symm (r.rotate d.reverse).reverse.reverse
  simp only [Dart.reverse_reverse, Equiv.symm_apply_apply]

/-- Dual faces are precisely source vertex cycles, with reversal giving the orientation
identification. This includes source degree-one vertices and singleton dual face orbits. -/
theorem dual_sameFace_iff (d e : Dart G) :
    r.dualRotation.faceNext.SameCycle (r.dualDartEquiv d) (r.dualDartEquiv e) ↔
      d.reverse.vertex = e.reverse.vertex := by
  let a : Dart G ≃ Dart r.dualGraph := (Dart.reversal G).trans r.dualDartEquiv
  have hs : Function.Semiconj a r.rotate r.dualRotation.faceNext := by
    intro d
    change r.dualDartEquiv ((r.rotate d).reverse) =
      r.dualRotation.faceNext (r.dualDartEquiv d.reverse)
    rw [dualRotation_faceNext, Dart.reverse_reverse]
  have h := Equiv.Perm.sameCycle_equiv_iff a r.rotate r.dualRotation.faceNext hs
    d.reverse e.reverse
  change r.dualRotation.faceNext.SameCycle
    (r.dualDartEquiv d.reverse.reverse) (r.dualDartEquiv e.reverse.reverse) ↔
      r.rotate.SameCycle d.reverse e.reverse at h
  simpa only [Dart.reverse_reverse, r.sameCycle_iff] using h

/-- Nonempty source endpoint fibers; declared isolated vertices are deliberately absent. -/
abbrev IncidentVertex (G : Graph) := {v : ℕ // ∃ d : Dart G, d.vertex = v}

private def dualFaceVertex : r.dualRotation.Face → IncidentVertex G :=
  Quotient.lift
    (fun d => ⟨(r.dualDartEquiv.symm d).reverse.vertex,
      ⟨(r.dualDartEquiv.symm d).reverse, rfl⟩⟩)
    (by
      intro d e h
      apply Subtype.ext
      obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
      obtain ⟨e, rfl⟩ := r.dualDartEquiv.surjective e
      simpa only [Equiv.symm_apply_apply] using (r.dual_sameFace_iff d e).mp h)

/-- Complete dual-face/source-vertex correspondence. It applies to every nonempty endpoint
fiber, including singleton rotations, with no connectedness or genus assumption. -/
noncomputable def dualFaceVertexEquiv : r.dualRotation.Face ≃ IncidentVertex G :=
  Equiv.ofBijective (dualFaceVertex r) ⟨by
    intro f g
    induction f using Quotient.inductionOn with | _ d =>
      induction g using Quotient.inductionOn with | _ e =>
        intro h
        apply Quotient.sound
        obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
        obtain ⟨e, rfl⟩ := r.dualDartEquiv.surjective e
        apply (r.dual_sameFace_iff d e).mpr
        exact congrArg Subtype.val h,
    by
      rintro ⟨v, d, rfl⟩
      exact ⟨Quotient.mk _ (r.dualDartEquiv d.reverse), by
        apply Subtype.ext
        change (r.dualDartEquiv.symm (r.dualDartEquiv d.reverse)).reverse.vertex = d.vertex
        simp only [Equiv.symm_apply_apply, Dart.reverse_reverse]⟩⟩

/-- The complete dual face count is the number of nonempty source vertex fibers. -/
theorem card_dual_faces : Nat.card r.dualRotation.Face = Nat.card (IncidentVertex G) :=
  Nat.card_congr r.dualFaceVertexEquiv

private def faceDualVertex : r.Face → {v // v ∈ r.dualGraph.1} :=
  Quotient.lift
    (fun d => ⟨r.faceId d, by
      simpa only [vertex_dualDartEquiv] using r.dual_vertex_mem (r.dualDartEquiv d)⟩)
    (by
      intro d e h
      exact Subtype.ext ((r.faceId_eq_iff d e).mpr h))

/-- Canonical names identify every source face with exactly one declared dual vertex. -/
noncomputable def faceDualVertexEquiv : r.Face ≃ {v // v ∈ r.dualGraph.1} :=
  Equiv.ofBijective (faceDualVertex r) ⟨by
    intro f g
    induction f using Quotient.inductionOn with | _ d =>
      induction g using Quotient.inductionOn with | _ e =>
        intro h
        exact Quotient.sound ((r.faceId_eq_iff d e).mp (congrArg Subtype.val h)),
    by
      rintro ⟨v, hv⟩
      obtain ⟨d, hd⟩ := r.dualGraph_no_isolates v hv
      obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
      exact ⟨Quotient.mk _ d, Subtype.ext (by
        change r.faceId d = v
        simpa only [vertex_dualDartEquiv] using hd)⟩⟩

/-- Distinct declared dual names count every source face once. -/
theorem card_dual_vertices : r.dualGraph.distinctVertices.length = Nat.card r.Face := by
  rw [Nat.card_congr r.faceDualVertexEquiv, Nat.card_eq_fintype_card,
    Graph.card_vertexSubtype, Graph.length_distinctVertices]

end Cslib.Complexity.Graph.RotationSystem
