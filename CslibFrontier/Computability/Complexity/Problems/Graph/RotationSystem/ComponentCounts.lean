/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Components
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD

/-!
# Finite sets counted by componentwise numerical Euler

The vertex universe is the set of declared names, edge indices are list positions, and
faces use the existing least-index representative predicate. These finite sets make the
existing certificate counts available to finite-dimensional arguments.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.numericalGenusZero_iff_component_cards`: finite counts.
* `Cslib.Complexity.Graph.RotationSystem.numericalGenusZero_dual_iff`: numerical duality.
-/

public section

namespace Cslib.Complexity.Graph

open Classical in
/-- Distinct declared vertex names in the existing component of `root`. -/
@[expose] noncomputable def componentVertexSet (G : Graph) (root : ℕ) : Finset ℕ :=
  G.1.toFinset.filter fun v => RotationCertificate.SameComponent G root v

open Classical in
/-- Listed edge positions whose first endpoint belongs to `root`'s existing component. -/
@[expose] noncomputable def componentEdgeSet (G : Graph) (root : ℕ) : Finset (Fin G.2.length) :=
  Finset.univ.filter fun i =>
    RotationCertificate.SameComponent G root (Dart.vertex (G := G) (i, false))

/-- Membership for an actual dart reduces to the existing component relation. -/
theorem mem_componentVertexSet_dart {G : Graph} (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    d.vertex ∈ G.componentVertexSet root ↔
      RotationCertificate.SameComponent G root d.vertex := by
  simp only [componentVertexSet, Finset.mem_filter, List.mem_toFinset,
    RotationSystem.vertex_mem hG d, true_and]

/-- Either indexed endpoint identifies the same set of listed component edges. -/
theorem mem_componentEdgeSet_iff {G : Graph} (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (i : Fin G.2.length) (b : Bool) :
    i ∈ G.componentEdgeSet root ↔ (Dart.vertex (G := G) (i, b)) ∈ G.componentVertexSet root := by
  rw [mem_componentVertexSet_dart root hG]
  simp only [componentEdgeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  cases b
  · rfl
  · have h := RotationSystem.sameComponent_reverse hG ((i, false) : Dart G)
    exact ⟨fun hi => hi.trans h, fun hi => hi.trans h.symm⟩

open Classical in
/-- Component vertices are counted by distinct names, independently of duplicate declarations. -/
theorem card_componentVertexSet (G : Graph) (root : ℕ) :
    (G.componentVertexSet root).card = G.distinctVertices.countP
      (fun v => decide (RotationCertificate.SameComponent G root v)) := by
  classical
  have he : G.distinctVertices.toFinset = G.1.toFinset := by
    ext v
    simp only [List.mem_toFinset, mem_distinctVertices]
  rw [componentVertexSet, ← he]
  exact G.nodup_distinctVertices.card_eq_countP

open Classical in
/-- Counting indexed component edges agrees with the existing edge-list occurrence count. -/
theorem card_componentEdgeSet (G : Graph) (root : ℕ) :
    (G.componentEdgeSet root).card = G.2.countP
      (fun edge => decide (RotationCertificate.SameComponent G root edge.1)) := by
  classical
  have h := (List.nodup_finRange G.2.length).card_eq_countP
    (P := fun i => RotationCertificate.SameComponent G root
      (Dart.vertex (G := G) (i, false)))
  rw [List.toFinset_finRange] at h
  rw [componentEdgeSet, h]
  conv_rhs => rw [← List.map_get_finRange G.2]
  simp only [List.countP_map, Function.comp_def, Dart.vertex, edgeEndpoint,
    Bool.false_eq_true, ite_false]
  apply List.countP_congr
  intro i _
  rw [List.getD_eq_getElem _ _ i.isLt]
  rfl

namespace RotationSystem

open Classical in
/-- Exactly one indexed dart per actual face in the chosen edge component. -/
@[expose] noncomputable def componentFaceIndices {G : Graph} (r : RotationSystem G)
    (root : ℕ) : Finset (Fin (2 * G.2.length)) :=
  Finset.univ.filter fun i =>
    RotationCertificate.SameComponent G root ((Dart.indexEquiv G).symm i).vertex ∧
      r.IsFaceRepresentative ((Dart.indexEquiv G).symm i)

open Classical in
/-- The finite face set is precisely the face count in `NumericalGenusZero`. -/
theorem card_componentFaceIndices {G : Graph} (r : RotationSystem G) (root : ℕ) :
    (r.componentFaceIndices root).card =
      ((List.finRange (2 * G.2.length)).countP fun i =>
        decide (RotationCertificate.SameComponent G root ((Dart.indexEquiv G).symm i).vertex ∧
          r.IsFaceRepresentative ((Dart.indexEquiv G).symm i))) := by
  classical
  simpa only [componentFaceIndices, List.toFinset_finRange] using
    (List.nodup_finRange (2 * G.2.length)).card_eq_countP
      (P := fun i => RotationCertificate.SameComponent G root
        ((Dart.indexEquiv G).symm i).vertex ∧
          r.IsFaceRepresentative ((Dart.indexEquiv G).symm i))

open Classical in
/-- Source face representatives and canonical dual vertex names agree in each edge component. -/
noncomputable def componentFaceDualVertexEquiv {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    ↥(r.componentFaceIndices d.vertex) ≃
      ↥(r.dualGraph.componentVertexSet (r.dualDartEquiv d).vertex) :=
  Equiv.ofBijective (fun i => ⟨(i : Fin (2 * G.2.length)).val, by
    let a := (Dart.indexEquiv G).symm i.val
    obtain ⟨hc, hr⟩ := (Finset.mem_filter.mp i.property).2
    have h := (mem_componentVertexSet_dart _ r.dualGraph_endpoints_declared
      (r.dualDartEquiv a)).mpr ((r.sameComponent_dual_iff hG d a).mpr hc)
    have ha : a.index = (i : Fin (2 * G.2.length)).val :=
      congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply i.val)
    rwa [r.vertex_dualDartEquiv a, (r.faceId_eq_index_iff a).mpr hr, ha] at h⟩) ⟨by
    intro i j h
    apply Subtype.ext
    exact Fin.ext (congrArg Subtype.val h), by
    intro v
    have hv := (Finset.mem_filter.mp v.property).1
    obtain ⟨a, ha⟩ := r.dualGraph_no_isolates v.val (List.mem_toFinset.mp hv)
    obtain ⟨a, rfl⟩ := r.dualDartEquiv.surjective a
    have hca : RotationCertificate.SameComponent G d.vertex a.vertex := by
      apply (r.sameComponent_dual_iff hG d a).mp
      apply (mem_componentVertexSet_dart _ r.dualGraph_endpoints_declared _).mp
      simpa only [ha] using v.property
    obtain ⟨b, hb, hab, hrb⟩ := r.faceId_spec a
    have hcb := hca.trans (r.sameComponent_of_sameFace hG hab)
    refine ⟨⟨Dart.indexEquiv G b, ?_⟩, ?_⟩
    · simp only [componentFaceIndices, Finset.mem_filter, Finset.mem_univ,
        Equiv.symm_apply_apply, true_and]
      exact ⟨hcb, hrb⟩
    · apply Subtype.ext
      exact hb.trans (by simpa only [vertex_dualDartEquiv] using ha)⟩

/-- Componentwise face counts equal componentwise declared dual vertex counts. -/
theorem card_component_faces_eq_dual_vertices {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    (r.componentFaceIndices d.vertex).card =
      (r.dualGraph.componentVertexSet (r.dualDartEquiv d).vertex).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (r.componentFaceDualVertexEquiv hG d)

/-- Edge positions in corresponding source and dual components are identified explicitly. -/
@[expose] noncomputable def componentEdgeDualEquiv {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    ↥(G.componentEdgeSet d.vertex) ≃
      ↥(r.dualGraph.componentEdgeSet (r.dualDartEquiv d).vertex) :=
  (finCongr r.dualGraph_length.symm).subtypeEquiv (by
    intro i
    simp only [componentEdgeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (r.sameComponent_dual_iff hG d (i, false)).symm)

/-- Corresponding components retain every listed edge occurrence. -/
theorem card_component_edges_eq_dual {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    (G.componentEdgeSet d.vertex).card =
      (r.dualGraph.componentEdgeSet (r.dualDartEquiv d).vertex).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (r.componentEdgeDualEquiv hG d)

open Classical in
/-- In each edge component, every dual face is exactly one nonempty source vertex fiber.
Declared isolated source points are absent from this dart-indexed correspondence. -/
noncomputable def componentDualFaceVertexEquiv {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    ↥(r.dualRotation.componentFaceIndices (r.dualDartEquiv d).vertex) ≃
      ↥(G.componentVertexSet d.vertex) :=
  Equiv.ofBijective (fun i =>
    let a := (Dart.indexEquiv r.dualGraph).symm i.val
    let b := r.dualDartEquiv.symm a
    ⟨b.reverse.vertex, by
      obtain ⟨hc, -⟩ := (Finset.mem_filter.mp i.property).2
      apply (mem_componentVertexSet_dart _ hG b.reverse).mpr
      have hdb := (r.sameComponent_dual_iff hG d b).mp (by
        simpa only [b, Equiv.apply_symm_apply] using hc)
      exact hdb.trans (sameComponent_reverse hG b)⟩) ⟨by
    intro i j hij
    let a := (Dart.indexEquiv r.dualGraph).symm i.val
    let b := (Dart.indexEquiv r.dualGraph).symm j.val
    have hc : r.dualRotation.faceNext.SameCycle a b := by
      have h := (r.dual_sameFace_iff (r.dualDartEquiv.symm a)
        (r.dualDartEquiv.symm b)).mpr (congrArg Subtype.val hij)
      simpa only [Equiv.apply_symm_apply] using h
    have hi := (Finset.mem_filter.mp i.property).2.2
    have hj := (Finset.mem_filter.mp j.property).2.2
    have hab : a = b := (r.dualRotation.existsUnique_faceRepresentative a).unique
      ⟨.rfl, hi⟩ ⟨hc, hj⟩
    apply Subtype.ext
    exact (Dart.indexEquiv r.dualGraph).symm.injective hab, by
    intro v
    have hv := (Finset.mem_filter.mp v.property).2
    obtain ⟨a, ha⟩ := Dart.exists_of_sameComponent d v.val hv
    let q := r.dualDartEquiv a.reverse
    have hda : RotationCertificate.SameComponent G d.vertex a.vertex := by
      simpa only [ha] using hv
    have hq : RotationCertificate.SameComponent r.dualGraph
        (r.dualDartEquiv d).vertex q.vertex :=
      (r.sameComponent_dual_iff hG d a.reverse).mpr
        (hda.trans (sameComponent_reverse hG a))
    obtain ⟨b, -, hqb, hrb⟩ := r.dualRotation.faceId_spec q
    have hcb := hq.trans (r.dualRotation.sameComponent_of_sameFace
      r.dualGraph_endpoints_declared hqb)
    refine ⟨⟨Dart.indexEquiv r.dualGraph b, ?_⟩, ?_⟩
    · simp only [componentFaceIndices, Finset.mem_filter, Finset.mem_univ,
        Equiv.symm_apply_apply, true_and]
      exact ⟨hcb, hrb⟩
    · apply Subtype.ext
      have h := (r.dual_sameFace_iff a.reverse (r.dualDartEquiv.symm b)).mp (by
        simpa only [q, Equiv.apply_symm_apply] using hqb)
      simp only [Dart.reverse_reverse] at h
      simpa only [Equiv.symm_apply_apply, Dart.reverse_reverse] using h.symm.trans ha⟩

/-- The dual face count in an edge component is its number of distinct source vertices. -/
theorem card_component_dual_faces_eq_vertices {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    (r.dualRotation.componentFaceIndices (r.dualDartEquiv d).vertex).card =
      (G.componentVertexSet d.vertex).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (r.componentDualFaceVertexEquiv hG d)

/-- The existing componentwise numerical predicate is exactly Euler on these finite sets.
Point components retain their original conventional face and impose no dart-index condition. -/
theorem numericalGenusZero_iff_component_cards {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    r.NumericalGenusZero ↔ ∀ d : Dart G,
      (G.componentVertexSet d.vertex).card + (r.componentFaceIndices d.vertex).card =
        (G.componentEdgeSet d.vertex).card + 2 := by
  classical
  constructor
  · intro h d
    have he := h d.vertex (vertex_mem hG d)
    rw [ite_eq_left ⟨d, rfl⟩] at he
    simpa only [card_componentVertexSet, card_componentFaceIndices,
      card_componentEdgeSet] using he
  · intro h root hr
    split_ifs with hi
    · obtain ⟨d, rfl⟩ := hi
      simpa only [card_componentVertexSet, card_componentFaceIndices,
        card_componentEdgeSet] using h d
    · rfl

/-- Actual indexed dualization preserves the existing componentwise numerical genus-zero
predicate. Source point components are dropped, and their conventional Euler equations are
tautologies on the source side. The empty graph is included. No geometric premise is used. -/
theorem numericalGenusZero_dual_iff {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    r.dualRotation.NumericalGenusZero ↔ r.NumericalGenusZero := by
  rw [r.dualRotation.numericalGenusZero_iff_component_cards r.dualGraph_endpoints_declared,
    r.numericalGenusZero_iff_component_cards hG]
  constructor
  · intro h d
    have hd := h (r.dualDartEquiv d)
    rw [r.card_component_dual_faces_eq_vertices hG,
      ← r.card_component_edges_eq_dual hG,
      ← r.card_component_faces_eq_dual_vertices hG] at hd
    omega
  · intro h q
    obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective q
    rw [r.card_component_dual_faces_eq_vertices hG,
      ← r.card_component_edges_eq_dual hG,
      ← r.card_component_faces_eq_dual_vertices hG]
    have := h d
    omega

end RotationSystem
end Cslib.Complexity.Graph
