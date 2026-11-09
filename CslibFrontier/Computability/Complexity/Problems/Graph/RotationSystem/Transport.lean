/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts
public import CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbits
public import CslibFrontier.Computability.Complexity.Problems.Graph.DartConnectivity

/-!
# Transport of actual indexed rotations

Dart equivalences preserve componentwise numerical genus when they preserve reversal and
the endpoint-fiber partition. Declared isolated points need no invented darts: their numerical
Euler convention is retained separately by the existing predicate. Edge occurrences, loops
and parallel edges remain indexed throughout.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.SelectedOrbits

/-- Reinterpret literally equal listed graphs by retaining their edge indices and end bits. -/
@[expose] def graphEqDartEquiv {G H : Graph} (h : G = H) : Dart G ≃ Dart H :=
  (finCongr (congrArg (fun K : Graph => K.2.length) h)).prodCongr (Equiv.refl Bool)

/-- Equality transport changes no actual endpoint. -/
theorem vertex_graphEqDartEquiv {G H : Graph} (h : G = H) (d : Dart G) :
    (graphEqDartEquiv h d).vertex = d.vertex := by
  cases h
  rfl

/-- Equality transport retains the literal indexed edge position. -/
theorem val_graphEqDartEquiv {G H : Graph} (h : G = H) (d : Dart G) :
    (graphEqDartEquiv h d).1.val = d.1.val := by
  cases h
  rfl

/-- Equality transport retains the original end tag. -/
theorem side_graphEqDartEquiv {G H : Graph} (h : G = H) (d : Dart G) :
    (graphEqDartEquiv h d).2 = d.2 := by
  cases h
  rfl

/-- Equality transport commutes with reversing the indexed edge. -/
theorem reverse_graphEqDartEquiv {G H : Graph} (h : G = H) (d : Dart G) :
    graphEqDartEquiv h d.reverse = (graphEqDartEquiv h d).reverse := by
  cases h
  rfl

/-- Reindex actual darts without changing the vertex-fiber partition. -/
@[expose] def transport {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex) : RotationSystem H where
  rotate := e.permCongr r.rotate
  sameCycle_iff a b := by
    have he := Perm.sameCycle_equiv_iff e r.rotate (e.permCongr r.rotate)
      (by intro d; simp) (e.symm a) (e.symm b)
    simp only [e.apply_symm_apply] at he
    rw [he, r.sameCycle_iff]
    simpa only [e.apply_symm_apply] using (hv (e.symm a) (e.symm b)).symm

/-- Complete reversal orbits are exactly the indexed listed edge occurrences. -/
theorem sameCycle_reversal_iff {G : Graph} (a b : Dart G) :
    (Dart.reversal G).SameCycle a b ↔ a.1 = b.1 := by
  have he : Dart.reversal G = Perm.doubled (1 : Perm (Fin G.2.length)) := by
    apply Equiv.ext
    rintro ⟨i, side⟩
    cases side <;> rfl
  rw [he, Perm.sameCycle_doubled, Perm.sameCycle_one]

open Classical in
/-- Vertex orbits restricted to an actual edge component are its declared vertex set. -/
noncomputable def vertexOrbitEquiv {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    OrbitOn r.rotate (fun a : Dart G => SameComponent G d.vertex a.vertex) ≃
      ↥(G.componentVertexSet d.vertex) :=
  let p := fun a : Dart G => SameComponent G d.vertex a.vertex
  let hp : ∀ a, p (r.rotate a) ↔ p a := fun a => by
    change SameComponent G d.vertex (r.rotate a).vertex ↔ SameComponent G d.vertex a.vertex
    rw [r.vertex_rotate]
  (subtypeOrbitEquiv r.rotate p hp).symm.trans (Equiv.ofBijective
    (Quotient.lift (fun a : {a : Dart G // p a} =>
      (⟨a.val.vertex, (Graph.mem_componentVertexSet_dart _ hG a.val).mpr a.property⟩ :
        ↥(G.componentVertexSet d.vertex))) (by
          intro a b hab
          exact Subtype.ext ((r.sameCycle_iff _ _).mp (Perm.sameCycle_subtypePerm.mp hab))))
    ⟨by
      intro q s hqs
      induction q using Quotient.inductionOn with
      | h a =>
        induction s using Quotient.inductionOn with
        | h b =>
          exact Quotient.sound (Perm.sameCycle_subtypePerm.mpr
            ((r.sameCycle_iff _ _).mpr (congrArg Subtype.val hqs))), by
      intro v
      have hv := (Finset.mem_filter.mp v.property).2
      obtain ⟨a, ha⟩ := Dart.exists_of_sameComponent d v.val hv
      exact ⟨Quotient.mk _ ⟨a, by simpa only [p, ha] using hv⟩, Subtype.ext ha⟩⟩)

open Classical in
/-- Reversal orbits restricted to an actual edge component are its indexed edge set. -/
noncomputable def edgeOrbitEquiv (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    OrbitOn (Dart.reversal G) (fun a : Dart G => SameComponent G d.vertex a.vertex) ≃
      ↥(G.componentEdgeSet d.vertex) :=
  let p := fun a : Dart G => SameComponent G d.vertex a.vertex
  let hp : ∀ a, p (Dart.reversal G a) ↔ p a := fun a =>
    ⟨fun h => h.trans (sameComponent_reverse hG a).symm,
      fun h => h.trans (sameComponent_reverse hG a)⟩
  (subtypeOrbitEquiv (Dart.reversal G) p hp).symm.trans (Equiv.ofBijective
    (Quotient.lift (fun a : {a : Dart G // p a} =>
      (⟨a.val.1, (Graph.mem_componentEdgeSet_iff _ hG _ a.val.2).mpr
        ((Graph.mem_componentVertexSet_dart _ hG a.val).mpr a.property)⟩ :
          ↥(G.componentEdgeSet d.vertex))) (by
            intro a b hab
            exact Subtype.ext ((sameCycle_reversal_iff _ _).mp
              (Perm.sameCycle_subtypePerm.mp hab))))
    ⟨by
      intro q s hqs
      induction q using Quotient.inductionOn with
      | h a =>
        induction s using Quotient.inductionOn with
        | h b =>
          exact Quotient.sound (Perm.sameCycle_subtypePerm.mpr
            ((sameCycle_reversal_iff _ _).mpr (congrArg Subtype.val hqs))), by
      intro i
      have hi := (Graph.mem_componentEdgeSet_iff _ hG i.val false).mp i.property
      have hp' := (Graph.mem_componentVertexSet_dart _ hG (i.val, false)).mp hi
      exact ⟨Quotient.mk _ ⟨(i.val, false), hp'⟩, rfl⟩⟩)

/-- A dart map preserving endpoint identifications and edge reversal maps every existing
edge component into one target component. Injectivity is not required. -/
theorem sameComponent_map_darts {G H : Graph} (e : Dart G → Dart H)
    (hv : ∀ a b, a.vertex = b.vertex → (e a).vertex = (e b).vertex)
    (he : ∀ a, e a.reverse = (e a).reverse)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1) {a b : Dart G}
    (hc : SameComponent G a.vertex b.vertex) : SameComponent H (e a).vertex (e b).vertex := by
  let dst (a : Dart G) := H.induced.connectedComponentMk ⟨(e a).vertex, vertex_mem hH (e a)⟩
  have hvertex (a b : Dart G) (h : a.vertex = b.vertex) : dst a = dst b :=
    congrArg H.induced.connectedComponentMk (Subtype.ext (hv a b h))
  have hedge (a : Dart G) : dst a = dst a.reverse := by
    have h := SimpleGraph.ConnectedComponent.sound (sameComponent_reverse hH (e a)).2.2
    simpa only [dst, he] using h
  have h := Dart.eq_of_sameComponent dst hvertex hedge hc
  exact ⟨vertex_mem hH (e a), vertex_mem hH (e b), SimpleGraph.ConnectedComponent.exact h⟩

/-- Endpoint-fiber and reversal preserving dart coordinates retain exactly the edge components.
There is no injectivity requirement on the natural-number vertex labels themselves. -/
theorem sameComponent_transport_iff {G H : Graph} (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (he : ∀ a, e a.reverse = (e a).reverse)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1) (a b : Dart G) :
    SameComponent H (e a).vertex (e b).vertex ↔ SameComponent G a.vertex b.vertex := by
  constructor
  · intro hc
    have h := sameComponent_map_darts e.symm (fun a b h =>
      (hv (e.symm a) (e.symm b)).mp (by simpa only [e.apply_symm_apply] using h))
      (fun a => by apply e.injective; simp only [he, e.apply_symm_apply]) hG hc
    simpa only [e.symm_apply_apply] using h
  · exact sameComponent_map_darts e (fun a b h => (hv a b).mpr h) he hH

/-- Exact face-successor conjugacy, retaining the inverse-rotation chirality convention. -/
theorem faceNext_transport {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (he : ∀ a, e a.reverse = (e a).reverse) (a : Dart G) :
    e (r.faceNext a) = (r.transport e hv).faceNext (e a) := by
  let s := r.transport e hv
  have hr (a : Dart G) : e (r.rotate a) = s.rotate (e a) := by simp [s, transport]
  change e (r.rotate.symm a.reverse) = s.rotate.symm (e a).reverse
  apply s.rotate.injective
  rw [← hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply, he]

/-- Actual vertex, indexed edge and full face counts agree in each transported edge component. -/
theorem component_cards_transport {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (he : ∀ a, e a.reverse = (e a).reverse)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1) (d : Dart G) :
    (H.componentVertexSet (e d).vertex).card = (G.componentVertexSet d.vertex).card ∧
      (H.componentEdgeSet (e d).vertex).card = (G.componentEdgeSet d.vertex).card ∧
      Nat.card (ComponentFace (r.transport e hv) (e d).vertex) =
        Nat.card (ComponentFace r d.vertex) := by
  let s := r.transport e hv
  let p := fun a : Dart G => SameComponent G d.vertex a.vertex
  let q := fun a : Dart H => SameComponent H (e d).vertex a.vertex
  have hp (a : Dart G) : p a ↔ q (e a) :=
    (sameComponent_transport_iff e hv he hG hH d a).symm
  have hcard (f : Perm (Dart G)) (g : Perm (Dart H)) (hm : ∀ a, e (f a) = g (e a)) :
      Nat.card (OrbitOn f p) = Nat.card (OrbitOn g q) :=
    Nat.card_congr (orbitOnEquiv e f g hm p q hp)
  constructor
  · have h₁ := Nat.card_congr (r.vertexOrbitEquiv hG d)
    have h₂ := Nat.card_congr (s.vertexOrbitEquiv hH (e d))
    simp only [Nat.card_eq_finsetCard] at h₁ h₂
    exact h₂.symm.trans ((hcard r.rotate s.rotate (by intro a; simp [s, transport])).symm.trans h₁)
  constructor
  · have h₁ := Nat.card_congr (edgeOrbitEquiv G hG d)
    have h₂ := Nat.card_congr (edgeOrbitEquiv H hH (e d))
    simp only [Nat.card_eq_finsetCard] at h₁ h₂
    exact h₂.symm.trans ((hcard (Dart.reversal G) (Dart.reversal H) he).symm.trans h₁)
  · exact (hcard r.faceNext s.faceNext (r.faceNext_transport e hv he)).symm

/-- Reindexing actual darts while preserving reversal and vertex fibers preserves the existing
componentwise numerical genus-zero predicate. Arbitrarily many declared point components are
allowed on either graph, because the predicate checks their conventional Euler equation. -/
theorem numericalGenusZero_transport {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (he : ∀ a, e a.reverse = (e a).reverse)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1) (hr : r.NumericalGenusZero) :
    (r.transport e hv).NumericalGenusZero := by
  apply ((r.transport e hv).numericalGenusZero_iff_component_cards hH).mpr
  intro d
  obtain ⟨a, rfl⟩ := e.surjective d
  obtain ⟨hV, hE, hF⟩ := r.component_cards_transport e hv he hG hH a
  have h := (r.numericalGenusZero_iff_component_cards hG).mp hr a
  rw [card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG] at h
  rw [card_componentFaceIndices,
    (r.transport e hv).count_faceRepresentatives_eq_card_componentFace hH, hV, hE, hF]
  exact h

end Cslib.Complexity.Graph.RotationSystem
