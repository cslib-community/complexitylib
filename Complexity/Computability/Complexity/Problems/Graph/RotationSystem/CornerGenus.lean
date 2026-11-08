/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CornerFaces
public import Complexity.Foundations.GroupTheory.Perm.SelectedOrbits
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts

/-!
# Numerical genus under cofacial corner insertion

The numerical Euler argument uses the actual generated rotation and the exact face counts.
The componentwise theorem includes loops, parallel edges, repeated boundary vertices and
coincident corners. Untouched closed components and declared points are retained. The two
selected corners are existing darts; creating an edge at a point is a separate operation.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open RotationCertificate

/-- Every appended edge endpoint is declared if all old endpoints were declared. -/
theorem cornerGraph_endpoints_declared {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    ∀ v ∈ (cornerGraph h k).incidenceVertices, v ∈ (cornerGraph h k).1 := by
  intro v hv
  have he : (cornerGraph h k).incidenceVertices = G.incidenceVertices ++
      [h.vertex, k.vertex] := by simp [cornerGraph, Graph.incidenceVertices]
  rw [he, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hG v hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact vertex_mem hG h
    · exact vertex_mem hG k

/-- Old edge paths remain edge paths after appending the edge. -/
theorem sameComponent_cornerGraph_of_old {G : Graph} (h k : Dart G) {u v : ℕ}
    (hc : SameComponent G u v) : SameComponent (cornerGraph h k) u v := by
  obtain ⟨hu, hv, hp⟩ := hc
  refine ⟨hu, hv, hp.mono ?_⟩
  intro x y hxy
  change G.toSimpleGraph.Adj x.val y.val at hxy
  change (cornerGraph h k).toSimpleGraph.Adj x.val y.val
  rw [Graph.toSimpleGraph_adj] at hxy ⊢
  exact ⟨hxy.1, hxy.2.imp (List.mem_append_left _) (List.mem_append_left _)⟩

/-- Insertion inside one old component preserves precisely all old connected components. -/
theorem sameComponent_cornerGraph_iff {G : Graph} (h k : Dart G)
    (hc : SameComponent G h.vertex k.vertex) (u v : ℕ) :
    SameComponent (cornerGraph h k) u v ↔ SameComponent G u v := by
  constructor
  · obtain ⟨hh, hk, hp⟩ := hc
    have hedge {a b : {w // w ∈ G.1}}
        (hab : (cornerGraph h k).induced.Adj a b) : G.induced.Reachable a b := by
      change (cornerGraph h k).toSimpleGraph.Adj a.val b.val at hab
      rw [Graph.toSimpleGraph_adj] at hab
      rcases hab with ⟨hne, he⟩
      simp only [cornerGraph, List.mem_append, List.mem_singleton] at he
      rcases he with (he | he) | (he | he)
      · exact SimpleGraph.Adj.reachable ((Graph.toSimpleGraph_adj).mpr ⟨hne, Or.inl he⟩)
      · rcases Prod.mk.inj he with ⟨ha, hb⟩
        convert hp using 1 <;> exact Subtype.ext (by assumption)
      · exact SimpleGraph.Adj.reachable ((Graph.toSimpleGraph_adj).mpr ⟨hne, Or.inr he⟩)
      · rcases Prod.mk.inj he with ⟨hb, ha⟩
        convert hp.symm using 1 <;> exact Subtype.ext (by assumption)
    rintro ⟨hu, hv, ⟨path⟩⟩
    refine ⟨hu, hv, ?_⟩
    have liftPath {a b : {w // w ∈ G.1}} (path : (cornerGraph h k).induced.Walk a b) :
        G.induced.Reachable a b := by
      induction path with
      | nil => exact .rfl
      | cons he _ ih => exact (hedge he).trans ih
    exact liftPath path
  · exact sameComponent_cornerGraph_of_old h k

/-- The declared-vertex finite set in every component is literally unchanged. -/
theorem componentVertexSet_cornerGraph {G : Graph} (h k : Dart G)
    (hc : SameComponent G h.vertex k.vertex) (root : ℕ) :
    (cornerGraph h k).componentVertexSet root = G.componentVertexSet root := by
  classical
  simp only [Graph.componentVertexSet, cornerGraph]
  congr 1
  funext v
  exact propext (sameComponent_cornerGraph_iff h k hc root v)

open Classical in
/-- The new edge contributes one indexed occurrence precisely in its selected component. -/
theorem card_componentEdgeSet_cornerGraph {G : Graph} (h k : Dart G)
    (hc : SameComponent G h.vertex k.vertex) (root : ℕ) :
    ((cornerGraph h k).componentEdgeSet root).card = (G.componentEdgeSet root).card +
      if SameComponent G root h.vertex then 1 else 0 := by
  classical
  rw [Graph.card_componentEdgeSet, Graph.card_componentEdgeSet]
  simp only [sameComponent_cornerGraph_iff h k hc]
  change (G.2 ++ [(h.vertex, k.vertex)]).countP
      (fun edge => decide (SameComponent G root edge.1)) = _
  simp

/-- The actual component selection agrees with the old dart selection extended to the two
new edge ends. No injectivity of vertices or boundary labels is used. -/
theorem component_cornerDartEquiv {G : Graph} (h k : Dart G)
    (hc : SameComponent G h.vertex k.vertex) (root : ℕ) (z : Option (Option (Dart G))) :
    SameComponent (cornerGraph h k) root ((cornerDartEquiv h k).symm z).vertex ↔
      Equiv.Perm.SelectedOrbits.extendedPredicate (fun d : Dart G => SameComponent G root d.vertex)
        (SameComponent G root h.vertex) z := by
  rcases z with _ | (_ | d)
  · change SameComponent (cornerGraph h k) root (newCornerDart h k true).vertex ↔ _
    rw [vertex_newCornerDart, sameComponent_cornerGraph_iff h k hc]
    exact ⟨fun h => h.trans hc.symm, fun h => h.trans hc⟩
  · change SameComponent (cornerGraph h k) root (newCornerDart h k false).vertex ↔ _
    rw [vertex_newCornerDart, sameComponent_cornerGraph_iff h k hc]
    rfl
  · change SameComponent (cornerGraph h k) root (oldCornerDart h k d).vertex ↔ _
    rw [vertex_oldCornerDart, sameComponent_cornerGraph_iff h k hc]
    rfl

open Classical in
/-- Exact component face count for cofacial insertion. Only the selected component gains a
face; every other component retains its full face quotient. -/
theorem card_componentFace_insertEdge {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (h k : Dart G)
    (hf : r.faceNext.SameCycle h k) (root : ℕ) :
    Nat.card (ComponentFace (r.insertEdge h k) root) = Nat.card (ComponentFace r root) +
      if SameComponent G root h.vertex then 1 else 0 := by
  classical
  have hc := r.sameComponent_of_sameFace hG hf
  let p := fun d : Dart G => SameComponent G root d.vertex
  let q := Equiv.Perm.SelectedOrbits.extendedPredicate p (p h)
  have hm : ∀ d, cornerDartEquiv h k ((r.insertEdge h k).faceNext d) =
      Equiv.Perm.CycleSurgery.splice r.faceNext h k (cornerDartEquiv h k d) := by
    intro d
    have he := congrArg (fun f => f (cornerDartEquiv h k d)) (r.faceNext_insertEdge h k)
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using he
  have hp : ∀ d : Dart (cornerGraph h k),
      SameComponent (cornerGraph h k) root d.vertex ↔ q (cornerDartEquiv h k d) := by
    intro d
    simpa only [Equiv.symm_apply_apply, q, p] using
      component_cornerDartEquiv h k hc root (cornerDartEquiv h k d)
  have he := Nat.card_congr (Equiv.Perm.SelectedOrbits.orbitOnEquiv (cornerDartEquiv h k)
    (r.insertEdge h k).faceNext (Equiv.Perm.CycleSurgery.splice r.faceNext h k) hm
    (fun d : Dart (cornerGraph h k) => SameComponent (cornerGraph h k) root d.vertex) q hp)
  rw [he]
  exact Equiv.Perm.SelectedOrbits.card_orbitOn_splice r.faceNext p
    (r.component_faceNext_iff hG root) h k
    ⟨fun h => h.trans hc, fun h => h.trans hc.symm⟩ hf

/-- Every new dart vertex is an old dart vertex. This uses occurrence corners, so distinct
visits to a repeated vertex are retained and never require injective boundary labels. -/
theorem exists_oldCornerVertex {G : Graph} (h k : Dart G)
    (d : Dart (cornerGraph h k)) : ∃ a : Dart G, d.vertex = a.vertex := by
  obtain ⟨z, rfl⟩ := (cornerDartEquiv h k).symm.surjective d
  rcases z with _ | (_ | a)
  · exact ⟨k, vertex_newCornerDart h k true⟩
  · exact ⟨h, vertex_newCornerDart h k false⟩
  · exact ⟨a, vertex_oldCornerDart h k a⟩

/-- Insertion at cofacial existing corners preserves componentwise numerical genus zero.
Disconnected closed components and declared point components remain in the same predicate;
there is no connectedness, distinct-vertex or distinct-corner hypothesis. -/
theorem numericalGenusZero_insertEdge {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero)
    (h k : Dart G) (hf : r.faceNext.SameCycle h k) :
    (r.insertEdge h k).NumericalGenusZero := by
  classical
  have hG' := cornerGraph_endpoints_declared h k hG
  have hc := r.sameComponent_of_sameFace hG hf
  apply ((r.insertEdge h k).numericalGenusZero_iff_component_cards hG').mpr
  intro d
  obtain ⟨a, ha⟩ := exists_oldCornerVertex h k d
  rw [ha]
  have he := (r.numericalGenusZero_iff_component_cards hG).mp hr a
  rw [card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG] at he
  rw [card_componentFaceIndices,
    (r.insertEdge h k).count_faceRepresentatives_eq_card_componentFace hG',
    componentVertexSet_cornerGraph h k hc, card_componentEdgeSet_cornerGraph h k hc,
    card_componentFace_insertEdge r hG h k hf]
  omega

end Cslib.Complexity.Graph.RotationSystem
