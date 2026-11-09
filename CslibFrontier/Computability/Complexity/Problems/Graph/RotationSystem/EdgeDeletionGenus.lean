/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletion
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionParity
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexFibers
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Lifting

/-!
# Numerical Euler bounds in edge deletion

The literal two-end deletion and complete orbit balance give an exact account of faces and
endpoints that become isolated. Face-even labels extend internally across every deletion;
the existing incidence lifting theorem and its algebraic converse then prove componentwise
numerical genus preservation. Splitting bridges, pendant edges, loops, disconnected and point
components require no provider. This is an original numerical argument, not a geometric theorem.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.CycleSurgery

/-- Every endpoint of a retained edge was already declared before deletion. -/
theorem endpoints_declared_deleteLastEdge {G : Graph} {u v : ℕ}
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1) :
    ∀ w ∈ G.incidenceVertices, w ∈ G.1 := by
  intro w hw
  apply hH w
  simp only [lastEdgeGraph, Graph.incidenceVertices, List.flatMap_append, List.mem_append]
  exact Or.inl hw

/-- The actual retained dart map commutes with reversal. -/
theorem retainedLastEdgeDart_reverse (G : Graph) (u v : ℕ) (d : Dart G) :
    retainedLastEdgeDart G u v d.reverse = (retainedLastEdgeDart G u v d).reverse := by
  rcases d with ⟨i, b⟩
  cases b <;> rfl

/-- If no declared vertex loses its last incidence, deletion preserves the actual incident
vertex set. The premise is on endpoint occurrences, rather than an unchecked cardinality. -/
def incidentVertexEquivDeleteLastEdge {G : Graph} {u v : ℕ}
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1)
    (hi : ∀ w ∈ G.1, ∃ d : Dart G, d.vertex = w) :
    IncidentVertex G ≃ IncidentVertex (lastEdgeGraph G u v) where
  toFun w := ⟨w.val, by
    obtain ⟨d, hd⟩ := w.property
    exact ⟨retainedLastEdgeDart G u v d, (vertex_retainedLastEdgeDart G u v d).trans hd⟩⟩
  invFun w := ⟨w.val, by
    obtain ⟨d, hd⟩ := w.property
    exact hi w.val (hd ▸ vertex_mem hH d)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Removing an edge cannot lose more than one face if every vertex retains an incident
dart. The face permutation and both vertex orbit counts are those of the actual rotations. -/
theorem card_faces_deleteLastEdge_le {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v))
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1)
    (hi : ∀ w ∈ G.1, ∃ d : Dart G, d.vertex = w) :
    Nat.card r.Face ≤ Nat.card r.deleteLastEdge.Face + 1 := by
  let e := lastEdgeDartEquiv G u v
  have hc : Nat.card (Quotient (Perm.SameCycle.setoid r.rotate)) =
      Nat.card (Quotient (Perm.SameCycle.setoid r.deleteLastEdge.rotate)) := by
    rw [Nat.card_congr r.rotateOrbitEquiv, Nat.card_congr r.deleteLastEdge.rotateOrbitEquiv]
    exact (Nat.card_congr (incidentVertexEquivDeleteLastEdge hH hi)).symm
  have hb := r.card_faces_deleteLastEdge_balance
  have hs := card_orbits_mul_swap (e.permCongr r.faceNext) (some none) none (by simp)
  have hf := card_orbits_permCongr e r.faceNext
  rw [hc] at hb
  by_cases hh : (e.permCongr r.faceNext).SameCycle (some none) none
  · have h := hs.1 hh
    dsimp only [e] at h hf
    change Nat.card (Quotient (Perm.SameCycle.setoid r.faceNext)) ≤ _
    omega
  · have h := hs.2 hh
    dsimp only [e] at h hf
    change Nat.card (Quotient (Perm.SameCycle.setoid r.faceNext)) ≤ _
    omega

/-- Deleting an arbitrary last indexed edge preserves componentwise numerical genus zero.
The internally constructed face-even extension applies also when the edge splits a component,
creates isolated points, or is a loop. No connectedness or face-location premise is required. -/
theorem numericalGenusZero_deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v))
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1)
    (hr : r.NumericalGenusZero) : r.deleteLastEdge.NumericalGenusZero := by
  have hG := endpoints_declared_deleteLastEdge hH
  apply r.deleteLastEdge.numericalGenusZero_of_faceEven_lifts hG
  intro x hx
  obtain ⟨y, hy, hxy⟩ := r.exists_faceEven_extension_deleteLastEdge x hx
  obtain ⟨spin, hspin⟩ := r.exists_vertexSpins_of_faceEven hH hr y hy
  refine ⟨spin, funext fun i => ?_⟩
  let d : Dart G := (i, false)
  have hs := Graph.edgeGradient_dart (lastEdgeGraph G u v) spin (retainedLastEdgeDart G u v d)
  rw [← retainedLastEdgeDart_reverse, vertex_retainedLastEdgeDart,
    vertex_retainedLastEdgeDart] at hs
  have ht := Graph.edgeGradient_dart G spin d
  exact ht.trans (hs.symm.trans ((congrFun hspin (retainedLastEdgeDart G u v d).1).trans (hxy i)))

/-- If no edges remain, every declared component is a point and uses the existing
conventional face. No dart or connectedness premise is required, including an empty declared
list and duplicate vertex declarations. -/
theorem numericalGenusZero_deleteLastEdge_of_no_edges {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (h : G.2 = []) :
    r.deleteLastEdge.NumericalGenusZero := by
  have hG : ∀ w ∈ G.incidenceVertices, w ∈ G.1 := by
    simp [Graph.incidenceVertices, h]
  apply (r.deleteLastEdge.numericalGenusZero_iff_component_cards hG).mpr
  intro d
  have hn : G.2.length = 0 := by rw [h]; rfl
  exact (Fin.cast hn d.1).elim0

end Cslib.Complexity.Graph.RotationSystem
