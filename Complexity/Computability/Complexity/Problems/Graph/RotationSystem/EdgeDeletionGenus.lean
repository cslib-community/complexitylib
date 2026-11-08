/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletion
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Transport
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.VertexFibers
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.ConnectedEuler
import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Lifting

/-!
# Numerical Euler bounds in edge deletion

The literal two-end deletion and complete orbit balance give a face-count lower bound when
every declared vertex retains an incidence. The matrix Euler bound supplies the opposite
inequality for a connected retained graph. This is an original numerical argument; no
geometric planarity theorem is used. The connected result requires a retained dart and does
not cover deletion that splits a component or leaves only points.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate CycleSplice

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
def incidentVertexEquiv_deleteLastEdge {G : Graph} {u v : ℕ}
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
    exact (Nat.card_congr (incidentVertexEquiv_deleteLastEdge hH hi)).symm
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

private theorem connected_euler_le {G : Graph} (r : RotationSystem G)
    (hG : ∀ w ∈ G.incidenceVertices, w ∈ G.1)
    (hc : ∀ a ∈ G.1, ∀ b ∈ G.1, SameComponent G a b) (d : Dart G) :
    G.1.toFinset.card + Nat.card r.Face ≤ G.2.length + 2 := by
  classical
  have hv : G.componentVertexSet d.vertex = G.1.toFinset := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact hc _ (vertex_mem hG d) _ (List.mem_toFinset.mp hv)
  have he : G.componentEdgeSet d.vertex = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact hc _ (vertex_mem hG d) _ (vertex_mem hG (i, false))
  have hf : (r.componentFaceIndices d.vertex).card = Nat.card r.Face := by
    rw [card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG]
    exact Nat.card_congr (r.connectedFaceEquiv hG hc d)
  simpa only [hv, he, hf, Finset.card_univ, Fintype.card_fin] using r.component_euler_le hG d

/-- Deleting the last edge of a numerically genus-zero rotation preserves numerical genus
zero when the retained declared graph is connected and has an actual dart. Cofaciality is
derived from the literal face count and the universal matrix Euler bound, not assumed. The
separate point convention and splitting deletions require their own component accounting. -/
theorem numericalGenusZero_deleteLastEdge_of_connected {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v))
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1)
    (hr : r.NumericalGenusZero)
    (hc : ∀ a ∈ G.1, ∀ b ∈ G.1, SameComponent G a b) (d : Dart G) :
    r.deleteLastEdge.NumericalGenusZero := by
  classical
  have hG := endpoints_declared_deleteLastEdge hH
  have hi (w : ℕ) (hw : w ∈ G.1) : ∃ a : Dart G, a.vertex = w :=
    Dart.exists_of_sameComponent d w (hc _ (vertex_mem hG d) _ hw)
  have hconn : ∀ a ∈ (lastEdgeGraph G u v).1,
      ∀ b ∈ (lastEdgeGraph G u v).1, SameComponent (lastEdgeGraph G u v) a b := by
    intro a ha b hb
    obtain ⟨p, hp⟩ := hi a ha
    obtain ⟨q, hq⟩ := hi b hb
    have hh := sameComponent_map_darts (retainedLastEdgeDart G u v)
      (fun p q he => by simp only [vertex_retainedLastEdgeDart, he])
      (retainedLastEdgeDart_reverse G u v) hH (hc _ (vertex_mem hG p) _ (vertex_mem hG q))
    simpa only [vertex_retainedLastEdgeDart, hp, hq] using hh
  have hold := (r.numericalGenusZero_iff_connected_euler hH hconn
    (retainedLastEdgeDart G u v d)).mp hr
  have hlo := r.card_faces_deleteLastEdge_le hH hi
  have hhi := connected_euler_le r.deleteLastEdge hG hc d
  apply (r.deleteLastEdge.numericalGenusZero_iff_connected_euler hG hc d).mpr
  change G.1.toFinset.card + Nat.card r.Face = _ at hold
  rw [show (lastEdgeGraph G u v).2.length = G.2.length + 1 by simp [lastEdgeGraph]] at hold
  omega

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
