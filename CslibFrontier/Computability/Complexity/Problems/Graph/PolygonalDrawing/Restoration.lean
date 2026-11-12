/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationEdges

/-!
# Embedding of the actual graph after nonloop restoration

The actual retained routes and selected connector satisfy every continuous embedding
condition. The radius and split geometry are derived internally in the realization API.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- Each source edge occurrence is retained or is the selected final occurrence. -/
theorem restoration_edge_cases (G : Graph) (u v : ℕ)
    (e : Fin (lastEdgeGraph G u v).2.length) :
    (∃ j : Fin G.2.length, e = (retainedLastEdgeDart G u v (j, false)).1) ∨
      e = (lastEdgeDart G u v false).1 := by
  by_cases he : e.val < G.2.length
  · exact Or.inl ⟨⟨e.val, he⟩, Fin.ext rfl⟩
  · right
    apply Fin.ext
    change e.val = G.2.length
    have hi := e.isLt
    simp only [lastEdgeGraph, List.length_append, List.length_singleton] at hi
    omega

/-- An actual retained source edge keeps its original named endpoints. -/
theorem vertex_restoration_retained (G : Graph) (u v : ℕ) (e : Fin G.2.length) (side : Bool) :
    Dart.vertex (G := lastEdgeGraph G u v)
      ((retainedLastEdgeDart G u v (e, false)).1, side) = Dart.vertex (G := G) (e, side) := by
  have h : ((retainedLastEdgeDart G u v (e, false)).1, side) =
      retainedLastEdgeDart G u v (e, side) := by cases side <;> rfl
  rw [h, vertex_retainedLastEdgeDart]

/-- The actual selected source edge has its original ordered named endpoints. -/
theorem vertex_restoration_last (G : Graph) (u v : ℕ) (side : Bool) :
    Dart.vertex (G := lastEdgeGraph G u v) ((lastEdgeDart G u v false).1, side) =
      if side then v else u := by
  have h : ((lastEdgeDart G u v false).1, side) = lastEdgeDart G u v side := by
    cases side <;> rfl
  rw [h, vertex_lastEdgeDart]

/-- The actual retained route of the restoration is its two-end attachment constructor. -/
theorem route_restoration_retained {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (e : Fin G.2.length) :
    (D.restoration huv ρ a b).route (retainedLastEdgeDart G u v (e, false)).1 =
      D.restoredRoute ρ a b e := by
  change (if h : e.val < G.2.length then D.restoredRoute ρ a b ⟨e.val, h⟩ else _) = _
  rw [dite_eq_left e.isLt]

/-- The actual selected route is the oriented single-segment connector. -/
theorem route_restoration_last {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) :
    (D.restoration huv ρ a b).route (lastEdgeDart G u v false).1 = Route.line a b := by
  change (if h : G.2.length < G.2.length then D.restoredRoute ρ a b ⟨G.2.length, h⟩ else _) = _
  rw [dite_eq_right (Nat.lt_irrefl _)]

/-- The restored actual drawing is an embedding. Every continuous contact condition is
proved for its real segments; no abstract patch or assumed target embedding is substituted. -/
theorem IsEmbedding.restoration {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding) (huv : u ≠ v)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hpoints : ∀ w ∈ (contractLastEdgeGraph G u v).1,
      D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v)
    (hlen : ∀ d : Dart (contractLastEdgeGraph G u v), d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (hsimple : ∀ e, (D.outsideRoute v ρ e).IsSimple)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (f : ℂ →ᵃ[ℝ] ℝ) (hsep : f b < f a)
    (hpa : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = u → f a < f (D.cutPort ρ d.val))
    (hpb : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = v → f (D.cutPort ρ d.val) < f b) :
    (D.restoration huv ρ a b).IsEmbedding := by
  have hab : a ≠ b := fun h => (ne_of_lt hsep) (congrArg f h.symm)
  refine ⟨hD.restoredVertex_injective huv hpoints ha hb hab, ?_, ?_, ?_⟩
  · intro e
    rcases restoration_edge_cases G u v e with ⟨j, rfl⟩ | rfl
    · rw [D.route_restoration_retained]
      exact hD.restoredRoute_simple huv hρ hsimple hcut ha hb f hsep hpa hpb j
    · rw [D.route_restoration_last]
      exact Route.isSimple_line hab
  · intro e
    rcases restoration_edge_cases G u v e with ⟨j, rfl⟩ | rfl
    · rw [D.route_restoration_retained huv ρ a b j]
      intro i t ht w hw heq
      obtain ⟨side, hat, hv⟩ := hD.restoredRoute_vertex_contacts huv hρ hpoints hlen hcut
        ha hb f hsep hpa hpb j i ht w hw heq
      exact ⟨side, hat, (vertex_restoration_retained G u v j side).trans hv⟩
    · rw [D.route_restoration_last huv ρ a b]
      intro i t ht w hw heq
      obtain ⟨side, hat, hv⟩ := D.connector_vertex_contacts huv hpoints ha hb hab i ht w hw heq
      exact ⟨side, hat, (vertex_restoration_last G u v side).trans hv⟩
  · intro e g heg
    rcases restoration_edge_cases G u v e with ⟨e, rfl⟩ | rfl
    · rcases restoration_edge_cases G u v g with ⟨g, rfl⟩ | rfl
      · rw [D.route_restoration_retained huv ρ a b e, D.route_restoration_retained huv ρ a b g]
        intro i j s t hs ht heq
        have hne : e ≠ g := fun h => heg (congrArg
          (fun e => (retainedLastEdgeDart G u v (e, false)).1) h)
        obtain ⟨side, tag, hat, hgat, hv⟩ := hD.restoredRoute_edge_contacts huv hρ hlen hcut
          ha hb f hsep hpa hpb e g hne i j hs ht heq
        exact ⟨side, tag, hat, hgat, (vertex_restoration_retained G u v e side).trans
          (hv.trans (vertex_restoration_retained G u v g tag).symm)⟩
      · rw [D.route_restoration_retained huv ρ a b e, D.route_restoration_last huv ρ a b]
        intro i j s t hs ht heq
        obtain ⟨side, tag, hat, hgat, hv⟩ := hD.restoredRoute_connector_contacts huv hρ hcut
          ha hb f hsep hpa hpb e i j hs ht heq
        exact ⟨side, tag, hat, hgat, (vertex_restoration_retained G u v e side).trans
          (hv.trans (vertex_restoration_last G u v tag).symm)⟩
    · rcases restoration_edge_cases G u v g with ⟨g, rfl⟩ | rfl
      · rw [D.route_restoration_last huv ρ a b, D.route_restoration_retained huv ρ a b g]
        intro i j s t hs ht heq
        obtain ⟨tag, side, hgat, hat, hv⟩ := hD.restoredRoute_connector_contacts huv hρ hcut
          ha hb f hsep hpa hpb g j i ht hs heq.symm
        exact ⟨side, tag, hat, hgat, (vertex_restoration_last G u v side).trans
          (hv.symm.trans (vertex_restoration_retained G u v g tag).symm)⟩
      · exact False.elim (heg rfl)

end Cslib.Complexity.Graph.PolygonalDrawing
