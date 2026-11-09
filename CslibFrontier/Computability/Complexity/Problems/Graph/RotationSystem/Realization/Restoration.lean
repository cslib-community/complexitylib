/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationOrder

/-!
# Automatic restoration of an arbitrary contracted polygonal embedding

The cut radius, finite circle gaps, split centers, straight fans and connector are
constructed internally from the actual contracted drawing and its literal rotation.
## Main results

* `Cslib.Complexity.Graph.PolygonalDrawing.Realizes.exists_restoration`:
  automatically restore any actual contracted realization, including its exact clockwise order.

-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- Restore an actual arbitrary contracted drawing as a source embedding, choosing
all local geometric data internally, including the exact literal clockwise source rotation. -/
theorem Realizes.exists_restoration {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (hG : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ G.1)
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding)
    (hR : D.Realizes (r.contractLastEdge huv)) :
    ∃ ρ > 0, ∃ a b : ℂ, (D.restoration huv ρ a b).IsEmbedding ∧
      (D.restoration huv ρ a b).Realizes r := by
  have hv : v ∈ G.1 := by
    have h := RotationSystem.vertex_mem hG (lastEdgeDart G u v true)
    have hv : v ∈ (lastEdgeGraph G u v).1 := by
      simpa only [vertex_lastEdgeDart, ↓reduceIte] using h
    exact hv
  have hdecl : v ∈ (contractLastEdgeGraph G u v).1 := by
    have h := List.mem_map_of_mem (f := Function.update id u v) hv
    simpa only [contractLastEdgeGraph, Graph.relabel, Function.update_of_ne huv.symm,
      id_eq] using h
  obtain ⟨ρ, hρ, hpoints, hlocal, hlen⟩ := hD.exists_restriction_radius v hdecl
  have hsimple := hD.outsideRoute_simple v hρ hlen
  have hcut := hD.outsideRoute_ball_contact v hρ hlen hlocal
  obtain ⟨a, ha, b, hb, f, hsep, hpa, hpb, horderU, horderV⟩ :=
    hR.exists_contraction_split r huv hD hρ
  have hnew := hD.restoration huv hρ hpoints hlen hsimple
    (fun e i t ht hz => hcut e i ht hz) ha hb f hsep hpa hpb
  refine ⟨ρ, hρ, a, b, hnew, hR.restoration r huv hD hρ hlen ha hb hnew ?_⟩
  intro side x y hx hy hxy
  cases side
  · simp only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
    exact horderU x y hx hy hxy
  · simp only [vertex_lastEdgeDart, ↓reduceIte] at hx hy ⊢
    exact horderV x y hx hy hxy

end Cslib.Complexity.Graph.PolygonalDrawing
