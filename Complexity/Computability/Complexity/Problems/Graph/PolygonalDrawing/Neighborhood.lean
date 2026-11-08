/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import Complexity.Foundations.Geometry.Polygonal.Neighborhood

/-!
# Local segment neighborhoods of polygonal graph embeddings

Every declared vertex of a polygonal embedding has a positive-radius ball meeting only
first or last segments actually incident to that vertex. The finite neighborhood is
constructed from the segment arrangement. Both ends of a loop are retained.

This proves a local straight-segment fact; it does not assume or establish a vertex-split
patch, an isotopy theorem, Jordan separation or the numerical-genus bridge.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- Near a declared vertex, every segment met by an embedding is an actual first or last
segment at that named vertex. The radius is proved to exist from finite real geometry. -/
theorem IsEmbedding.exists_vertex_ball {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.1) :
    ∃ ε > 0, ∀ e (i : Fin (D.route e).segments) w,
      w ∈ Metric.ball (D.vertex v) ε →
      w ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
        (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v) := by
  let ι := (e : Fin G.2.length) × Fin (D.route e).segments
  obtain ⟨ε, hε, hball⟩ := Polygonal.exists_ball_only_incident_segments
    (fun p : ι => (D.route p.1).point p.2.castSucc)
    (fun p : ι => (D.route p.1).point p.2.succ) (D.vertex v)
  refine ⟨ε, hε, fun e i w hw hseg => ?_⟩
  have hcenter := hball ⟨e, i⟩ w hw hseg
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨t, ht, heq⟩ := hcenter
  obtain ⟨b, hb, hvertex⟩ := hD.vertex_contacts e i t ht v hv heq
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi1 : (i.val : ℝ) + 1 ≤ (D.route e).segments := by exact_mod_cast i.isLt
  cases b
  · left
    refine ⟨?_, hvertex⟩
    have hi : (i.val : ℝ) = 0 := by
      dsimp [Polygonal.Route.AtEnd, Polygonal.Route.position] at hb
      linarith [ht.1]
    exact_mod_cast hi
  · right
    refine ⟨?_, hvertex⟩
    have hi : (i.val : ℝ) + 1 = (D.route e).segments := by
      dsimp [Polygonal.Route.AtEnd, Polygonal.Route.position] at hb
      linarith [ht.2]
    exact_mod_cast hi

end Cslib.Complexity.Graph.PolygonalDrawing
