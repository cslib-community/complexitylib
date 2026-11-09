/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing.Bouquet

/-!
# Clockwise polygonal realization of loop-only genus-zero rotations

For any finite listed graph whose edges are all loops, declared endpoints and componentwise
numerical genus zero suffice to construct an actual polygonal embedding realizing the exact
given clockwise rotation. The construction uses first-hit ranks and internally derived
nonalternation. There is no matching, drawing, disk, topological or geometric provider premise.

Vertex declarations may repeat, be sparse, or include disconnected isolated names; edges may
repeat the same pair of endpoint names arbitrarily often. The empty graph is included. Each
indexed loop has five actual real affine segments. No degree, coordinate-bit or connectedness
bound is assumed or claimed. This is an original coordinate construction.

This proves only the forward realization for loop-only graphs. It does not restore nonloop
edges after contraction or prove the geometric-to-numerical converse.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.exists_polygonalDrawing_of_loops`: loop-only realization.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Every loop-only numerical-genus-zero rotation has a genuine polygonal embedding
with its exact clockwise germ order. All listed occurrences and both ends of every loop
are retained, without any noncrossing or geometric hypothesis. -/
theorem exists_polygonalDrawing_of_loops {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero)
    (hloop : ∀ e : Fin G.2.length,
      (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) :
    ∃ D : PolygonalDrawing G, D.IsEmbedding ∧ D.Realizes r :=
  ⟨PolygonalDrawing.bouquet r hloop, PolygonalDrawing.bouquet_isEmbedding r hG hr hloop,
    PolygonalDrawing.bouquet_realizes r hloop⟩

end Cslib.Complexity.Graph.RotationSystem
