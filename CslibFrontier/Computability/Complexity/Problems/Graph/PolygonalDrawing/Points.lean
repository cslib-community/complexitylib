/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic

/-!
# Polygonal drawings of arbitrary declared point sets

Sparse and repeated declarations of isolated vertices need no extra darts or routes.
Distinct declared names have distinct real-axis positions. This includes the empty graph.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- Draw an arbitrary list of declared isolates at their natural-number real-axis positions.
Repeated occurrences of a name retain the same point. -/
@[expose] def points (vertices : List ℕ) : PolygonalDrawing ⟨vertices, []⟩ where
  vertex := fun v => (v : ℂ)
  route := fun e => Fin.elim0 e
  endpoint_eq := fun e => Fin.elim0 e

/-- All distinct declared isolates are separated, independently of sparsity or repetition. -/
theorem points_isEmbedding (vertices : List ℕ) : (points vertices).IsEmbedding where
  vertices_injective := by
    intro u _ v _ h
    change (u : ℂ) = (v : ℂ) at h
    exact_mod_cast h
  simple := fun e => Fin.elim0 e
  vertex_contacts := fun e => Fin.elim0 e
  edge_contacts := fun e => Fin.elim0 e

/-- Every rotation of an edgeless listed graph is realized by its declared point drawing. -/
theorem points_realizes (vertices : List ℕ) (r : RotationSystem ⟨vertices, []⟩) :
    (points vertices).Realizes r where
  nonzero := fun d => Fin.elim0 d.1
  directions_injective := fun d => Fin.elim0 d.1
  clockwise := fun d => Fin.elim0 d.1

end Cslib.Complexity.Graph.PolygonalDrawing
