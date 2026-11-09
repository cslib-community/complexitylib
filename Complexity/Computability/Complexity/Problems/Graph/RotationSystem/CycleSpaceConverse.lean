/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpace

/-!
# A cycle-space criterion for numerical genus zero

If every vertex-even Boolean edge label is the boundary of colors on the actual face
quotient, the rotation is componentwise numerically genus zero. The proof applies the
face-even lifting converse to the actual indexed dual and transports the edge labels back.
It retains loops, parallel occurrences, disconnected components, sparse or duplicate vertex
declarations, isolated points and the empty graph.

This is an original finite algebraic argument. The criterion is not a geometric converse:
constructing these colors from a polygonal embedding is a separate obligation.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.numericalGenusZero_of_vertexEven_faceBoundary`:
  the cycle-space criterion, with no genus assumption.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Exactness of vertex-even labels as boundaries of actual face colors forces numerical
genus zero. No connectedness, degree or nonloop assumption is needed. This algebraic
criterion does not by itself construct colors from a geometric drawing. -/
theorem numericalGenusZero_of_vertexEven_faceBoundary {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hcolor : ∀ x : Fin G.2.length → Bool, G.VertexEven x →
      ∃ q : r.Face → Bool, r.faceBoundary q = x) : r.NumericalGenusZero := by
  apply (r.numericalGenusZero_dual_iff hG).mp
  apply r.dualRotation.numericalGenusZero_of_faceEven_lifts r.dualGraph_endpoints_declared
  intro y hy
  let x (i : Fin G.2.length) : Bool := y (Fin.cast r.dualGraph_length.symm i)
  have hxy : (fun i => x (Fin.cast r.dualGraph_length i)) = y :=
    funext fun _ => congrArg y (Fin.ext rfl)
  have hx : G.VertexEven x := by
    apply (r.vertexEven_iff_dual_faceEven x).mpr
    simpa only [hxy] using hy
  obtain ⟨q, hq⟩ := hcolor x hx
  obtain ⟨spin, hs⟩ := r.dual_edgeGradient_faceColors q
  refine ⟨spin, ?_⟩
  simpa only [hq, hxy] using hs

end Cslib.Complexity.Graph.RotationSystem
