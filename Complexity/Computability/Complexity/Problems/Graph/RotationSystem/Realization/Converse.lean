/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing.FaceColors
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpaceConverse

/-!
# A polygonal realization has numerical genus zero

For an arbitrary listed finite multigraph with declared incident endpoints, an actual
polygonal embedding that literally realizes a clockwise rotation has componentwise
numerical genus zero. The proof constructs colors on the actual face quotient from every
vertex-even indexed edge label and applies the cycle-space converse.

Coordinates are arbitrary complex numbers and segment parameters range over all real
numbers in `[0,1]`. Loops retain their two ends, parallel edges retain their list indices,
and sparse or duplicate declarations, isolates, disconnected graphs and the empty graph
are permitted. There is no degree bound or supplied topological, face-color or genus oracle.

This is an original finite PL proof. It does not establish a topological-source comparison,
taming of arbitrary topological arcs, Hanani–Tutte, a recognition algorithm or a CSP dichotomy.

## Main results

* `Cslib.Complexity.Graph.PolygonalDrawing.IsEmbedding.numericalGenusZero`.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- A genuine finite polygonal embedding with exact literal clockwise realization has
numerical genus zero on every component, including isolated declared vertices. -/
theorem IsEmbedding.numericalGenusZero {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {r : RotationSystem G}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hR : D.Realizes r) :
    r.NumericalGenusZero :=
  r.numericalGenusZero_of_vertexEven_faceBoundary hG
    (fun x hx => hD.exists_faceColors hR hG x hx)

end Cslib.Complexity.Graph.PolygonalDrawing
