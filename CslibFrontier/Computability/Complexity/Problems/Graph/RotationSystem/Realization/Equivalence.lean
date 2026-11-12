/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse

/-!
# Numerical genus zero is equivalent to polygonal realization

For a supplied rotation on a listed finite multigraph with declared incident endpoints,
the existing componentwise numerical genus-zero predicate is equivalent to an actual
polygonal embedding realizing its literal clockwise order. Coordinates are arbitrary
complex numbers and contacts quantify over all real segment parameters. Loops, indexed
parallel occurrences, arbitrary degree, disconnected components, repeated declarations,
isolates and empty graphs are included.

This finite PL equivalence does not prove topological taming, a source-model comparison,
Hanani–Tutte, recognition, coordinate-bit or runtime bounds, or a planar CSP dichotomy.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.numericalGenusZero_iff_exists_polygonalDrawing`.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- A supplied rotation has componentwise numerical genus zero exactly when an actual
polygonal embedding realizes its literal clockwise order. -/
theorem numericalGenusZero_iff_exists_polygonalDrawing {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    r.NumericalGenusZero ↔ ∃ D : PolygonalDrawing G, D.IsEmbedding ∧ D.Realizes r := by
  constructor
  · exact r.exists_polygonalDrawing hG
  · rintro ⟨D, hD, hR⟩
    exact hD.numericalGenusZero hG hR

end Cslib.Complexity.Graph.RotationSystem
