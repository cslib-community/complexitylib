/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContractionGenus
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse

/-!
# Numerical genus zero before and after nonloop contraction

Automatic polygonal restoration proves the reverse of numerical genus preservation for
the existing literal nonloop contraction. The conclusion concerns the original rotation,
including its clockwise order. No drawing, local split or genus provider is an input.
Geometry is used only in the proof; neither geometric coordinates nor a search enter the
finite rotation or its certificate.

This topic is separate from `EdgeContractionGenus`: the forward polygonal theorem imports
the one-way contraction theorem, so placing the converse there would create an import cycle.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Reopening a contracted nonloop edge preserves numerical genus zero, with the original
two cyclic vertex blocks and connector recovered by automatic polygonal restoration. -/
theorem numericalGenusZero_of_contractLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (hG : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ G.1)
    (hr : (r.contractLastEdge huv).NumericalGenusZero) : r.NumericalGenusZero := by
  obtain ⟨D, hD, hR⟩ := (r.contractLastEdge huv).exists_polygonalDrawing
    (endpoints_declared_contractLastEdge hG) hr
  obtain ⟨ρ, _, a, b, hEmb, hReal⟩ := hR.exists_restoration r huv hG hD
  exact hEmb.numericalGenusZero hG hReal

/-- Componentwise numerical genus zero is invariant under the existing directed nonloop
contraction, including loops elsewhere, parallel edges, closed components and isolates. -/
theorem numericalGenusZero_contractLastEdge_iff {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (hG : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ G.1) :
    (r.contractLastEdge huv).NumericalGenusZero ↔ r.NumericalGenusZero :=
  ⟨r.numericalGenusZero_of_contractLastEdge huv hG,
    r.numericalGenusZero_contractLastEdge huv hG⟩

end Cslib.Complexity.Graph.RotationSystem
