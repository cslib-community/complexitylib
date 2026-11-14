/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMerge
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CornerContraction
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CornerGenus
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.ContractionGenus

/-!
# Numerical genus zero under a directed vertex split

Splitting a vertex cycle into two contiguous directed blocks preserves componentwise
numerical genus zero. Equivalently, if the existing outgoing merge of two distinct vertex
fibers has genus zero, the original two-fiber rotation does too. A connector contracts to
that exact merge; automatic polygonal restoration gives its genus, and deleting the connector
recovers the original rotation. No cofacial, connectedness or degree hypothesis is needed.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Undoing an outgoing vertex merge preserves numerical genus zero, with the two directed
blocks and every closed or isolated component retained. -/
theorem numericalGenusZero_of_mergeVertices {G : Graph} (r : RotationSystem G)
    (h k : Dart G) (hk : h.vertex ≠ k.vertex)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hr : (r.mergeVertices h k hk).NumericalGenusZero) : r.NumericalGenusZero := by
  have hdecl := cornerGraph_endpoints_declared k h hG
  have hcontract : ((r.insertEdge k h).contractLastEdge hk.symm).NumericalGenusZero := by
    rw [contractLastEdge_insertEdge]
    exact hr
  have he := (r.insertEdge k h).numericalGenusZero_of_contractLastEdge hk.symm hdecl hcontract
  have hd := (r.insertEdge k h).numericalGenusZero_deleteLastEdge hdecl he
  rwa [deleteLastEdge_insertEdge] at hd

end Cslib.Complexity.Graph.RotationSystem
