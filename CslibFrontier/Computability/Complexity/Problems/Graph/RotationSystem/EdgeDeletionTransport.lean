/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletion
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus

/-!
# Edge deletion between explicit positional transports

A literal view of the source as a prefix plus its last edge allows deletion, followed by
endpoint-fiber and reversal preserving reindexing into an actual target graph. All numerical
genus obligations are discharged internally by deletion and transport. Keeping the graph
parameters abstract avoids elaborating concrete dense-name construction programs inside
the general surgery proof.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- A source equality, last-edge deletion and explicit target dart map preserve numerical
genus. Neither endpoint name injection nor a connectedness/cofaciality hypothesis is needed.
Endpoint declaration is required only on the actual source and actual target graphs. -/
theorem numericalGenusZero_deleteLastEdge_transport {S G T : Graph} {u v : ℕ}
    (r : RotationSystem S) (h : S = lastEdgeGraph G u v) (e : Dart G ≃ Dart T)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (he : ∀ a, e a.reverse = (e a).reverse)
    (hS : ∀ w ∈ S.incidenceVertices, w ∈ S.1)
    (hT : ∀ w ∈ T.incidenceVertices, w ∈ T.1) (hr : r.NumericalGenusZero) :
    (((r.transport (graphEqDartEquiv h)
      (by intro a b; rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])).deleteLastEdge
        (G := G) (u := u) (v := v)).transport e hv).NumericalGenusZero := by
  cases h
  exact r.deleteLastEdge.numericalGenusZero_transport (H := T) e hv he
    (endpoints_declared_deleteLastEdge hS) hT (r.numericalGenusZero_deleteLastEdge hS hr)

end Cslib.Complexity.Graph.RotationSystem
