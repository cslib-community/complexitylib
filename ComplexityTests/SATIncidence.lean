/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Incidence
import Complexity.Computability.Complexity.Problems.Graph.OrthogonalLayout

/-! Concrete incidence records, including parallel literal incidences and isolated clauses. -/

namespace ComplexityTests.SATIncidence

open Cslib.Complexity Cslib.Logic.PL

-- Vertex names depend on the number of distinct variables, not their numeric magnitudes.
example : SAT.incidenceGraph
    ([[(17, true), (17, false)], [], [(100000000000000000000, false)]] : CNF ℕ) =
    ([0, 1, 2, 3, 4], [(0, 2), (0, 2), (1, 4)]) := by decide

-- An empty clause remains an isolated clause vertex. Repeated clauses have distinct vertices.
example : SAT.incidenceGraph ([[], []] : CNF ℕ) = ([0, 1], []) := by decide

example : SAT.incidenceGraph ([] : CNF ℕ) = ([], []) := by decide

-- The construction works for ordinary finite variable types too.
example : SAT.incidenceGraph ([[(true, false)], [(false, true)]] : CNF Bool) =
    ([0, 1, 2, 3], [(0, 2), (1, 3)]) := by decide

-- One actual width/occurrence-bounded formula exercises canonical degree-three ports.
private def boundedFormula : CNF ℕ :=
  [[(0, true), (1, false)], [(0, false), (1, true), (2, true)], [(0, true), (2, false)]]

private def boundedGraph : Graph := SAT.incidenceGraph boundedFormula

example : boundedGraph =
    ([0, 1, 2, 3, 4, 5], [(0, 3), (1, 3), (0, 4), (1, 4), (2, 4), (0, 5), (2, 5)]) := by decide

private theorem bounded_degree : ∀ v, boundedGraph.incidenceVertices.count v ≤ 3 := by
  intro v
  by_cases hv : v ∈ boundedGraph.incidenceVertices
  · have hvle : v ≤ 5 := by
      change v ∈ [0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
    have hcases : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [List.count_eq_zero.mpr hv]
    decide

example : boundedGraph.canonicalPorts =
    [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (1, 1)] := by decide

example : (boundedGraph.orthogonalRoutes boundedGraph.canonicalPorts).getD 0 [] =
    [(4, 4), (2, 4), (2, 50), (26, 50), (26, 28), (28, 28)] := by decide

example : Graph.portAt boundedGraph.canonicalPorts 0 false ≠
    Graph.portAt boundedGraph.canonicalPorts 2 false := by
  have h := Graph.canonical_index_port_ne boundedGraph
    (fun _ => SAT.incidenceGraph_endpoints) bounded_degree
    (by decide : 0 < boundedGraph.2.length) (by decide : 2 < boundedGraph.2.length)
    (by decide) false false
  exact fun hp => h (Prod.ext (by decide) hp)

end ComplexityTests.SATIncidence
