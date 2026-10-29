/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Drawing
import Mathlib.Data.List.GetD

/-!
# Exact incidence counts of the positive drawing compiler

Positions and routes are counted on the emitted lists. In particular, source placeholders are
absent from the actual vertex list, and splicing never introduces an additional graph edge.

## Main results

* `positiveDrawing_vertexCount`: the exact actual incidence-graph vertex count.
* `positiveDrawing_edgeCount`: one actual route for each actual output literal occurrence.

## References

The finite-profile counting and incidence-indexing proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- Collars and source-boundary extensions preserve every local incidence's clause index. -/
theorem clauseGeometry_incidence_count (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) (j : Fin 22) :
    ((clauseGeometry φ d i c).incidenceRoutes.filter fun e => e.1 == j.val).length =
      ((profileFormula (clauseProfile c)).getD j.val []).length := by
  simpa only [clauseGeometry, collaredPrefixGeometry, profilePrefixGeometry,
    LocalGeometry.toPrefix, List.filter_map, List.length_map, Function.comp_def] using
      profileGeometry_incidence_count (clauseProfile c) j

/-- Every placed actual clause has exactly one route per literal position. -/
theorem positiveClauseBlock_route_count (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {pc : PositivePlacedClause} (hpc : pc ∈ positiveClauseBlock φ d i c) :
    pc.2.2.length = pc.1.length := by
  obtain ⟨⟨cl, j⟩, hj, rfl⟩ := List.mem_map.mp hpc
  have hj' := List.mem_zipIdx_iff_getElem?.mp hj
  have hindex : j < (profileFormula (clauseProfile c)).length :=
    (List.getElem?_eq_some_iff.mp hj').choose
  have hbound := profileFormula_length_le (clauseProfile c)
  have he : (profileFormula (clauseProfile c)).getD j [] = cl := by
    rw [List.getD_eq_getElem?_getD, hj']
    rfl
  simpa only [List.length_map, Clause.length_relabel, he] using
    clauseGeometry_incidence_count φ d i c ⟨j, by omega⟩

/-- Every actual emitted clause has exactly one actual incidence route per literal. -/
theorem positivePlacedClauses_route_count (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {pc : PositivePlacedClause} (hpc : pc ∈ positivePlacedClauses φ d) :
    pc.2.2.length = pc.1.length := by
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hpc
  exact positiveClauseBlock_route_count φ d c.2 c.1 hc

/-- The actual output drawing has exactly one position per actual output graph vertex. -/
theorem positiveDrawing_vertexCount (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveDrawing φ d).1.length =
      (SAT.incidenceGraph (CNF.PositiveExactOneCompile.formula φ)).1.length := by
  have hlen := congrArg List.length (positivePlacedClauses_formula φ d)
  rw [CNF.PositiveExactOneCompile.formula, SAT.incidenceGraph_compact]
  simp only [positiveDrawing, List.length_append, List.length_map,
    SAT.incidenceGraph, List.length_range]
  simpa only [List.length_map] using
    congrArg ((CNF.PositiveExactOneCompile.rawFormula φ).distinctVars.length + ·) hlen

/-- Splicing preserves one route per actual literal occurrence, in the emitted finite lists. -/
theorem positiveDrawing_edgeCount (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveDrawing φ d).2.length =
      (SAT.incidenceGraph (CNF.PositiveExactOneCompile.formula φ)).2.length := by
  rw [CNF.PositiveExactOneCompile.formula, SAT.incidenceGraph_compact,
    SAT.length_edges_incidenceGraph]
  change ((positivePlacedClauses φ d).flatMap fun c => c.2.2).length = _
  rw [← positivePlacedClauses_formula φ d, CNF.length_vars, List.length_flatMap, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pc hpc
  exact positivePlacedClauses_route_count φ d hpc

end Cslib.Complexity.SAT.ExactOne
