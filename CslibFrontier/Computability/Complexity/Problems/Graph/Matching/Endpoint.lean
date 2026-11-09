/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Correctness
public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.PolyTime

/-!
# Native polynomial-time unweighted perfect and maximum matching

Import this module for graph-only executable search, correctness against the existing Mathlib
`Graph.induced.Subgraph` model, ordinary native polynomial-time certificates on complete framed
binary graph inputs, and the perfect-matching P corollary.

`Graph.maximumMatching` returns actual selected original edge pairs; its cardinality is at least
that of every actual matching. `Graph.perfectMatching` returns those pairs exactly when a perfect
matching exists. `Graph.maximumMatchingPositions` provides canonical original edge positions and
`Graph.edgesAtPositions` their executable conversion. The empty graph returns the empty perfect
matching; isolates are admitted and left unmatched by maximum search. Loops, undeclared endpoints,
parallel/reversed edges and duplicate vertex declarations follow the existing induced simple graph.

This specializes the constructive minimum-defect even-delta-matroid solver of
[KazdaKolmogorovRolinek2018]. It supplies an unweighted matching corollary; weighted/min-cost
matching and a tight classical cubic operation bound are separate questions.
-/

public section

namespace Cslib.Complexity.Graph

/-- Perfect matching on the existing finite induced graph, for every raw framed graph input. -/
@[expose] def perfectMatchingProblem : Set Graph :=
  {G | ∃ M : G.induced.Subgraph, M.IsPerfectMatching}

/-- Perfect-matching decision belongs to native P on complete framed binary graph inputs. -/
theorem perfectMatchingProblem_mem_P : perfectMatchingProblem ∈ P encGraph :=
  ⟨decidePerfectMatching, computableInPolyTime_decidePerfectMatching,
    fun G => (decidePerfectMatching_eq_true G).symm⟩

end Cslib.Complexity.Graph
