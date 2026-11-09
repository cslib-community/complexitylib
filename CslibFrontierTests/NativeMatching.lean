/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Endpoint

/-! Complete graph endpoints on normalized raw inputs, with ordinary-import symbolic clients. -/

-- These commands are executable regressions in a test module.
set_option linter.hashCommand false

open Cslib.Complexity Cslib.Complexity.Graph Turing.MultiTapeTM

namespace NativeMatchingTests

def empty : Graph := ([], [])
def isolates : Graph := ([0, 1], [])
def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])
-- Taking the first edge greedily prevents a perfect matching.
def greedyFailure : Graph := ([0, 1, 2, 3], [(1, 2), (0, 1), (2, 3)])
-- An odd cycle with a stem has a perfect matching using the stem and opposite triangle edge.
def blossom : Graph := ([0, 1, 2, 3], [(0, 1), (1, 2), (2, 0), (0, 3)])
def disconnected : Graph := ([0, 1, 2, 3, 4, 5], [(0, 1), (1, 2), (2, 0), (3, 4)])
def degreeFive : Graph := ([0, 1, 2, 3, 4, 5], [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)])
def raw : Graph := ([0, 0, 1, 2], [(0, 0), (0, 1), (1, 0), (0, 1), (2, 999), (888, 1)])
def sparse : Graph := ([0, 2 ^ 250], [(2 ^ 250, 0)])

#guard empty.maximumMatching == []
#guard empty.perfectMatching == some []
#guard empty.decidePerfectMatching
#guard isolates.maximumMatching == []
#guard !isolates.decidePerfectMatching
#guard isolates.perfectMatching == none
#guard triangle.maximumMatching.length == 1
#guard triangle.perfectMatching == none
#guard !triangle.decidePerfectMatching
#guard greedyFailure.maximumMatching == [(0, 1), (2, 3)]
#guard greedyFailure.perfectMatching == some [(0, 1), (2, 3)]
#guard greedyFailure.decidePerfectMatching
#guard blossom.maximumMatching == [(1, 2), (0, 3)]
#guard blossom.perfectMatching == some [(1, 2), (0, 3)]
#guard blossom.decidePerfectMatching
#guard disconnected.maximumMatching.length == 2
#guard disconnected.perfectMatching == none
#guard degreeFive.maximumMatching.length == 1
#guard degreeFive.perfectMatching == none
#guard raw.maximumMatching == [(0, 1)]
#guard raw.perfectMatching == none
#guard sparse.maximumMatching == [(2 ^ 250, 0)]
#guard sparse.perfectMatching == some [(2 ^ 250, 0)]
#guard sparse.decidePerfectMatching

example : empty.maximumMatching = [] := by decide +kernel

-- A concrete nonbipartite perfect matching makes the abstract model nonvacuous.
example : ∃ M : blossom.induced.Subgraph, M.IsPerfectMatching := by
  refine ⟨ofPositions blossom {1, 3}, isPerfectMatching_ofPositions (by decide +kernel) ?_⟩
  intro v hv
  simp only [blossom, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals
    first
    | refine ⟨1, by decide +kernel, ?_⟩
    | refine ⟨3, by decide +kernel, ?_⟩
  all_goals
    intro i hi
    have his := hi.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at his
    rcases his with rfl | rfl
    all_goals
      first
      | rfl
      | exact False.elim (absurd hi (by decide +kernel))

example (G : Graph) : G.maximumMatchingSubgraph.IsMaximumMatching :=
  maximumMatchingSubgraph_isMaximumMatching G

example (G : Graph) (M : G.induced.Subgraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ G.maximumMatching.length := maximumMatching_cardinality G M hM

example (G : Graph) (u v : {v // v ∈ G.1}) :
    G.maximumMatchingSubgraph.Adj u v ↔
      (u.val, v.val) ∈ G.maximumMatching ∨ (v.val, u.val) ∈ G.maximumMatching :=
  maximumMatchingSubgraph_adj_iff G u v

example (G : Graph) {edges : List (ℕ × ℕ)} (h : G.perfectMatching = some edges) :
    edges = G.maximumMatching ∧ G.maximumMatchingSubgraph.IsPerfectMatching :=
  perfectMatching_spec h

example (G : Graph) : G.decidePerfectMatching = true ↔
    ∃ M : G.induced.Subgraph, M.IsPerfectMatching := decidePerfectMatching_eq_true G

example : ComputableInPolyTime maximumMatching encGraph encMatching :=
  computableInPolyTime_maximumMatching

example : ComputableInPolyTime perfectMatching encGraph (encOption encMatching) :=
  computableInPolyTime_perfectMatching

example : ComputableInPolyTime decidePerfectMatching encGraph encBool :=
  computableInPolyTime_decidePerfectMatching

example : perfectMatchingProblem ∈ P encGraph := perfectMatchingProblem_mem_P

end NativeMatchingTests
