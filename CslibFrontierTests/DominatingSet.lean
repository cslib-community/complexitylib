/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.DominatingSet

/-!
# Dominating set: tests

The domination test on small graphs; dominating sets of a path, an isolated vertex and a
self-loop; the reduction from `VertexCover` on concrete graphs, including the vertices of edges, the
dropped self-loops and edges to undeclared vertices, and the target `0` for `k` above the number of
vertices; and the headline results.
-/

namespace ComplexityTests.DominatingSet

open Cslib.Complexity Turing.MultiTapeTM

/-- The path `0 - 1 - 2`. -/
private def path : Graph := ([0, 1, 2], [(0, 1), (1, 2)])

/-- The edge `0 - 1` with the isolated vertex `2`. -/
private def edgeIso : Graph := ([0, 1, 2], [(0, 1)])

/-- A self-loop at `0`, an edge to the undeclared vertex `5`, and a repeated vertex entry. -/
private def junk : Graph := ([0, 0], [(0, 0), (0, 5)])

/-! ### Headline results -/

example : DominatingSet ∈ NP (encPair encGraph encNat) ∧
    NPHard (encPair encGraph encNat) DominatingSet ∧
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) VertexCover
      DominatingSet :=
  ⟨DominatingSet_npComplete.1, DominatingSet_npComplete.2,
    polyTimeReducible_VertexCover_DominatingSet⟩

/-! ### The domination test -/

-- The middle vertex dominates the path; an end vertex does not.
example : DominatingSet.isDominating path [1] = true := by decide
example : DominatingSet.isDominating path [0] = false := by decide

-- An isolated vertex must be chosen: `{0}` misses `2`, and `{0, 2}` dominates.
example : DominatingSet.isDominating edgeIso [0] = false := by decide
example : DominatingSet.isDominating edgeIso [0, 2] = true := by decide

-- A self-loop does not dominate its vertex, and the undeclared vertex `5` needs no domination.
example : DominatingSet.isDominating junk [] = false := by decide
example : DominatingSet.isDominating junk [0] = true := by decide
-- The test reads adjacency off the edge list, so the undeclared `5` passes it. Certificates
-- select declared vertices only (`mem_DominatingSet_iff` asks for `S ⊆ G.1`).
example : DominatingSet.isDominating junk [5] = true := by decide

/-! ### Dominating sets -/

example : (path, 1) ∈ DominatingSet :=
  mem_DominatingSet_iff.2 ⟨{1}, by decide,
    DominatingSet.isDominating_eq_true_iff.1 (by decide), rfl⟩

-- Three vertices dominate the path too, but four distinct declared vertices do not exist.
example : (path, 3) ∈ DominatingSet :=
  mem_DominatingSet_iff.2 ⟨{0, 1, 2}, by decide,
    DominatingSet.isDominating_eq_true_iff.1 (by decide), rfl⟩

example : (path, 4) ∉ DominatingSet := fun h => by
  have := (mem_DominatingSet_iff_exists_card_le.1 h).1
  revert this
  decide

-- The repeated entry counts once.
example : (junk, 1) ∈ DominatingSet :=
  mem_DominatingSet_iff.2 ⟨{0}, by decide,
    DominatingSet.isDominating_eq_true_iff.1 (by decide), rfl⟩

example : (junk, 2) ∉ DominatingSet := fun h => by
  have := (mem_DominatingSet_iff_exists_card_le.1 h).1
  revert this
  decide

/-! ### The reduction from vertex cover -/

-- Only edges between distinct declared vertices are proper.
example : VertexCover.properEdges path = [(0, 1), (1, 2)] := by decide
example : VertexCover.properEdges junk = [] := by decide

-- The graph of `junk`: hub, pendant and copies only.
example : VertexCover.dominationGraph junk = ([1, 3, 0, 0], [(1, 3), (1, 0), (1, 0)]) := by decide

-- The edge `0 - 1` gets the vertex `2 * Nat.pair 0 1 + 5 = 7`, adjacent to the copies `0` and `2`.
example : VertexCover.edgeVertex (0, 1) = 7 := by decide
example : VertexCover.dominationGraph ([0, 1], [(0, 1)]) =
    ([1, 3, 0, 2, 7], [(1, 3), (1, 0), (1, 2), (7, 0), (7, 2)]) := by decide

-- The target becomes `k + 1`, or `0` when `k` exceeds the number of distinct vertices.
example : VertexCover.toDominatingSet (path, 1) = (VertexCover.dominationGraph path, 2) := by
  decide
example : VertexCover.toDominatingSet (junk, 2) = (VertexCover.dominationGraph junk, 0) := by
  decide

-- `{1}` covers the path, so the hub and the copy `2` dominate its graph.
example : VertexCover.toDominatingSet (path, 1) ∈ DominatingSet :=
  (VertexCover.toDominatingSet_mem_iff _).2
    (mem_VertexCover_iff.2 ⟨{1}, by decide, VertexCover.isCover_eq_true_iff.1 (by decide), rfl⟩)

-- The isolated vertex `2` costs nothing: `{0}` covers `edgeIso`, and the hub dominates the copy
-- `4` of `2`.
example : VertexCover.toDominatingSet (edgeIso, 1) ∈ DominatingSet :=
  (VertexCover.toDominatingSet_mem_iff _).2
    (mem_VertexCover_iff.2 ⟨{0}, by decide, VertexCover.isCover_eq_true_iff.1 (by decide), rfl⟩)

-- No vertex cover is empty when there is an edge, so no single vertex (target `0 + 1`) dominates
-- the graph of the path.
example : VertexCover.toDominatingSet (path, 0) ∉ DominatingSet := by
  rw [VertexCover.toDominatingSet_mem_iff, mem_VertexCover_iff]
  rintro ⟨S, -, hS, hcard⟩
  rw [Finset.card_eq_zero] at hcard
  subst hcard
  simpa using hS 0 (by decide) 1 (by decide) (Graph.adjBool_eq_true_iff _ _ _ |>.1 (by decide))

-- `junk` has no vertex cover of `2` distinct vertices, and its target `0` is unsatisfiable,
-- although the graph has a dominating set of at most `2` vertices.
example : VertexCover.toDominatingSet (junk, 2) ∉ DominatingSet := by
  rw [VertexCover.toDominatingSet_mem_iff]
  intro h
  have := (mem_VertexCover_iff_exists_card_le.1 h).1
  revert this
  decide

end ComplexityTests.DominatingSet
