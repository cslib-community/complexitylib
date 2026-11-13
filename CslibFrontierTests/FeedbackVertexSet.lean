/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.FeedbackVertexSet

/-!
# Feedback vertex set: tests

Directed cycles and acyclicity on small graphs, feedback vertex sets of a directed triangle, a
self-loop and an acyclic graph, arcs to undeclared vertices, Karp's reduction from `VertexCover`,
and the headline results.
-/

namespace CslibFrontierTests.FeedbackVertexSet

open Cslib.Complexity Turing.MultiTapeTM

/-- The directed triangle `0 → 1 → 2 → 0`. -/
private def tri : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩

/-- A self-loop at `0`. -/
private def loop : Graph := ⟨[0], [(0, 0)]⟩

/-- An acyclic graph with arcs `0 → 1 → 2` and `0 → 2`. -/
private def dag : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (0, 2)]⟩

/-! ### Headline results -/

example : FeedbackVertexSet ∈ NP encFeedbackVertexSet ∧
    NPHard encFeedbackVertexSet FeedbackVertexSet ∧
    PolyTimeReducible encVertexCoverInstance encFeedbackVertexSet VertexCover
      FeedbackVertexSet :=
  ⟨FeedbackVertexSet_npComplete.1, FeedbackVertexSet_npComplete.2,
    polyTimeReducible_VertexCover_FeedbackVertexSet⟩

example : ComputableInPolyTime (fun x : FeedbackVertexSetInstance => x.graph)
    encFeedbackVertexSet encGraph := by
  fun_prop

example : ComputableInPolyTime (fun x : FeedbackVertexSetInstance => x.bound)
    encFeedbackVertexSet encNat := by
  fun_prop

example : ComputableInPolyTime (fun p : Graph × ℕ => (⟨p.1, p.2⟩ : FeedbackVertexSetInstance))
    (encPair encGraph encNat) encFeedbackVertexSet := by
  fun_prop

example : (default : FeedbackVertexSetInstance) = ⟨default, default⟩ := rfl

/-! ### Directed cycles -/

-- The triangle is a directed cycle, read cyclically from any vertex.
example : tri.IsDirCycle [0, 1, 2] := by
  refine ⟨by simp, by decide, by decide, ?_⟩
  rw [Cycle.chain_coe_cons]
  decide

example : tri.IsDirCycle [1, 2, 0] := by
  refine ⟨by simp, by decide, by decide, ?_⟩
  rw [Cycle.chain_coe_cons]
  decide

-- Read in the wrong direction, it is not.
example : ¬tri.IsDirCycle [0, 2, 1] := by
  rintro ⟨-, -, -, h⟩
  rw [Cycle.chain_coe_cons] at h
  revert h
  decide

-- A self-loop is a cycle of length one.
example : loop.IsDirCycle [0] :=
  ⟨by simp, by simp, by decide, by rw [Cycle.chain_singleton]; decide⟩

-- The acyclic graph has a topological numbering, and its adjacency is `Relation.Acyclic`.
example : dag.IsDirAcyclic := by
  refine Graph.isDirAcyclic_of_rank (f := id) fun u v ⟨_, _, he⟩ => ?_
  simp only [dag, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

example (h : dag.IsDirAcyclic) : Relation.Acyclic dag.DirAdj :=
  Graph.isDirAcyclic_iff_acyclic.1 h

/-! ### Feedback vertex sets -/

-- Removing `0` breaks the triangle, but some vertex must be removed.
example : (⟨tri, 1⟩ : FeedbackVertexSetInstance) ∈ FeedbackVertexSet := by
  refine ⟨{0}, by decide, by decide, Graph.isDirAcyclic_of_rank (f := id) fun u v h => ?_⟩
  rw [Graph.dirAdj_deleteVerts] at h
  obtain ⟨⟨-, -, he⟩, hu, hv⟩ := h
  simp only [tri, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (Finset.mem_singleton_self 0) hu
  · decide
  · exact absurd (Finset.mem_singleton_self 0) hv

example : (⟨tri, 0⟩ : FeedbackVertexSetInstance) ∉ FeedbackVertexSet := by
  rw [mem_FeedbackVertexSet_iff_forall_isDirCycle]
  rintro ⟨R, -, hcard, hR⟩
  obtain rfl : R = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
  obtain ⟨v, -, hv⟩ := hR [0, 1, 2] ⟨by simp, by decide, by decide, by
    rw [Cycle.chain_coe_cons]; decide⟩
  exact Finset.notMem_empty v hv

-- A self-loop must be removed.
example : (⟨loop, 0⟩ : FeedbackVertexSetInstance) ∉ FeedbackVertexSet := by
  rintro ⟨R, -, hcard, hacyc⟩
  obtain rfl : R = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
  obtain ⟨f, -, hf⟩ := Graph.exists_rank_of_isDirAcyclic hacyc
  exact (hf 0 0 (Graph.dirAdj_deleteVerts.2 ⟨⟨by decide, by decide, by decide⟩,
    Finset.notMem_empty 0, Finset.notMem_empty 0⟩)).false

example : (⟨loop, 1⟩ : FeedbackVertexSetInstance) ∈ FeedbackVertexSet := by
  refine ⟨{0}, by decide, by decide, Graph.isDirAcyclic_of_rank (f := id) fun u v h => ?_⟩
  rw [Graph.dirAdj_deleteVerts] at h
  obtain ⟨⟨hu, -, -⟩, hu', -⟩ := h
  simp only [loop, List.mem_cons, List.not_mem_nil, or_false] at hu
  subst hu
  exact absurd (Finset.mem_singleton_self 0) hu'

-- An acyclic graph needs no removal.
example : (⟨dag, 0⟩ : FeedbackVertexSetInstance) ∈ FeedbackVertexSet := by
  refine ⟨∅, by simp, by simp, Graph.isDirAcyclic_of_rank (f := id) fun u v h => ?_⟩
  obtain ⟨⟨_, _, he⟩, -, -⟩ := Graph.dirAdj_deleteVerts.1 h
  simp only [dag, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

-- Arcs to undeclared vertices are ignored: `0 ⇄ 1` with only `0` declared has no cycle.
example : (⟨(⟨[0], [(0, 1), (1, 0)]⟩ : Graph), 0⟩ : FeedbackVertexSetInstance) ∈
    FeedbackVertexSet := by
  refine ⟨∅, by simp, by simp, Graph.isDirAcyclic_of_rank (f := fun _ => 0) fun u v h => ?_⟩
  obtain ⟨⟨hu, hv, he⟩, -, -⟩ := Graph.dirAdj_deleteVerts.1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  subst hu hv
  simp at he

/-! ### Karp's reduction from `VertexCover` -/

-- The edge `0 - 1` becomes the arcs `0 → 1` and `1 → 0`.
example : VertexCover.toFeedbackVertexSet (⟨⟨[0, 1], [(0, 1)]⟩, 1⟩ : VertexCoverInstance) =
    ⟨(⟨[0, 1], [(0, 1), (1, 0)]⟩ : Graph), 1⟩ := by
  decide

-- Self-loops of the undirected graph are dropped.
example : VertexCover.bidirect (⟨[0], [(0, 0)]⟩ : Graph) = (⟨[0], []⟩ : Graph) := by
  decide

-- A target above the number of distinct vertices goes to the self-loop with target `0`.
example : VertexCover.toFeedbackVertexSet (⟨⟨[0, 1], [(0, 1)]⟩, 3⟩ : VertexCoverInstance) =
    ⟨(⟨[0], [(0, 0)]⟩ : Graph), 0⟩ := by
  decide

example : (⟨⟨[0, 1], [(0, 1)]⟩, 1⟩ : VertexCoverInstance) ∈ VertexCover ↔
    VertexCover.toFeedbackVertexSet
      (⟨⟨[0, 1], [(0, 1)]⟩, 1⟩ : VertexCoverInstance) ∈ FeedbackVertexSet :=
  (VertexCover.toFeedbackVertexSet_mem_iff _).symm

end CslibFrontierTests.FeedbackVertexSet
