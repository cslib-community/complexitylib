/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.FeedbackArcSet

/-!
# Feedback arc set: tests

Feedback arc sets of a directed triangle, a two-cycle and a self-loop, back arcs of a numbering,
the vertex-splitting reduction from `FeedbackVertexSet`, and the headline results.
-/

namespace CslibFrontierTests.FeedbackArcSet

open Cslib.Complexity Turing.MultiTapeTM

/-- The directed triangle `0 → 1 → 2 → 0`. -/
private def tri : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩

/-- The two-cycle `0 ⇄ 1`. -/
private def two : Graph := ⟨[0, 1], [(0, 1), (1, 0)]⟩

/-! ### Headline results -/

example : FeedbackArcSet ∈ NP encFeedbackArcSet ∧
    NPHard encFeedbackArcSet FeedbackArcSet ∧
    PolyTimeReducible encFeedbackVertexSet encFeedbackArcSet FeedbackVertexSet FeedbackArcSet :=
  ⟨FeedbackArcSet_npComplete.1, FeedbackArcSet_npComplete.2,
    polyTimeReducible_FeedbackVertexSet_FeedbackArcSet⟩

-- Karp's chain: `VertexCover` reduces to `FeedbackArcSet` through `FeedbackVertexSet`.
example :
    PolyTimeReducible encVertexCoverInstance encFeedbackArcSet VertexCover FeedbackArcSet :=
  polyTimeReducible_VertexCover_FeedbackVertexSet.trans
    polyTimeReducible_FeedbackVertexSet_FeedbackArcSet

example : ComputableInPolyTime (fun x : FeedbackArcSetInstance => x.graph)
    encFeedbackArcSet encGraph := by
  fun_prop

example : ComputableInPolyTime (fun x : FeedbackArcSetInstance => x.bound)
    encFeedbackArcSet encNat := by
  fun_prop

example : ComputableInPolyTime (fun p : Graph × ℕ => (⟨p.1, p.2⟩ : FeedbackArcSetInstance))
    (encPair encGraph encNat) encFeedbackArcSet := by
  fun_prop


/-! ### Feedback arc sets -/

-- Removing the arc `2 → 0` breaks the triangle, but some arc must be removed.
example : (⟨tri, 1⟩ : FeedbackArcSetInstance) ∈ FeedbackArcSet := by
  refine ⟨{(2, 0)}, by decide, by decide, Graph.isDirAcyclic_of_rank (f := id) fun u v h => ?_⟩
  rw [Graph.dirAdj_deleteArcs] at h
  obtain ⟨⟨-, -, he⟩, hS⟩ := h
  simp only [tri, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · decide
  · decide
  · exact absurd (Finset.mem_singleton_self _) hS

example : (⟨tri, 0⟩ : FeedbackArcSetInstance) ∉ FeedbackArcSet := by
  rintro ⟨S, -, hcard, hacyc⟩
  obtain rfl : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
  obtain ⟨f, -, hf⟩ := Graph.exists_rank_of_isDirAcyclic hacyc
  have harc (u v : ℕ) (h : tri.DirAdj u v) : f u < f v :=
    hf u v (Graph.dirAdj_deleteArcs.2 ⟨h, Finset.notMem_empty _⟩)
  have h01 := harc 0 1 ⟨by decide, by decide, by decide⟩
  have h12 := harc 1 2 ⟨by decide, by decide, by decide⟩
  have h20 := harc 2 0 ⟨by decide, by decide, by decide⟩
  omega

-- One arc of a two-cycle suffices.
example : (⟨two, 1⟩ : FeedbackArcSetInstance) ∈ FeedbackArcSet := by
  refine ⟨{(1, 0)}, by decide, by decide, Graph.isDirAcyclic_of_rank (f := id) fun u v h => ?_⟩
  rw [Graph.dirAdj_deleteArcs] at h
  obtain ⟨⟨-, -, he⟩, hS⟩ := h
  simp only [two, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · decide
  · exact absurd (Finset.mem_singleton_self _) hS

-- A self-loop must be removed.
example : (⟨(⟨[0], [(0, 0)]⟩ : Graph), 0⟩ : FeedbackArcSetInstance) ∉ FeedbackArcSet := by
  rintro ⟨S, -, hcard, hacyc⟩
  obtain rfl : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
  obtain ⟨f, -, hf⟩ := Graph.exists_rank_of_isDirAcyclic hacyc
  exact (hf 0 0 (Graph.dirAdj_deleteArcs.2
    ⟨⟨by decide, by decide, by decide⟩, Finset.notMem_empty _⟩)).false

/-! ### Back arcs -/

-- The numbering `0 ↦ 1, 1 ↦ 2, 2 ↦ 3` of the triangle has the single back arc `2 → 0`.
example : FeedbackArcSet.backArcs tri [1, 2, 3] = [(2, 0)] := by
  decide

/-! ### The vertex-splitting reduction -/

-- The arc `0 → 1` between the vertices `0` and `1` becomes `0 → 1`, `2 → 3` and `1 → 2`.
example : FeedbackVertexSet.toFeedbackArcSet ⟨(⟨[0, 1], [(0, 1)]⟩ : Graph), 1⟩ =
    ⟨(⟨[0, 2, 1, 3], [(0, 1), (2, 3), (1, 2)]⟩ : Graph), 1⟩ := by
  decide

-- The split triangle has a feedback arc set of size one, the arc of the vertex `0`.
example : FeedbackVertexSet.toFeedbackArcSet ⟨tri, 1⟩ ∈ FeedbackArcSet :=
  (FeedbackVertexSet.toFeedbackArcSet_mem_iff _).2 ⟨{0}, by decide, by decide,
    Graph.isDirAcyclic_of_rank (f := id) fun u v h => by
      rw [Graph.dirAdj_deleteVerts] at h
      obtain ⟨⟨-, -, he⟩, hu, hv⟩ := h
      simp only [tri, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (Finset.mem_singleton_self 0) hu
      · decide
      · exact absurd (Finset.mem_singleton_self 0) hv⟩

end CslibFrontierTests.FeedbackArcSet
