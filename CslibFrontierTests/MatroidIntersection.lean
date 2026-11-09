/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Matroid.Intersection.Konig

/-!
# Tests for matroid intersection

Exercises:
1. Bipartite matching as two unit-capacity partition matroids on `Fin 2 × Fin 2`: a common
   independent set, a set that fails in `M₁`, and the `IsMatching` correspondence.
2. **Shortest walks matter.** In the graph with edges `a = (0,0)`, `b = (1,0)` and `c = (0,1)` and
   `I = {b}`, the list `[a, b, c]` is an `X₁(I)`-to-`X₂(I)` walk in the exchange digraph, but
   `I ∆ {a, b, c} = {a, c}` is not independent in `M₁`, since both edges share the left vertex `0`.
   The single vertex walk `[c]` is shortest, and augmenting along it gives the matching `{b, c}`.
3. Nonvacuity of `IsShortestExchAugWalk` on a three-edge path where the shortest walk has three
   vertices, and its augmentation.
4. König's theorem recovered from `exists_maxMatching_separatorCover`.
-/

namespace CslibFrontierTests.MatroidIntersection

open Cslib.Algorithms.Lean.Matroid Cslib.Algorithms.Lean.MaxFlow
open scoped symmDiff

private abbrev V := Fin 2 × Fin 2

private abbrev M₁ : Matroid V := unitPartitionMatroid Prod.fst
private abbrev M₂ : Matroid V := unitPartitionMatroid Prod.snd

/-- Independence of a `Finset` in a unit-capacity partition matroid, as a decidable statement. -/
private theorem indep_coe_iff {β : Type*} (f : V → β) (S : Finset V) :
    (unitPartitionMatroid f).Indep (S : Set V) ↔ ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
  rw [unitPartitionMatroid_indep_iff]
  exact ⟨fun h x hx y hy hxy => h hx hy hxy, fun h x hx y hy hxy => h x hx y hy hxy⟩

/-! ## 1. Common independent sets of the two partition matroids -/

example : IsCommonIndep M₁ M₂ {(0, 0), (1, 1)} := by
  refine ⟨?_, ?_⟩ <;> rw [indep_coe_iff] <;> decide

example : ¬ IsCommonIndep M₁ M₂ {(0, 0), (0, 1)} := by
  rintro ⟨h₁, -⟩
  rw [indep_coe_iff] at h₁
  exact absurd (h₁ (0, 0) (by decide) (0, 1) (by decide) rfl) (by decide)

private def gPath : V → Bool
  | (0, 0) => true
  | (1, 0) => true
  | (0, 1) => true
  | _ => false

example : IsMatching gPath {(1, 0), (0, 1)} ↔
    {(1, 0), (0, 1)} ⊆ bipartiteEdges gPath ∧ IsCommonIndep M₁ M₂ {(1, 0), (0, 1)} :=
  isMatching_iff_isCommonIndep

example : IsMatching gPath {(1, 0), (0, 1)} := by decide

/-! ## 2. Augmenting along a non-shortest walk can fail -/

private abbrev E : Finset V := {(0, 0), (1, 0), (0, 1)}
private abbrev I₀ : Finset V := {(1, 0)}

/-- `[a, b, c]` with `a = (0,0)`, `b = (1,0)`, `c = (0,1)` is an augmenting walk for `I₀ = {b}`. -/
private theorem longWalk_isExchAugWalk : IsExchAugWalk M₁ M₂ E I₀ [(0, 0), (1, 0), (0, 1)] := by
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rw [indep_coe_iff]
    decide
  · refine ⟨by decide, ?_⟩
    rw [indep_coe_iff]
    decide
  · decide
  · refine List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_ (List.isChain_singleton _))
    · refine .inr ⟨by decide, by decide, ?_⟩
      rw [indep_coe_iff]
      decide
    · refine .inl ⟨by decide, by decide, ?_⟩
      rw [indep_coe_iff]
      decide

/-- The walk `[a, b, c]` is not shortest, and augmenting along it breaks `M₁`-independence. -/
example : ¬ M₁.Indep ((I₀ ∆ [(0, 0), (1, 0), (0, 1)].toFinset : Finset V) : Set V) := by
  rw [indep_coe_iff]
  decide

/-- The one-vertex walk `[c]` is a shortest augmenting walk. -/
private theorem shortWalk_isShortest : IsShortestExchAugWalk M₁ M₂ E I₀ [(0, 1)] := by
  refine ⟨⟨List.cons_ne_nil _ _, ?_, ?_, by decide, List.isChain_singleton _⟩, ?_⟩
  · refine ⟨by decide, ?_⟩
    rw [indep_coe_iff]
    decide
  · refine ⟨by decide, ?_⟩
    rw [indep_coe_iff]
    decide
  · rintro q ⟨hne, -⟩
    exact List.length_pos_of_ne_nil hne

example : ¬ IsShortestExchAugWalk M₁ M₂ E I₀ [(0, 0), (1, 0), (0, 1)] := fun h => by
  have := h.2 [(0, 1)] shortWalk_isShortest.1
  simp at this

/-- Augmenting along the shortest walk `[c]` gives the matching `{b, c}` of size two. -/
example : IsCommonIndep M₁ M₂ (I₀ ∆ [(0, 1)].toFinset) ∧ (I₀ ∆ [(0, 1)].toFinset).card = 2 :=
  let h := shortWalk_isShortest.augment (by decide)
  ⟨h.2.1, h.2.2⟩

/-! ## 3. A shortest walk with three vertices -/

/-- The path `(0,1) — (0,0) — (1,0)`, seen from the edges: `e₁ = (0,1)`, `e₂ = (0,0)`,
`e₃ = (1,0)`, with `I = {e₂}`. -/
private abbrev F : Finset V := {(0, 1), (0, 0), (1, 0)}
private abbrev J₀ : Finset V := {(0, 0)}

private theorem pathWalk_isExchAugWalk : IsExchAugWalk M₁ M₂ F J₀ [(1, 0), (0, 0), (0, 1)] := by
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rw [indep_coe_iff]
    decide
  · refine ⟨by decide, ?_⟩
    rw [indep_coe_iff]
    decide
  · decide
  · refine List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_ (List.isChain_singleton _))
    · refine .inr ⟨by decide, by decide, ?_⟩
      rw [indep_coe_iff]
      decide
    · refine .inl ⟨by decide, by decide, ?_⟩
      rw [indep_coe_iff]
      decide

/-- No augmenting walk for `J₀ = {(0,0)}` has fewer than three vertices. `X₁(J₀) = {(1,0)}` and
`X₂(J₀) = {(0,1)}` are disjoint, so there is no one-vertex walk. Arcs alternate between `F \ J₀`
and `J₀`, so a two-vertex walk would end in `J₀`, which contains no sink. -/
private theorem pathWalk_isShortest :
    IsShortestExchAugWalk M₁ M₂ F J₀ [(1, 0), (0, 0), (0, 1)] := by
  refine ⟨pathWalk_isExchAugWalk, fun q hq => ?_⟩
  obtain ⟨hne, ⟨hsrcE, hsrc⟩, ⟨hsnkE, hsnk⟩, hmem, hchain⟩ := hq
  match q, hne, hsrcE, hsrc, hsnkE, hsnk, hmem, hchain with
  | [u], _, hsrcE, hsrc, _, hsnk, hmem, _ =>
    exfalso
    simp only [List.head_cons, List.getLast_singleton] at hsrcE hsrc hsnk
    rw [indep_coe_iff] at hsrc hsnk
    have hu : u ∈ F := hmem u (List.mem_singleton_self u)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact absurd hsrc (by decide)
    · exact absurd hsrcE (by decide)
    · exact absurd hsnk (by decide)
  | [u, v], _, hsrcE, _, hsnkE, _, _, hchain =>
    exfalso
    simp only [List.head_cons, List.getLast_cons_cons, List.getLast_singleton] at hsrcE hsnkE
    rcases (List.IsChain.rel hchain : IsExchArc M₁ M₂ F J₀ u v) with ⟨hu, -⟩ | ⟨-, hv, -⟩
    · exact (Finset.mem_sdiff.mp hsrcE).2 hu
    · exact (Finset.mem_sdiff.mp hsnkE).2 hv
  | _ :: _ :: _ :: _, _, _, _, _, _, _, _ => simp

example : IsCommonIndep M₁ M₂ (J₀ ∆ [(1, 0), (0, 0), (0, 1)].toFinset) ∧
    (J₀ ∆ [(1, 0), (0, 0), (0, 1)].toFinset).card = 2 :=
  let h := pathWalk_isShortest.augment (by decide)
  ⟨h.2.1, h.2.2⟩

/-! ## 4. König's theorem from Edmonds' theorem -/

/-- König's theorem for every finite bipartite graph, obtained from the matroid-intersection
bridge (compare `Cslib.Algorithms.Lean.MaxFlow.exists_maxMatching_eq_minVertexCover`). -/
example {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (G : L × R → Bool) :
    ∃ (M : Finset (L × R)) (C : VertexCover L R),
      IsMaxMatching G M ∧ IsMinVertexCover G C ∧ M.card = C.size := by
  obtain ⟨M, U, -, hM, hC, heq⟩ := exists_maxMatching_separatorCover G
  exact ⟨M, _, hM, hC, heq⟩

/-- On `gPath`, the separator `U = {(0,0), (0,1)}` gives the cover with left vertex `0` and right
vertex `0`, of size two. -/
example : IsVertexCover gPath (separatorCover (bipartiteEdges gPath) {(0, 0), (0, 1)}) ∧
    (separatorCover (bipartiteEdges gPath) {(0, 0), (0, 1)}).size = 2 :=
  ⟨isVertexCover_separatorCover gPath _, by decide⟩

end CslibFrontierTests.MatroidIntersection
