/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Positions
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Berge
import Mathlib.Data.Set.Card

/-!
# Matchings represented by original edge positions

`matchingOfPositions` uses the original graph's adjacency and precisely the covered vertices;
it represents an incomplete matching without adding isolated vertices to its vertex set.
The position count is the cardinality of the existing Mathlib subgraph edge set.
-/

public section

namespace Cslib.Complexity.Graph

variable {G : Graph}

/-- Keep the selected original edges and exactly their endpoints. -/
@[expose] def matchingOfPositions (G : Graph) (S : Finset ℕ) : G.induced.Subgraph where
  verts := (ofPositions G S).support
  Adj := (ofPositions G S).Adj
  adj_sub := (ofPositions G S).adj_sub
  edge_vert h := ⟨_, h⟩
  symm := (ofPositions G S).symm

/-- At most one selected incident position per vertex suffices for a Mathlib matching. -/
theorem isMatching_matchingOfPositions {S : Finset ℕ}
    (huniq : ∀ (v : ℕ), v ∈ G.1 → ∀ i ∈ S, ∀ j ∈ S,
      incident (G.edgeList.getD i (0, 0)) v = true →
      incident (G.edgeList.getD j (0, 0)) v = true → i = j) :
    (matchingOfPositions G S).IsMatching := by
  intro u hu
  obtain ⟨w, hw⟩ := hu
  refine ⟨w, hw, fun w' hw' => ?_⟩
  have hne : u.val ≠ w.val := fun h => G.induced.ne_of_adj hw.1 (Subtype.ext h)
  obtain ⟨_, i, hi, he⟩ := hw
  obtain ⟨_, j, hj, he'⟩ := hw'
  have hinc : incident (G.edgeList.getD i (0, 0)) u = true := by
    rcases he with h | h <;> rw [h] <;> simp [incident]
  have hinc' : incident (G.edgeList.getD j (0, 0)) u = true := by
    rcases he' with h | h <;> rw [h] <;> simp [incident]
  have hij := huniq u u.2 i hi j hj hinc hinc'
  subst j
  apply Subtype.ext
  rcases he with h | h <;> rcases he' with h' | h' <;> rw [h] at h' <;>
    simp only [Prod.mk.injEq] at h' <;> omega

/-- Every selected valid edge is recovered by the represented subgraph. -/
theorem positions_matchingOfPositions {S : Finset ℕ}
    (hS : ∀ i ∈ S, i < G.edgeList.length) :
    positions (matchingOfPositions G S) = S := by
  ext i
  constructor
  · intro hi
    obtain ⟨hi, hu, hw, _, j, hj, he⟩ := mem_positions.mp hi
    have hij : j = i := eq_of_getD_edgeList (hS j hj) hi (by
      rcases he with he | he
      · exact Or.inl he
      · exact Or.inr he)
    exact hij ▸ hj
  · intro hi
    obtain ⟨hG, hne, ha, hb⟩ := of_mem_edgeList (getD_edgeList_mem (hS i hi))
    refine mem_positions.mpr ⟨hS i hi, ha, hb, ?_, i, hi, Or.inl rfl⟩
    rw [induced_adj, toSimpleGraph_adj]
    exact ⟨hne, Or.inl hG⟩

/-- Position cardinality is actual unoriented edge cardinality, for every subgraph. -/
theorem card_positions (M : G.induced.Subgraph) : (positions M).card = M.edgeSet.ncard := by
  classical
  let f : (positions M) → M.edgeSet := fun i =>
    ⟨s(⟨(G.edgeList.getD i.val (0, 0)).1,
        (of_mem_edgeList (getD_edgeList_mem (mem_positions.mp i.2).1)).2.2.1⟩,
      ⟨(G.edgeList.getD i.val (0, 0)).2,
        (of_mem_edgeList (getD_edgeList_mem (mem_positions.mp i.2).1)).2.2.2⟩), by
      obtain ⟨_, _, _, h⟩ := mem_positions.mp i.2
      exact h⟩
  have hinj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply eq_of_getD_edgeList (mem_positions.mp i.2).1 (mem_positions.mp j.2).1
    have hh := congrArg (fun e : M.edgeSet => Sym2.map Subtype.val e.val) he
    change s((G.edgeList.getD i.val (0, 0)).1, (G.edgeList.getD i.val (0, 0)).2) =
      s((G.edgeList.getD j.val (0, 0)).1, (G.edgeList.getD j.val (0, 0)).2) at hh
    exact Sym2.mk_eq_mk_iff.mp hh
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with | h u w =>
      obtain ⟨i, hi, hie⟩ := exists_getD_edgeList_of_adj (M.adj_sub he)
      refine ⟨⟨i, mem_positions.mpr ⟨hi, ?_⟩⟩, ?_⟩
      · rcases hie with hie | hie
        · rw [hie]
          exact ⟨u.2, w.2, he⟩
        · rw [hie]
          exact ⟨w.2, u.2, he.symm⟩
      · apply Subtype.ext
        apply (Sym2.map.injective Subtype.val_injective)
        change s((G.edgeList.getD i (0, 0)).1, (G.edgeList.getD i (0, 0)).2) = s(u.val, w.val)
        rcases hie with hie | hie
        · rw [hie]
        · rw [hie, Sym2.eq_swap]
  rw [← Nat.card_eq_finsetCard, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

end Cslib.Complexity.Graph
