/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Perfect matchings of bipartite graphs and the 0/1 permanent

A Boolean table `A` with `n` rows is the biadjacency matrix of the bipartite simple graph
`bipartiteGraph A` on `Fin n ⊕ Fin n`: the left vertex `i` and the right vertex `j` are adjacent
exactly when entry `j` of row `i` is `true`, and no two vertices on the same side are adjacent.
`BipartitePerfectMatchingCount A` is the number of perfect matchings of this graph, in the sense
of Mathlib's `SimpleGraph.Subgraph.IsPerfectMatching`. A perfect matching matches every left
vertex `i` with a right vertex `σ i`, and `σ` is a permutation supported on `true` entries, so
the count is the 0/1 permanent (`bipartitePerfectMatchingCount_eq_zeroOnePermanent`,
[Goldreich, Exercise 6.23][Goldreich2007Draft], [Arora and Barak, Section 9.2.1][AroraBarak07]).
Every statement about `ZeroOnePermanent`, including its #P-completeness, therefore applies to
counting perfect matchings in bipartite graphs, the form of Goldreich's Theorem 6.20.

## Main definitions

* `Cslib.Complexity.bipartiteGraph`: the bipartite graph of a Boolean table.
* `Cslib.Complexity.BipartitePerfectMatchingCount`: the number of its perfect matchings.

## Main results

* `Cslib.Complexity.bipartitePerfectMatchingCount_eq_zeroOnePermanent`: perfect matchings are
  counted by the 0/1 permanent.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

@[expose] public section

namespace Cslib.Complexity

open SimpleGraph

/-- Adjacency in the bipartite graph of a Boolean table: the left vertex `i` and the right vertex
`j` are adjacent when entry `j` of row `i` is `true`; vertices on one side are not adjacent. -/
def bipartiteAdj (A : List (List Bool)) :
    Fin A.length ⊕ Fin A.length → Fin A.length ⊕ Fin A.length → Prop
  | .inl i, .inr j => A[i].getD j false = true
  | .inr j, .inl i => A[i].getD j false = true
  | _, _ => False

/-- The bipartite simple graph on `Fin n ⊕ Fin n` whose biadjacency matrix is the Boolean
table `A` with `n` rows. -/
def bipartiteGraph (A : List (List Bool)) : SimpleGraph (Fin A.length ⊕ Fin A.length) where
  Adj := bipartiteAdj A
  symm := ⟨fun u v h => by cases u <;> cases v <;> simp_all [bipartiteAdj]⟩
  loopless := ⟨fun u h => by cases u <;> simp [bipartiteAdj] at h⟩

@[simp]
theorem bipartiteGraph_adj (A : List (List Bool)) (u v : Fin A.length ⊕ Fin A.length) :
    (bipartiteGraph A).Adj u v ↔ bipartiteAdj A u v :=
  Iff.rfl

/-- The number of perfect matchings of the bipartite graph of a Boolean table. -/
noncomputable def BipartitePerfectMatchingCount (A : List (List Bool)) : ℕ :=
  Nat.card {M : (bipartiteGraph A).Subgraph // M.IsPerfectMatching}

/-- The matching adjacency of a permutation: the left vertex `i` is matched with the right vertex
`σ i`. -/
def permMatchingAdj {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n ⊕ Fin n → Fin n ⊕ Fin n → Prop
  | .inl i, .inr j => σ i = j
  | .inr j, .inl i => σ i = j
  | _, _ => False

/-- The perfect matching of a permutation supported on `true` entries. -/
def permSubgraph (A : List (List Bool)) (σ : Equiv.Perm (Fin A.length))
    (hσ : ∀ i : Fin A.length, A[i].getD (σ i) false = true) : (bipartiteGraph A).Subgraph where
  verts := Set.univ
  Adj := permMatchingAdj σ
  adj_sub {u v} h := by
    rw [bipartiteGraph_adj]
    cases u <;> cases v <;> simp only [permMatchingAdj] at h
    · simp only [bipartiteAdj, ← h, hσ]
    · simp only [bipartiteAdj, ← h, hσ]
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun u v h => by cases u <;> cases v <;> simp_all [permMatchingAdj]⟩

/-- The subgraph of a permutation is a perfect matching. -/
theorem permSubgraph_isPerfectMatching (A : List (List Bool)) (σ : Equiv.Perm (Fin A.length))
    (hσ : ∀ i : Fin A.length, A[i].getD (σ i) false = true) :
    (permSubgraph A σ hσ).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  rintro (i | j)
  · refine ⟨.inr (σ i), rfl, fun w hw => ?_⟩
    cases w with
    | inl _ => exact hw.elim
    | inr j => exact congrArg Sum.inr (Eq.symm (show σ i = j from hw))
  · refine ⟨.inl (σ.symm j), σ.apply_symm_apply j, fun w hw => ?_⟩
    cases w with
    | inl i => exact congrArg Sum.inl (σ.eq_symm_apply.mpr (show σ i = j from hw))
    | inr _ => exact hw.elim

/-- **Perfect matchings of a bipartite graph are counted by the 0/1 permanent** of its
biadjacency table [Goldreich, Exercise 6.23][Goldreich2007Draft]. -/
theorem bipartitePerfectMatchingCount_eq_zeroOnePermanent (A : List (List Bool)) :
    BipartitePerfectMatchingCount A = ZeroOnePermanent A := by
  classical
  rw [zeroOnePermanent_eq_card, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    BipartitePerfectMatchingCount]
  symm
  refine Nat.card_eq_of_bijective
    (fun σ => ⟨permSubgraph A σ.1 σ.2, permSubgraph_isPerfectMatching A σ.1 σ.2⟩) ⟨?_, ?_⟩
  · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
    have h' := congrArg (fun M : {M : (bipartiteGraph A).Subgraph // M.IsPerfectMatching} =>
      M.1.Adj) h
    simp only at h'
    refine Subtype.ext (Equiv.ext fun i => ?_)
    have := congrFun (congrFun h' (.inl i)) (.inr (σ i))
    simp only [permSubgraph] at this
    exact (this.mp (rfl : σ i = σ i)).symm
  · rintro ⟨M, hM⟩
    rw [Subgraph.isPerfectMatching_iff] at hM
    have hleft : ∀ i, ∃ j, M.Adj (.inl i) (.inr j) := fun i => by
      obtain ⟨w, hw, -⟩ := hM (.inl i)
      cases w with
      | inl k => exact (M.adj_sub hw).elim
      | inr j => exact ⟨j, hw⟩
    choose f hf using hleft
    have hinj : Function.Injective f := fun i k hik => by
      obtain ⟨w, -, hw⟩ := hM (.inr (f i))
      have h1 := hw _ (M.symm.symm _ _ (hf i))
      have h2 := hw _ (M.symm.symm _ _ (hik ▸ hf k))
      exact Sum.inl_injective (h1.trans h2.symm)
    let σ : Equiv.Perm (Fin A.length) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    have hσ : ∀ i : Fin A.length, A[i].getD (σ i) false = true := fun i => M.adj_sub (hf i)
    refine ⟨⟨σ, hσ⟩, Subtype.ext (Subgraph.ext ?_ ?_)⟩
    · simp only [permSubgraph]
      exact (Set.eq_univ_of_forall fun v => M.edge_vert (hM v).exists.choose_spec).symm
    · funext u v
      have key : ∀ i j, M.Adj (.inl i) (.inr j) ↔ f i = j := fun i j =>
        ⟨fun h => by
          obtain ⟨w, -, hw⟩ := hM (.inl i)
          exact Sum.inr_injective ((hw _ (hf i)).trans (hw _ h).symm),
         fun h => h ▸ hf i⟩
      apply propext
      cases u with
      | inl i =>
        cases v with
        | inl k => exact ⟨False.elim, fun h => (M.adj_sub h).elim⟩
        | inr j => exact (key i j).symm
      | inr j =>
        cases v with
        | inl i => exact (key i j).symm.trans ⟨fun h => M.symm.symm _ _ h,
            fun h => M.symm.symm _ _ h⟩
        | inr k => exact ⟨False.elim, fun h => (M.adj_sub h).elim⟩

end Cslib.Complexity
