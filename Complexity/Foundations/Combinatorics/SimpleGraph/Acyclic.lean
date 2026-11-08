/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Rooting trees and parent arrays

Two ways of presenting a rooted tree.

* **Rooting a tree.** For a tree `T` on `ι` and a root `r`, `SimpleGraph.IsTree.pathTo hT r t`
  is the unique path from `t` to `r`. `SimpleGraph.IsTree.parent hT r t` is its second vertex: the
  neighbour of `t` on the way to `r`, or `r` itself when `t = r`. Every edge of `T` joins a vertex
  to its parent (`SimpleGraph.IsTree.adj_iff_parent`), and the parent is one step closer to the
  root (`SimpleGraph.IsTree.length_pathTo_parent`).
* **Parent arrays.** A map `p : Fin (n + 1) → Fin (n + 1)` with `p i < i` for every `i ≠ 0`
  determines the graph `SimpleGraph.parentTree p`, which joins each `i ≠ 0` to `p i`. It is a tree
  (`SimpleGraph.parentTree_isTree`). In such a tree a preconnected vertex set has at most one
  vertex whose parent lies outside it (`SimpleGraph.eq_of_preconnected_parentTree`).

Parent arrays are the input format of tree-decomposition algorithms; rooting is how an arbitrary
finite tree is brought into that format.

## Main definitions

* `SimpleGraph.IsTree.pathTo`, `SimpleGraph.IsTree.parent`: rooting a tree.
* `SimpleGraph.parentTree`: the tree of a parent array.

## Main results

* `SimpleGraph.IsTree.adj_iff_parent`: the edges of a rooted tree are the parent edges.
* `SimpleGraph.parentTree_isTree`: a parent array with `p i < i` for `i ≠ 0` gives a tree.
* `SimpleGraph.eq_of_preconnected_parentTree`: a preconnected set in a parent-array tree has a
  unique topmost vertex.
-/

public section

namespace SimpleGraph

universe uι

variable {ι : Type uι}

/-! ### Rooting a tree -/

namespace IsTree

variable {T : SimpleGraph ι} (hT : T.IsTree) (r : ι)

/-- The unique path in the tree `T` from `t` to the root `r`. -/
noncomputable def pathTo (t : ι) : T.Walk t r := (hT.existsUnique_path t r).choose

theorem isPath_pathTo (t : ι) : (hT.pathTo r t).IsPath :=
  (hT.existsUnique_path t r).choose_spec.1

theorem eq_pathTo {t : ι} {q : T.Walk t r} (hq : q.IsPath) : q = hT.pathTo r t :=
  (hT.existsUnique_path t r).choose_spec.2 q hq

/-- The parent of `t` when `T` is rooted at `r`: the second vertex of the path from `t` to `r`, or
`r` itself when `t = r`. -/
noncomputable def parent (t : ι) : ι := (hT.pathTo r t).snd

@[simp] theorem pathTo_self : hT.pathTo r r = Walk.nil := (hT.eq_pathTo r Walk.IsPath.nil).symm

@[simp] theorem parent_self : hT.parent r r = r := by
  rw [parent, pathTo_self]
  rfl

theorem adj_parent {t : ι} (ht : t ≠ r) : T.Adj t (hT.parent r t) :=
  Walk.adj_snd (Walk.not_nil_of_ne ht)

/-- The parent of a non-root vertex is one step closer to the root. -/
theorem length_pathTo_parent {t : ι} (ht : t ≠ r) :
    (hT.pathTo r (hT.parent r t)).length + 1 = (hT.pathTo r t).length := by
  have hnn := Walk.not_nil_of_ne (p := hT.pathTo r t) ht
  change (hT.pathTo r (hT.pathTo r t).snd).length + 1 = _
  rw [← hT.eq_pathTo r ((hT.isPath_pathTo r t).tail), Walk.length_tail_add_one hnn]

/-- Every edge of a rooted tree joins a non-root vertex to its parent. -/
theorem adj_iff_parent {x y : ι} :
    T.Adj x y ↔ (x ≠ r ∧ hT.parent r x = y) ∨ (y ≠ r ∧ hT.parent r y = x) := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hy : y ∈ (hT.pathTo r x).support
    · left
      have hxr : x ≠ r := by
        rintro rfl
        rw [pathTo_self] at hy
        simp only [Walk.support_nil, List.mem_singleton] at hy
        exact h.ne hy.symm
      exact ⟨hxr, (hT.isAcyclic.eq_snd_of_adj_start (hT.isPath_pathTo r x) h hy).symm⟩
    · right
      have hq : (Walk.cons h.symm (hT.pathTo r x)).IsPath := (hT.isPath_pathTo r x).cons hy
      have hyr : y ≠ r := by
        rintro rfl
        exact hy (Walk.end_mem_support _)
      refine ⟨hyr, ?_⟩
      rw [parent, ← hT.eq_pathTo r hq]
      exact Walk.snd_cons _ _
  · rintro (⟨hx, rfl⟩ | ⟨hy, rfl⟩)
    · exact hT.adj_parent r hx
    · exact (hT.adj_parent r hy).symm

end IsTree

/-! ### Parent arrays -/

/-- The graph of a parent array on `Fin (n + 1)`: each `i ≠ 0` is joined to `p i`. When
`p i < i` for every `i ≠ 0` this is a tree rooted at `0` (`parentTree_isTree`). -/
def parentTree {n : ℕ} (p : Fin (n + 1) → Fin (n + 1)) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun i j => i ≠ 0 ∧ p i = j

section ParentArray

variable {n : ℕ} {p : Fin (n + 1) → Fin (n + 1)}

theorem parentTree_adj (hlt : ∀ i, i ≠ 0 → p i < i) {i j : Fin (n + 1)} :
    (parentTree p).Adj i j ↔ (i ≠ 0 ∧ p i = j) ∨ (j ≠ 0 ∧ p j = i) := by
  rw [parentTree, fromRel_adj]
  constructor
  · exact fun h => h.2
  · rintro (⟨hi, rfl⟩ | ⟨hj, rfl⟩)
    · exact ⟨(hlt i hi).ne', Or.inl ⟨hi, rfl⟩⟩
    · exact ⟨(hlt j hj).ne, Or.inr ⟨hj, rfl⟩⟩

theorem parentTree_adj_self (hlt : ∀ i, i ≠ 0 → p i < i) {i : Fin (n + 1)} (hi : i ≠ 0) :
    (parentTree p).Adj i (p i) :=
  (parentTree_adj hlt).2 (Or.inl ⟨hi, rfl⟩)

private theorem parent_le_of (h0 : p 0 = 0) (hlt : ∀ i, i ≠ 0 → p i < i) (i : Fin (n + 1)) :
    p i ≤ i := by
  by_cases hi : i = 0
  · rw [hi, h0]
  · exact (hlt i hi).le

private theorem parent_iterate_le_of (h0 : p 0 = 0) (hlt : ∀ i, i ≠ 0 → p i < i) (a : ℕ)
    (i : Fin (n + 1)) : p^[a] i ≤ i := by
  induction a generalizing i with
  | zero => exact le_rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (parent_le_of h0 hlt i)

/-- A parent array with `p i < i` for every `i ≠ 0` describes a tree. -/
theorem parentTree_isTree (hlt : ∀ i, i ≠ 0 → p i < i) : (parentTree p).IsTree := by
  classical
  have hreach : ∀ i, (parentTree p).Reachable i 0 := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      by_cases hi : i = 0
      · rw [hi]
      · exact (parentTree_adj_self hlt hi).reachable.trans (ih _ (hlt i hi))
  rw [isTree_iff_connected_and_card]
  refine ⟨⟨fun i j => (hreach i).trans (hreach j).symm⟩, ?_⟩
  let f : {i : Fin (n + 1) // i ≠ 0} → (parentTree p).edgeSet :=
    fun i => ⟨s(i.1, p i.1), parentTree_adj_self hlt i.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
      have h' : s(i, p i) = s(j, p j) := congrArg Subtype.val h
      rcases Sym2.eq_iff.1 h' with ⟨h, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h
      · exfalso
        have h3 := hlt i hi
        have h4 := hlt j hj
        rw [h2] at h3
        rw [← h1] at h4
        exact lt_asymm h3 h4
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h i j =>
        rcases (parentTree_adj hlt).1 ((mem_edgeSet _).1 he) with ⟨hi, rfl⟩ | ⟨hj, rfl⟩
        · exact ⟨⟨i, hi⟩, rfl⟩
        · exact ⟨⟨j, hj⟩, Subtype.ext Sym2.eq_swap⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- In a parent-array tree, a preconnected vertex set has at most one *topmost* element: one that
is the root `0` or whose parent lies outside the set. -/
theorem eq_of_preconnected_parentTree (h0 : p 0 = 0) (hlt : ∀ i, i ≠ 0 → p i < i)
    {S : Set (Fin (n + 1))} (hS : ((parentTree p).induce S).Preconnected) {a b : Fin (n + 1)}
    (ha : a ∈ S) (hat : a = 0 ∨ p a ∉ S) (hb : b ∈ S) (hbt : b = 0 ∨ p b ∉ S) : a = b := by
  -- Every element of `S` climbs to a topmost element `a` through `S`: otherwise a walk inside
  -- `S` would cross from the ancestors-of-`a` side to the other along a parent edge.
  have key : ∀ {a b : Fin (n + 1)}, a ∈ S → (a = 0 ∨ p a ∉ S) → b ∈ S → ∃ k, p^[k] b = a := by
    intro a b ha hat hb
    by_contra hnot
    obtain ⟨w⟩ := hS ⟨a, ha⟩ ⟨b, hb⟩
    let w' := w.map (Embedding.induce S).toHom
    obtain ⟨d, hd, hd1, hd2⟩ := w'.exists_boundary_dart {x | ∃ k, p^[k] x = a} ⟨0, rfl⟩
      (by simpa using hnot)
    have hd2S : d.snd ∈ S := by
      have := w'.dart_snd_mem_support_of_mem_darts hd
      simp only [w', Walk.support_map, List.mem_map] at this
      obtain ⟨x, -, hx⟩ := this
      rw [← hx]
      exact x.2
    obtain ⟨k, hk⟩ := hd1
    rcases (parentTree_adj hlt).1 d.adj with ⟨-, hpd⟩ | ⟨hne, hpd⟩
    · rcases k with _ | k
      · simp only [Function.iterate_zero, id_eq] at hk
        subst hk
        rcases hat with h0' | hpa
        · exact hd2 ⟨0, by
            have : d.snd = p d.fst := hpd.symm
            rw [this, h0', h0]
            rfl⟩
        · exact hpa (hpd ▸ hd2S)
      · exact hd2 ⟨k, by rw [← hpd, ← Function.iterate_succ_apply]; exact hk⟩
    · exact hd2 ⟨k + 1, by rw [Function.iterate_succ_apply, hpd]; exact hk⟩
  obtain ⟨k, hk⟩ := key ha hat hb
  obtain ⟨l, hl⟩ := key hb hbt ha
  have h1 : a ≤ b := hk ▸ parent_iterate_le_of h0 hlt k b
  have h2 : b ≤ a := hl ▸ parent_iterate_le_of h0 hlt l a
  exact le_antisymm h1 h2

end ParentArray

end SimpleGraph
