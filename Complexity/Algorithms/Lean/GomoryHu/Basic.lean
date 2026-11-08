/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Submodular.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Powerset

/-!
# Gomory–Hu trees of set functions

A set function `f : Finset V → β` on a finite ground set `V` assigns a value to every cut. A set
`X` is a minimum `s`–`t` cut of `f` (`IsMinCutBetween f s t X`) when it contains `s`, misses `t`,
and minimizes `f` among such sets. The cut function `X ↦ w(δ(X))` of an undirected graph with edge
weights `w` is the motivating example; it is symmetric (`f Xᶜ = f X`) and submodular.

A **Gomory–Hu tree** (cut-equivalent tree) of `f` ([GomoryHu1961]; [Schrijver2003],
Section 15.4) is a spanning tree `T` on `V` such that for every tree edge `uv`, the side of `T - uv`
containing `u` is a minimum `u`–`v` cut of `f`. This module defines Gomory–Hu trees, the sides of
tree edges (`edgeSide`), and proves that for every two distinct vertices `s, t`, some edge on the
`s`–`t` path of a Gomory–Hu tree has a side that is a minimum `s`–`t` cut. Existence of Gomory–Hu
trees for symmetric submodular functions is in `Complexity.Algorithms.Lean.GomoryHu.Existence`, and
the weighted-graph instance in `Complexity.Algorithms.Lean.GomoryHu.WeightedCut`.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.IsMinCutBetween`: `X` is a minimum `s`–`t` cut of `f`.
* `Cslib.Algorithms.Lean.GomoryHu.edgeSide`: the vertices reachable from `u` in `T` after deleting
  the edge `uv`.
* `Cslib.Algorithms.Lean.GomoryHu.IsGomoryHuTree`: a spanning tree whose edge sides are minimum
  cuts between the edge's endpoints.

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.exists_isMinCutBetween`: minimum cuts exist between distinct
  elements, for values in a linear order.
* `Cslib.Algorithms.Lean.GomoryHu.IsMinCutBetween.inter`: uncrossing of minimum cuts for a
  submodular function.
* `Cslib.Algorithms.Lean.GomoryHu.mem_edgeSide_of_mem_darts`: along a path in a forest, the start
  and the end of the path lie on opposite sides of each edge of the path.
* `Cslib.Algorithms.Lean.GomoryHu.edgeSide_eq_of_forall_adj`: a criterion that identifies the side
  of a tree edge, used to check candidate Gomory–Hu trees.
* `Cslib.Algorithms.Lean.GomoryHu.IsGomoryHuTree.exists_isMinCutBetween_of_isPath`: some edge of
  the `s`–`t` path of a Gomory–Hu tree has a side that is a minimum `s`–`t` cut.

## References

* [GomoryHu1961]
* [Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean.Submodular

variable {V : Type*} {β : Type*}

/-! ### Minimum cuts between two elements -/

/-- `X` is a minimum `s`–`t` cut of the set function `f` when it contains `s`, misses `t`, and
`f X ≤ f Y` for every `Y` that contains `s` and misses `t`. -/
@[expose] def IsMinCutBetween [Preorder β] (f : Finset V → β) (s t : V) (X : Finset V) : Prop :=
  s ∈ X ∧ t ∉ X ∧ ∀ Y : Finset V, s ∈ Y → t ∉ Y → f X ≤ f Y

section MinCut

variable [Preorder β] {f : Finset V → β} {s t : V} {X : Finset V}

theorem IsMinCutBetween.left_mem (h : IsMinCutBetween f s t X) : s ∈ X := h.1

theorem IsMinCutBetween.right_notMem (h : IsMinCutBetween f s t X) : t ∉ X := h.2.1

theorem IsMinCutBetween.le (h : IsMinCutBetween f s t X) {Y : Finset V} (hs : s ∈ Y)
    (ht : t ∉ Y) : f X ≤ f Y :=
  h.2.2 Y hs ht

theorem IsMinCutBetween.ne (h : IsMinCutBetween f s t X) : s ≠ t := fun hst =>
  h.right_notMem (hst ▸ h.left_mem)

variable [Fintype V] [DecidableEq V]

/-- For a symmetric set function, the complement of a minimum `s`–`t` cut is a minimum `t`–`s`
cut. -/
theorem IsMinCutBetween.compl (hsym : ∀ X, f Xᶜ = f X) (h : IsMinCutBetween f s t X) :
    IsMinCutBetween f t s Xᶜ := by
  refine ⟨Finset.mem_compl.mpr h.right_notMem, fun hs => Finset.mem_compl.mp hs h.left_mem,
    fun Y ht hs => ?_⟩
  rw [hsym, ← hsym Y]
  exact h.le (Finset.mem_compl.mpr hs) (fun h' => Finset.mem_compl.mp h' ht)

/-- For a symmetric set function, a minimum `s`–`t` cut is no larger than any set separating `s`
from `t`, in either direction. -/
theorem IsMinCutBetween.le_of_separates (hsym : ∀ X, f Xᶜ = f X) (h : IsMinCutBetween f s t X)
    {Y : Finset V} (hY : s ∈ Y ↔ t ∉ Y) : f X ≤ f Y := by
  by_cases hs : s ∈ Y
  · exact h.le hs (hY.mp hs)
  · rw [← hsym Y]
    exact h.le (Finset.mem_compl.mpr hs)
      (fun ht => Finset.mem_compl.mp ht (not_not.mp (mt hY.mpr hs)))

end MinCut

/-- Minimum cuts exist between distinct elements of a finite ground set. -/
theorem exists_isMinCutBetween [LinearOrder β] [Finite V] (f : Finset V → β)
    {s t : V} (hst : s ≠ t) : ∃ X, IsMinCutBetween f s t X := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨X, hX, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun X : Finset V => s ∈ X ∧ t ∉ X) f
    ⟨{s}, by simp [hst.symm]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
  exact ⟨X, hX.1, hX.2, fun Y hs ht => hmin Y (by simp [hs, ht])⟩

/-- **Uncrossing.** For a submodular `f`, if `U` is a minimum `s`–`t` cut, `a ∈ U`, and `X` is a
minimum `a`–`b` cut missing `t`, then `X ∩ U` is a minimum `a`–`b` cut too. -/
theorem IsMinCutBetween.inter [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    [DecidableEq V] {f : Finset V → β} {s t a b : V} {U X : Finset V}
    (hX : IsMinCutBetween f a b X) (hsub : IsSubmodular f) (hU : IsMinCutBetween f s t U)
    (haU : a ∈ U) (htX : t ∉ X) : IsMinCutBetween f a b (X ∩ U) := by
  refine ⟨Finset.mem_inter.mpr ⟨hX.left_mem, haU⟩,
    fun hb => hX.right_notMem (Finset.mem_inter.mp hb).1, fun Y ha hb => ?_⟩
  have h1 : f U ≤ f (X ∪ U) :=
    hU.le (Finset.mem_union_right _ hU.left_mem)
      (by simp only [Finset.mem_union, not_or]; exact ⟨htX, hU.right_notMem⟩)
  have h3 : f (X ∩ U) + f U ≤ f X + f U :=
    calc f (X ∩ U) + f U ≤ f (X ∩ U) + f (X ∪ U) := add_le_add le_rfl h1
      _ = f (X ∪ U) + f (X ∩ U) := add_comm _ _
      _ ≤ f X + f U := hsub X U
  exact (le_of_add_le_add_right h3).trans (hX.le ha hb)

/-! ### Sides of tree edges -/

/-- The side of the edge `uv` containing `u` in a graph `T`: the vertices reachable from `u` once
the edge `s(u, v)` is deleted. For an edge `uv` of a tree, this is the component of `u` in
`T - uv`. -/
noncomputable def edgeSide [Fintype V] (T : SimpleGraph V) (u v : V) : Finset V :=
  haveI := Classical.decPred fun x => (T.deleteEdges {s(u, v)}).Reachable u x
  Finset.univ.filter fun x => (T.deleteEdges {s(u, v)}).Reachable u x

section Tree

variable [Fintype V] {T : SimpleGraph V}

theorem mem_edgeSide {u v x : V} :
    x ∈ edgeSide T u v ↔ (T.deleteEdges {s(u, v)}).Reachable u x := by
  unfold edgeSide
  simp

theorem mem_edgeSide_self (u v : V) : u ∈ edgeSide T u v :=
  mem_edgeSide.mpr (SimpleGraph.Reachable.refl u)

theorem notMem_edgeSide_of_isAcyclic (hT : T.IsAcyclic) {u v : V} (huv : T.Adj u v) :
    v ∉ edgeSide T u v := fun h =>
  (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT huv) (mem_edgeSide.mp h)

/-- In a tree, the two sides of an edge partition the vertices. -/
theorem mem_edgeSide_swap (hT : T.IsTree) {u v : V} (huv : T.Adj u v) (x : V) :
    x ∈ edgeSide T v u ↔ x ∉ edgeSide T u v := by
  rw [mem_edgeSide, mem_edgeSide, Sym2.eq_swap]
  have hbr := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic huv
  rw [SimpleGraph.isBridge_iff] at hbr
  constructor
  · intro hv hu
    exact hbr (hu.trans hv.symm)
  · intro hu
    -- Every vertex reaches `u` or `v` in `T - uv`.
    have key : ∀ a b (q : T.Walk a b), ((T.deleteEdges {s(u, v)}).Reachable u b ∨
        (T.deleteEdges {s(u, v)}).Reachable v b) →
        ((T.deleteEdges {s(u, v)}).Reachable u a ∨ (T.deleteEdges {s(u, v)}).Reachable v a) := by
      intro a b q
      induction q with
      | nil => exact id
      | @cons a c b hac q ih =>
        intro hb
        by_cases he : s(a, c) = s(u, v)
        · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (SimpleGraph.Reachable.refl _)
          · exact Or.inr (SimpleGraph.Reachable.refl _)
        · have hadj : (T.deleteEdges {s(u, v)}).Adj c a := by
            rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_swap]
            exact ⟨hac.symm, he⟩
          exact (ih hb).imp (fun h => h.trans hadj.reachable) (fun h => h.trans hadj.reachable)
    obtain ⟨q⟩ := hT.connected.preconnected x u
    exact (key x u q (Or.inl (SimpleGraph.Reachable.refl u))).resolve_left hu

/-- In a tree, the side of `vu` containing `v` is the complement of the side of `uv` containing
`u`. -/
theorem edgeSide_swap [DecidableEq V] (hT : T.IsTree) {u v : V} (huv : T.Adj u v) :
    edgeSide T v u = (edgeSide T u v)ᶜ := by
  ext x
  rw [Finset.mem_compl]
  exact mem_edgeSide_swap hT huv x

/-- Along a path in a forest, the start and the end of the path lie on the two sides of each of
its darts. -/
theorem mem_edgeSide_of_mem_darts (hT : T.IsAcyclic) {s t : V} {p : T.Walk s t}
    (hp : p.IsPath) {d : T.Dart} (hd : d ∈ p.darts) :
    s ∈ edgeSide T d.fst d.snd ∧ t ∉ edgeSide T d.fst d.snd := by
  have hbr := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT d.adj
  rw [SimpleGraph.isBridge_iff] at hbr
  have key : ∀ a b (q : T.Walk a b), q.IsPath → ∀ d ∈ q.darts,
      (T.deleteEdges {s(d.fst, d.snd)}).Reachable d.fst a ∧
        (T.deleteEdges {s(d.fst, d.snd)}).Reachable d.snd b := by
    intro a b q
    induction q with
    | nil => intro _ d hd; simp at hd
    | @cons a a' b haa' q ih =>
      intro hp d hd
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      rw [SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
      rcases hd with rfl | hd
      · refine ⟨SimpleGraph.Reachable.refl _, ?_⟩
        rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
        exact ⟨q, fun h => hp.2 (q.fst_mem_support_of_mem_edges h)⟩
      · obtain ⟨h1, h2⟩ := ih hp.1 d hd
        refine ⟨?_, h2⟩
        have hne : s(a, a') ≠ s(d.fst, d.snd) := by
          intro h
          rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨h', _⟩
          · exact hp.2 (h' ▸ q.dart_fst_mem_support_of_mem_darts hd)
          · exact hp.2 (h' ▸ q.dart_snd_mem_support_of_mem_darts hd)
        have hadj : (T.deleteEdges {s(d.fst, d.snd)}).Adj a' a := by
          rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_swap]
          exact ⟨haa'.symm, hne⟩
        exact h1.trans hadj.reachable
  obtain ⟨h1, h2⟩ := key s t p hp d hd
  exact ⟨mem_edgeSide.mpr h1, fun h => hbr ((mem_edgeSide.mp h).trans h2.symm)⟩

/-- A criterion for the side of a tree edge: if `S` contains `u`, misses `v`, and no other edge of
the tree `T` crosses `S`, then `S` is the side of `uv` containing `u`. -/
theorem edgeSide_eq_of_forall_adj (hT : T.IsTree) {u v : V} (huv : T.Adj u v) {S : Finset V}
    (hu : u ∈ S) (hv : v ∉ S)
    (hS : ∀ ⦃x y : V⦄, T.Adj x y → s(x, y) ≠ s(u, v) → (x ∈ S ↔ y ∈ S)) :
    edgeSide T u v = S := by
  have inv : ∀ a b, (T.deleteEdges {s(u, v)}).Reachable a b → (a ∈ S ↔ b ∈ S) := by
    intro a b h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Iff.rfl
    | tail _ hbc ih =>
      rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hbc
      exact ih.trans (hS hbc.1 hbc.2)
  ext x
  constructor
  · intro hx
    exact (inv u x (mem_edgeSide.mp hx)).mp hu
  · intro hx
    by_contra hx'
    have h := (mem_edgeSide_swap hT huv x).mpr hx'
    rw [mem_edgeSide, Sym2.eq_swap] at h
    exact hv ((inv v x h).mpr hx)

end Tree

/-! ### Gomory–Hu trees -/

/-- A **Gomory–Hu tree** (cut-equivalent tree) of a set function `f` on the finite ground set `V`
([GomoryHu1961]; [Schrijver2003], Section 15.4): a spanning tree `T` on `V` such that for every
tree edge `uv`, the side of `T - uv` containing `u` is a minimum `u`–`v` cut of `f`. -/
structure IsGomoryHuTree [Fintype V] [Preorder β] (f : Finset V → β) (T : SimpleGraph V) :
    Prop where
  /-- `T` is a spanning tree on `V`. -/
  isTree : T.IsTree
  /-- For each tree edge `uv`, the side of `T - uv` containing `u` is a minimum `u`–`v` cut. -/
  isMinCutBetween_edgeSide : ∀ ⦃u v : V⦄, T.Adj u v → IsMinCutBetween f u v (edgeSide T u v)

/-- **Minimum cuts along a Gomory–Hu tree path.** For distinct `s` and `t`, some dart of the
`s`–`t` path in a Gomory–Hu tree has a side that is a minimum `s`–`t` cut. -/
theorem IsGomoryHuTree.exists_isMinCutBetween_of_isPath [Fintype V] [LinearOrder β]
    {f : Finset V → β} {T : SimpleGraph V} (hT : IsGomoryHuTree f T) {s t : V} (hst : s ≠ t)
    {p : T.Walk s t} (hp : p.IsPath) :
    ∃ d ∈ p.darts, IsMinCutBetween f s t (edgeSide T d.fst d.snd) := by
  obtain ⟨X, hX⟩ := exists_isMinCutBetween f hst
  obtain ⟨d, hd, h1, h2⟩ := p.exists_boundary_dart (X : Set V) hX.left_mem hX.right_notMem
  obtain ⟨hs, ht⟩ := mem_edgeSide_of_mem_darts hT.isTree.isAcyclic hp hd
  exact ⟨d, hd, hs, ht, fun Y hsY htY =>
    ((hT.isMinCutBetween_edgeSide d.adj).le h1 h2).trans (hX.le hsY htY)⟩

end Cslib.Algorithms.Lean.GomoryHu
