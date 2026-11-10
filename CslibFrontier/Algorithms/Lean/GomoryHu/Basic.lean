/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.EdgeSide
import Mathlib.Data.Fintype.Powerset

/-!
# Gomory–Hu trees of set functions

A set function `f : Finset V → β` on a finite ground set `V` assigns a value to every cut. A set
`X` is a minimum `s`–`t` cut of `f` (`IsMinCutBetween f s t X`) when it contains `s`, misses `t`,
and minimizes `f` among such sets. The cut function `X ↦ w(δ(X))` of an undirected graph with edge
weights `w` is the motivating example; it is symmetric (`f Xᶜ = f X`) and submodular.

A **Gomory–Hu tree** (cut-equivalent tree) of `f` ([GomoryHu1961]; [Schrijver2003],
Section 15.4) is a spanning tree `T` on `V` such that for every tree edge `uv`, the side of `T - uv`
containing `u` is a minimum `u`–`v` cut of `f`. This module defines Gomory–Hu trees, using the
sides of tree edges `SimpleGraph.edgeSide`
(`CslibFrontier.Foundations.Combinatorics.SimpleGraph.EdgeSide`), and proves that for every two
distinct vertices `s, t`, some edge on the `s`–`t` path of a Gomory–Hu tree has a side that is a
minimum `s`–`t` cut. Existence of Gomory–Hu trees for symmetric submodular functions is in
`CslibFrontier.Algorithms.Lean.GomoryHu.Existence`, and the weighted-graph instance in
`CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut`.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.IsMinCutBetween`: `X` is a minimum `s`–`t` cut of `f`.
* `Cslib.Algorithms.Lean.GomoryHu.IsGomoryHuTree`: a spanning tree whose edge sides are minimum
  cuts between the edge's endpoints.

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.exists_isMinCutBetween`: minimum cuts exist between distinct
  elements, for values in a linear order.
* `Cslib.Algorithms.Lean.GomoryHu.IsMinCutBetween.inter`,
  `Cslib.Algorithms.Lean.GomoryHu.IsMinCutBetween.union`,
  `Cslib.Algorithms.Lean.GomoryHu.IsMinCutBetween.sdiff`: uncrossing of minimum cuts for a
  submodular function.
* `Cslib.Algorithms.Lean.GomoryHu.IsGomoryHuTree.exists_isMinCutBetween_of_isPath`: some edge of
  the `s`–`t` path of a Gomory–Hu tree has a side that is a minimum `s`–`t` cut.

## References

* [GomoryHu1961]
* [Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean.Submodular
open SimpleGraph (edgeSide mem_edgeSide_of_mem_darts)

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

/-- **Uncrossing by union.** For a submodular `f`, if `U` is a minimum `s`–`t` cut, `A` is a
minimum `a`–`t` cut and `a ∈ U`, then `U ∪ A` is a minimum `s`–`t` cut too. -/
theorem IsMinCutBetween.union [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    [DecidableEq V] {f : Finset V → β} {s t a : V} {U A : Finset V} (hsub : IsSubmodular f)
    (hU : IsMinCutBetween f s t U) (hA : IsMinCutBetween f a t A) (haU : a ∈ U) :
    IsMinCutBetween f s t (U ∪ A) := by
  have htU : t ∉ U ∪ A := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hU.right_notMem, hA.right_notMem⟩
  refine ⟨Finset.mem_union_left _ hU.left_mem, htU, fun Y hs ht => ?_⟩
  have h1 : f A ≤ f (U ∩ A) :=
    hA.le (Finset.mem_inter.mpr ⟨haU, hA.left_mem⟩)
      (fun h => hA.right_notMem (Finset.mem_inter.mp h).2)
  have h2 : f (U ∪ A) + f (U ∩ A) ≤ f U + f (U ∩ A) :=
    (hsub U A).trans (add_le_add le_rfl h1)
  exact (le_of_add_le_add_right h2).trans (hU.le hs ht)

/-- **Uncrossing by difference.** For a symmetric submodular `f`, if `U` is a minimum `s`–`t`
cut, `A` is a minimum `a`–`t` cut, `a ∉ U` and `s ∉ A`, then `U \ A` is a minimum `s`–`t` cut
too. -/
theorem IsMinCutBetween.sdiff [Fintype V] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedCancelAddMonoid β] [DecidableEq V] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {s t a : V} {U A : Finset V} (hU : IsMinCutBetween f s t U)
    (hA : IsMinCutBetween f a t A) (haU : a ∉ U) (hsA : s ∉ A) :
    IsMinCutBetween f s t (U \ A) := by
  rw [Finset.sdiff_eq_inter_compl]
  exact hU.inter hsub (hA.compl hsym) (Finset.mem_compl.mpr hsA) haU

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
