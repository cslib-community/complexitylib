/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.WeightedCut.MinCutBetween
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Real-valued capacities for weighted cuts

This module extends the minimum cut theory to real-valued capacities (and more generally,
any linearly ordered field `K`).

## Main definitions
* `Cslib.WeightedCut.realCutWeight`: the weight of a cut in a graph with real capacities.
* `Cslib.WeightedCut.minRealCutBetween`: the minimum `s`–`t` cut weight with real capacities.

## Main results
* `Cslib.WeightedCut.realCutWeight_union_add_realCutWeight_inter_le`: submodularity.
* `Cslib.WeightedCut.realCutWeight_sdiff_add_realCutWeight_sdiff_le`: posimodularity.
* `Cslib.WeightedCut.exists_realCutWeight_eq_minRealCutBetween`: cut value attainment.
* `Cslib.WeightedCut.minRealCutBetween_comm`: symmetry of minimum cut.
-/

public section

namespace Cslib.WeightedCut

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The real-valued weight of a cut. -/
def realCutWeight (W : V → V → K) (C : Finset V) : K :=
  ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, W u v

/-- The weight of the complement `Xᶜ` of a cut of a multigraph is the weight of `X`. -/
theorem realCutWeight_compl {W : V → V → K} (hW : ∀ u v, W u v = W v u) (C : Finset V) :
    realCutWeight W (Finset.univ \ C) = realCutWeight W C := by
  unfold realCutWeight
  have hsdiff : Finset.univ \ (Finset.univ \ C) = C := by ext x; simp
  rw [hsdiff, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hW v u

theorem realCutWeight_compl' {W : V → V → K} (hW : ∀ u v, W u v = W v u) (X : Finset V) :
    realCutWeight W Xᶜ = realCutWeight W X := by
  rw [Finset.compl_eq_univ_sdiff, realCutWeight_compl hW]

/-- The cut function is submodular: `w(δ(A ∪ B)) + w(δ(A ∩ B)) ≤ w(δ(A)) + w(δ(B))`. Symmetry of
`W` is not needed, provided weights are non-negative. -/
theorem realCutWeight_union_add_realCutWeight_inter_le (W : V → V → K) (hW : ∀ u v, 0 ≤ W u v)
    (A B : Finset V) :
    realCutWeight W (A ∪ B) + realCutWeight W (A ∩ B) ≤ realCutWeight W A + realCutWeight W B := by
  have key : ∀ C : Finset V, realCutWeight W C =
      ∑ u, ∑ v, if u ∈ C ∧ v ∉ C then W u v else 0 := by
    intro C
    unfold realCutWeight
    calc ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, W u v
        = ∑ u ∈ C, ∑ v, if v ∉ C then W u v else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      _ = ∑ u, if u ∈ C then ∑ v, (if v ∉ C then W u v else 0) else 0 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
          refine Finset.sum_congr rfl fun u _ => ?_
          by_cases hu : u ∈ C
          · simp only [hu, ite_true, true_and]
          · simp only [hu, ite_false, false_and, Finset.sum_const_zero]
  rw [key, key, key, key, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases huA : u ∈ A <;> by_cases huB : u ∈ B <;> by_cases hvA : v ∈ A <;>
    by_cases hvB : v ∈ B <;> simp [huA, huB, hvA, hvB] <;> (try rfl) <;> (try apply hW)

/-- The cut function of a multigraph is posimodular:
`w(δ(A \ B)) + w(δ(B \ A)) ≤ w(δ(A)) + w(δ(B))`. -/
theorem realCutWeight_sdiff_add_realCutWeight_sdiff_le {W : V → V → K} (hWs : ∀ u v, W u v = W v u)
    (hWn : ∀ u v, 0 ≤ W u v) (A B : Finset V) :
    realCutWeight W (A \ B) + realCutWeight W (B \ A) ≤ realCutWeight W A + realCutWeight W B := by
  have h := realCutWeight_union_add_realCutWeight_inter_le W hWn A Bᶜ
  rw [realCutWeight_compl' hWs B, ← Finset.sdiff_eq_inter_compl] at h
  have hu : A ∪ Bᶜ = (B \ A)ᶜ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  rw [hu, realCutWeight_compl' hWs] at h
  rwa [add_comm (realCutWeight W (A \ B))]

def minCutBetweenSet (W : V → V → K) (s t : V) : Finset K :=
  Finset.image (fun X => realCutWeight W X) (Finset.filter (fun X => s ∈ X ∧ t ∉ X) Finset.univ)

theorem minCutBetweenSet_nonempty (W : V → V → K) {s t : V} (hst : s ≠ t) :
    (minCutBetweenSet W s t).Nonempty := by
  use realCutWeight W {s}
  unfold minCutBetweenSet
  rw [Finset.mem_image]
  use {s}
  simp [Ne.symm hst]

/-- The minimum `s`–`t` cut weight `λ(s, t)` of a weighted multigraph `W`: the least weight of a
vertex set containing `s` and missing `t`, and `0` when `s = t`. -/
noncomputable def minRealCutBetween (W : V → V → K) (s t : V) : K :=
  if hst : s = t then 0
  else (minCutBetweenSet W s t).min' (minCutBetweenSet_nonempty W hst)

theorem exists_realCutWeight_eq_minRealCutBetween (W : V → V → K) {s t : V} (hst : s ≠ t) :
    ∃ X : Finset V, s ∈ X ∧ t ∉ X ∧ realCutWeight W X = minRealCutBetween W s t := by
  rw [minRealCutBetween]
  split_ifs with h
  · exact (hst h).elim
  · have hmem := Finset.min'_mem (minCutBetweenSet W s t) (minCutBetweenSet_nonempty W hst)
    unfold minCutBetweenSet at hmem
    rcases Finset.mem_image.mp hmem with ⟨X, hX, hXeq⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    exact ⟨X, hX.1, hX.2, hXeq⟩

theorem minRealCutBetween_le_realCutWeight (W : V → V → K) {s t : V} {X : Finset V} (hs : s ∈ X)
    (ht : t ∉ X) : minRealCutBetween W s t ≤ realCutWeight W X := by
  rw [minRealCutBetween]
  split_ifs with hst
  · rcases hst with rfl
    exact (ht hs).elim
  · have hmem : realCutWeight W X ∈ minCutBetweenSet W s t := by
      unfold minCutBetweenSet
      rw [Finset.mem_image]
      use X
      simp [hs, ht]
    exact Finset.min'_le _ _ hmem

@[simp]
theorem minRealCutBetween_self (W : V → V → K) (s : V) : minRealCutBetween W s s = 0 := by
  rw [minRealCutBetween]
  split_ifs with h
  · rfl
  · exact (h rfl).elim

theorem le_minRealCutBetween_iff (W : V → V → K) {s t : V} (hst : s ≠ t) (m : K) :
    m ≤ minRealCutBetween W s t ↔ ∀ X : Finset V, s ∈ X → t ∉ X → m ≤ realCutWeight W X := by
  constructor
  · intro hm X hs ht
    exact hm.trans (minRealCutBetween_le_realCutWeight W hs ht)
  · intro h
    obtain ⟨X, hs, ht, hX⟩ := exists_realCutWeight_eq_minRealCutBetween W hst
    exact hX ▸ h X hs ht

theorem minRealCutBetween_comm {W : V → V → K} (hW : ∀ u v, W u v = W v u) (s t : V) :
    minRealCutBetween W s t = minRealCutBetween W t s := by
  by_cases hst : s = t
  · rw [hst]
  · apply le_antisymm
    · rw [le_minRealCutBetween_iff _ (Ne.symm hst)]
      intro X ht hs
      have hX_s : s ∈ Finset.univ \ X := by simp [hs]
      have hX_t : t ∉ Finset.univ \ X := by simp [ht]
      exact (minRealCutBetween_le_realCutWeight W hX_s hX_t).trans_eq (realCutWeight_compl hW X)
    · rw [le_minRealCutBetween_iff _ hst]
      intro X hs ht
      have hX_t : t ∈ Finset.univ \ X := by simp [ht]
      have hX_s : s ∉ Finset.univ \ X := by simp [hs]
      exact (minRealCutBetween_le_realCutWeight W hX_t hX_s).trans_eq (realCutWeight_compl hW X)

theorem min_le_minRealCutBetween (W : V → V → K) {u w : V} (huw : u ≠ w) (v : V) :
    min (minRealCutBetween W u v) (minRealCutBetween W v w) ≤ minRealCutBetween W u w := by
  obtain ⟨X, hu, hw, hX⟩ := exists_realCutWeight_eq_minRealCutBetween W huw
  rw [← hX]
  by_cases hv : v ∈ X
  · exact (min_le_right _ _).trans (minRealCutBetween_le_realCutWeight W hv hw)
  · exact (min_le_left _ _).trans (minRealCutBetween_le_realCutWeight W hu hv)

end Cslib.WeightedCut
