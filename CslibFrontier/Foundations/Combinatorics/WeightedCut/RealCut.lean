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

The cut weight `Cslib.WeightedCut.cutWeight` and its submodularity and posimodularity
(`cutWeight_union_add_cutWeight_inter_le_of_nonneg`,
`cutWeight_sdiff_add_cutWeight_sdiff_le_of_symm`) are shared with the natural-number theory.
This module adds the minimum `s`–`t` cut weight over a linearly ordered field, where the
natural-number `minCutBetween` (an `sInf` over `ℕ`) does not apply.

## Main definitions
* `Cslib.WeightedCut.minRealCutBetween`: the minimum `s`–`t` cut weight, `0` when `s = t`.

## Main results
* `Cslib.WeightedCut.exists_cutWeight_eq_minRealCutBetween`: cut value attainment.
* `Cslib.WeightedCut.minRealCutBetween_comm`: symmetry of the minimum cut for symmetric weights.
* `Cslib.WeightedCut.min_le_minRealCutBetween`: the triangle inequality.
-/

public section

namespace Cslib.WeightedCut

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K]

variable [LinearOrder K]

/-- The weights of the vertex sets containing `s` and missing `t`. -/
def minCutBetweenSet (W : V → V → K) (s t : V) : Finset K :=
  Finset.image (fun X => cutWeight W X) (Finset.filter (fun X => s ∈ X ∧ t ∉ X) Finset.univ)

theorem minCutBetweenSet_nonempty (W : V → V → K) {s t : V} (hst : s ≠ t) :
    (minCutBetweenSet W s t).Nonempty := by
  use cutWeight W {s}
  unfold minCutBetweenSet
  rw [Finset.mem_image]
  use {s}
  simp [Ne.symm hst]

/-- The minimum `s`–`t` cut weight `λ(s, t)` of a weighted multigraph `W`: the least weight of a
vertex set containing `s` and missing `t`, and `0` when `s = t`. -/
noncomputable def minRealCutBetween (W : V → V → K) (s t : V) : K :=
  if hst : s = t then 0
  else (minCutBetweenSet W s t).min' (minCutBetweenSet_nonempty W hst)

theorem exists_cutWeight_eq_minRealCutBetween (W : V → V → K) {s t : V} (hst : s ≠ t) :
    ∃ X : Finset V, s ∈ X ∧ t ∉ X ∧ cutWeight W X = minRealCutBetween W s t := by
  rw [minRealCutBetween]
  split_ifs with h
  · exact (hst h).elim
  · have hmem := Finset.min'_mem (minCutBetweenSet W s t) (minCutBetweenSet_nonempty W hst)
    unfold minCutBetweenSet at hmem
    rcases Finset.mem_image.mp hmem with ⟨X, hX, hXeq⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    exact ⟨X, hX.1, hX.2, hXeq⟩

theorem minRealCutBetween_le_cutWeight (W : V → V → K) {s t : V} {X : Finset V} (hs : s ∈ X)
    (ht : t ∉ X) : minRealCutBetween W s t ≤ cutWeight W X := by
  rw [minRealCutBetween]
  split_ifs with hst
  · rcases hst with rfl
    exact (ht hs).elim
  · have hmem : cutWeight W X ∈ minCutBetweenSet W s t := by
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
    m ≤ minRealCutBetween W s t ↔ ∀ X : Finset V, s ∈ X → t ∉ X → m ≤ cutWeight W X := by
  constructor
  · intro hm X hs ht
    exact hm.trans (minRealCutBetween_le_cutWeight W hs ht)
  · intro h
    obtain ⟨X, hs, ht, hX⟩ := exists_cutWeight_eq_minRealCutBetween W hst
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
      exact (minRealCutBetween_le_cutWeight W hX_s hX_t).trans_eq
        (cutWeight_univ_sdiff_of_symm hW X)
    · rw [le_minRealCutBetween_iff _ hst]
      intro X hs ht
      have hX_t : t ∈ Finset.univ \ X := by simp [ht]
      have hX_s : s ∉ Finset.univ \ X := by simp [hs]
      exact (minRealCutBetween_le_cutWeight W hX_t hX_s).trans_eq
        (cutWeight_univ_sdiff_of_symm hW X)

theorem min_le_minRealCutBetween (W : V → V → K) {u w : V} (huw : u ≠ w) (v : V) :
    min (minRealCutBetween W u v) (minRealCutBetween W v w) ≤ minRealCutBetween W u w := by
  obtain ⟨X, hu, hw, hX⟩ := exists_cutWeight_eq_minRealCutBetween W huw
  rw [← hX]
  by_cases hv : v ∈ X
  · exact (min_le_right _ _).trans (minRealCutBetween_le_cutWeight W hv hw)
  · exact (min_le_left _ _).trans (minRealCutBetween_le_cutWeight W hu hv)

end Cslib.WeightedCut
