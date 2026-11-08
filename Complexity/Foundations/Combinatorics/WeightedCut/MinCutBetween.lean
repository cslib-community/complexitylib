/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.WeightedCut
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Minimum cuts between two vertices of a weighted multigraph

For a weighted multigraph `W : V → V → ℕ` (`Cslib.WeightedCut.IsMultigraph`) and vertices `s` and
`t`, the minimum `s`–`t` cut weight `λ(s, t) = Cslib.WeightedCut.minCutBetween W s t` is the least
weight `cutWeight W X` of a vertex set `X` containing `s` and missing `t` (and `0` when `s = t`).
By max-flow min-cut it is the value of a maximum `s`–`t` flow; see
`Complexity.Algorithms.Lean.GomoryHu.WeightedCut`.

The cut function `X ↦ cutWeight W X` is submodular, and posimodular when `W` is symmetric. The
values `λ` satisfy the ultrametric triangle inequality `λ(u, w) ≥ min (λ(u, v)) (λ(v, w))`, the
basic fact behind Gomory–Hu trees ([GomoryHu1961]; [Schrijver2003], Section 15.4).

## Main definitions

* `Cslib.WeightedCut.minCutBetween`: the minimum `s`–`t` cut weight `λ(s, t)`.

## Main results

* `Cslib.WeightedCut.exists_cutWeight_eq_minCutBetween`: for `s ≠ t`, some set containing `s` and
  missing `t` has weight `λ(s, t)`.
* `Cslib.WeightedCut.le_minCutBetween_iff`: for `s ≠ t`, `m ≤ λ(s, t)` exactly when every set
  containing `s` and missing `t` weighs at least `m`.
* `Cslib.WeightedCut.minCutBetween_comm`: `λ(s, t) = λ(t, s)` for a multigraph.
* `Cslib.WeightedCut.cutWeight_union_add_cutWeight_inter_le`: submodularity of the cut function.
* `Cslib.WeightedCut.cutWeight_sdiff_add_cutWeight_sdiff_le`: posimodularity of the cut function of
  a multigraph.
* `Cslib.WeightedCut.min_le_minCutBetween`: the triangle inequality
  `min (λ(u, v)) (λ(v, w)) ≤ λ(u, w)`.

## References

* [GomoryHu1961]
* [Schrijver2003]
-/

public section

namespace Cslib.WeightedCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weight of the complement `Xᶜ` of a cut of a multigraph is the weight of `X`. -/
theorem cutWeight_compl' {W : V → V → ℕ} (hW : IsMultigraph W) (X : Finset V) :
    cutWeight W Xᶜ = cutWeight W X := by
  rw [Finset.compl_eq_univ_sdiff, cutWeight_compl hW]

/-- The cut function is submodular: `w(δ(A ∪ B)) + w(δ(A ∩ B)) ≤ w(δ(A)) + w(δ(B))`. Symmetry of
`W` is not needed. -/
theorem cutWeight_union_add_cutWeight_inter_le (W : V → V → ℕ) (A B : Finset V) :
    cutWeight W (A ∪ B) + cutWeight W (A ∩ B) ≤ cutWeight W A + cutWeight W B := by
  have key : ∀ C : Finset V, cutWeight W C =
      ∑ u, ∑ v, if u ∈ C ∧ v ∉ C then W u v else 0 := by
    intro C
    unfold cutWeight
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
    by_cases hvB : v ∈ B <;> simp [huA, huB, hvA, hvB]

/-- The cut function of a multigraph is posimodular:
`w(δ(A \ B)) + w(δ(B \ A)) ≤ w(δ(A)) + w(δ(B))`. -/
theorem cutWeight_sdiff_add_cutWeight_sdiff_le {W : V → V → ℕ} (hW : IsMultigraph W)
    (A B : Finset V) :
    cutWeight W (A \ B) + cutWeight W (B \ A) ≤ cutWeight W A + cutWeight W B := by
  have h := cutWeight_union_add_cutWeight_inter_le W A Bᶜ
  rw [cutWeight_compl' hW B, ← Finset.sdiff_eq_inter_compl] at h
  have hu : A ∪ Bᶜ = (B \ A)ᶜ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  rw [hu, cutWeight_compl' hW] at h
  omega

/-- The minimum `s`–`t` cut weight `λ(s, t)` of a weighted multigraph `W`: the least weight of a
vertex set containing `s` and missing `t`, and `0` when `s = t`. -/
noncomputable def minCutBetween (W : V → V → ℕ) (s t : V) : ℕ :=
  sInf {k | ∃ X : Finset V, s ∈ X ∧ t ∉ X ∧ cutWeight W X = k}

theorem minCutBetween_le_cutWeight (W : V → V → ℕ) {s t : V} {X : Finset V} (hs : s ∈ X)
    (ht : t ∉ X) : minCutBetween W s t ≤ cutWeight W X :=
  Nat.sInf_le ⟨X, hs, ht, rfl⟩

@[simp]
theorem minCutBetween_self (W : V → V → ℕ) (s : V) : minCutBetween W s s = 0 := by
  have : {k | ∃ X : Finset V, s ∈ X ∧ s ∉ X ∧ cutWeight W X = k} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨_, h1, h2, _⟩ => h2 h1
  rw [minCutBetween, this, Nat.sInf_empty]

/-- For distinct `s` and `t`, the minimum `s`–`t` cut weight is attained. -/
theorem exists_cutWeight_eq_minCutBetween (W : V → V → ℕ) {s t : V} (hst : s ≠ t) :
    ∃ X : Finset V, s ∈ X ∧ t ∉ X ∧ cutWeight W X = minCutBetween W s t :=
  Nat.sInf_mem (s := {k | ∃ X : Finset V, s ∈ X ∧ t ∉ X ∧ cutWeight W X = k})
    ⟨_, {s}, Finset.mem_singleton_self s, fun h => hst (Finset.mem_singleton.mp h).symm, rfl⟩

theorem le_minCutBetween_iff (W : V → V → ℕ) {s t : V} (hst : s ≠ t) (m : ℕ) :
    m ≤ minCutBetween W s t ↔ ∀ X : Finset V, s ∈ X → t ∉ X → m ≤ cutWeight W X := by
  constructor
  · intro hm X hs ht
    exact hm.trans (minCutBetween_le_cutWeight W hs ht)
  · intro h
    obtain ⟨X, hs, ht, hX⟩ := exists_cutWeight_eq_minCutBetween W hst
    exact hX ▸ h X hs ht

/-- A set containing `s` and missing `t` is a minimum `s`–`t` cut exactly when its weight is at
most that of every such set. -/
theorem cutWeight_eq_minCutBetween_iff (W : V → V → ℕ) {s t : V} {X : Finset V} (hs : s ∈ X)
    (ht : t ∉ X) :
    cutWeight W X = minCutBetween W s t ↔
      ∀ Y : Finset V, s ∈ Y → t ∉ Y → cutWeight W X ≤ cutWeight W Y := by
  have hst : s ≠ t := fun h => ht (h ▸ hs)
  constructor
  · intro hX Y hsY htY
    exact hX ▸ minCutBetween_le_cutWeight W hsY htY
  · intro h
    exact le_antisymm ((le_minCutBetween_iff W hst _).mpr h) (minCutBetween_le_cutWeight W hs ht)

/-- The minimum cut weight between two vertices of a multigraph is symmetric. -/
theorem minCutBetween_comm {W : V → V → ℕ} (hW : IsMultigraph W) (s t : V) :
    minCutBetween W s t = minCutBetween W t s := by
  have key : ∀ a b : V, minCutBetween W b a ≤ minCutBetween W a b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨X, ha, hb, hX⟩ := exists_cutWeight_eq_minCutBetween W hab
    rw [← hX, ← cutWeight_compl' hW]
    exact minCutBetween_le_cutWeight W (Finset.mem_compl.mpr hb) (fun h => Finset.mem_compl.mp h ha)
  exact le_antisymm (key t s) (key s t)

/-- **Triangle inequality** for minimum cuts ([GomoryHu1961]): for distinct `u` and `w` and any
`v`, `min (λ(u, v)) (λ(v, w)) ≤ λ(u, w)`. A minimum `u`–`w` cut separates `v` from `u` or from
`w`. Symmetry of `W` is not needed. -/
theorem min_le_minCutBetween (W : V → V → ℕ) {u w : V} (huw : u ≠ w) (v : V) :
    min (minCutBetween W u v) (minCutBetween W v w) ≤ minCutBetween W u w := by
  obtain ⟨X, hu, hw, hX⟩ := exists_cutWeight_eq_minCutBetween W huw
  rw [← hX]
  by_cases hv : v ∈ X
  · exact (min_le_right _ _).trans (minCutBetween_le_cutWeight W hv hw)
  · exact (min_le_left _ _).trans (minCutBetween_le_cutWeight W hu hv)

/-- Among the three values `λ(u, v)`, `λ(v, w)`, `λ(u, w)` of a multigraph, the minimum is
attained at least twice: if `λ(u, v) < λ(v, w)` then `λ(u, w) = λ(u, v)`. -/
theorem minCutBetween_eq_of_lt {W : V → V → ℕ} (hW : IsMultigraph W) {u v w : V} (huv : u ≠ v)
    (huw : u ≠ w) (h : minCutBetween W u v < minCutBetween W v w) :
    minCutBetween W u w = minCutBetween W u v := by
  have h1 := min_le_minCutBetween W huw v
  have h2 := min_le_minCutBetween W huv w
  rw [minCutBetween_comm hW w v] at h2
  rw [min_le_iff] at h1 h2
  omega

end Cslib.WeightedCut
