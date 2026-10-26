/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Splitting a finite sum of bounded natural weights

If each item has weight at most `M` and the total is at least `2 * k + M`, a subset and its
complement both have weight at least `k`. A first subset reaching `k` overshoots by at most
`M - 1`, leaving enough weight in its complement.

## Main results

* `Finset.exists_subset_sum_ge`: a balanced split of bounded natural-number weights.

## References

* [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*,
  Threshold/Internal/Excess][Schlesinger2026Algebraic]
-/

@[expose] public section

open scoped BigOperators

namespace Finset

/-- **Subset sum.** Items of weight at most `M` with total weight at least `2 * k + M` can be
partitioned into `𝒢 ⊆ 𝓑` and `𝓑 \ 𝒢` each of weight at least `k`. -/
theorem exists_subset_sum_ge {ι : Type*} [DecidableEq ι] (𝓑 : Finset ι) (φ : ι → ℕ)
    (M k : ℕ) (hφ : ∀ b ∈ 𝓑, φ b ≤ M) (htot : 2 * k + M ≤ ∑ b ∈ 𝓑, φ b) :
    ∃ 𝒢 ⊆ 𝓑, k ≤ ∑ b ∈ 𝒢, φ b ∧ k ≤ ∑ b ∈ 𝓑 \ 𝒢, φ b := by
  have key : ∀ 𝓑 : Finset ι, (∀ b ∈ 𝓑, φ b ≤ M) → k ≤ ∑ b ∈ 𝓑, φ b →
      ∃ 𝒢 ⊆ 𝓑, k ≤ ∑ b ∈ 𝒢, φ b ∧ ∑ b ∈ 𝒢, φ b ≤ k + M - 1 := by
    intro 𝓑
    induction 𝓑 using Finset.induction_on with
    | empty =>
      intro _ hk
      rw [sum_empty] at hk
      exact ⟨∅, Subset.refl _, by simpa using hk, by simp⟩
    | insert a t ha ih =>
      intro hφ hk
      rw [sum_insert ha] at hk
      by_cases hkt : k ≤ ∑ b ∈ t, φ b
      · obtain ⟨𝒢, h𝒢, h1, h2⟩ := ih (fun b hb => hφ b (mem_insert_of_mem hb)) hkt
        exact ⟨𝒢, h𝒢.trans (subset_insert _ _), h1, h2⟩
      · refine ⟨insert a t, Subset.refl _, ?_, ?_⟩
        · rw [sum_insert ha]
          exact hk
        · rw [sum_insert ha]
          have := hφ a (mem_insert_self _ _)
          omega
  obtain ⟨𝒢, h𝒢, h1, h2⟩ := key 𝓑 hφ (by omega)
  refine ⟨𝒢, h𝒢, h1, ?_⟩
  have := sum_sdiff (f := φ) h𝒢
  omega

end Finset
