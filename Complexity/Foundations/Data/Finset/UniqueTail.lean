/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib)

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# At most one selected tail of a nonnegative finite sum

If at most one index is selected, summing the selected tails counts each nonnegative summand
at most once. This pointwise fact needs no probabilistic independence. Its compression
consumer uses uniqueness of the actual first-overflow index.
-/

public section

namespace Finset

/-- If at most one starting index is selected, its nonnegative tail is bounded by the full sum.
The endpoint `m` is excluded from both sums. -/
theorem sum_ite_Ico_le_sum_range {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]
    (m : ℕ) (P : ℕ → Prop) [DecidablePred P] {f : ℕ → M} (hf : ∀ i < m, 0 ≤ f i)
    (hunique : ∀ j < m, ∀ k < m, P j → P k → j = k) :
    (∑ j ∈ range m, if P j then ∑ i ∈ Ico j m, f i else 0) ≤ ∑ i ∈ range m, f i := by
  have htail (j : ℕ) : (∑ i ∈ Ico j m, f i) ≤ ∑ i ∈ range m, f i :=
    sum_le_sum_of_subset_of_nonneg
      (fun i hi => mem_range.mpr (mem_Ico.mp hi).2)
      (fun i hi _ => hf i (mem_range.mp hi))
  calc
    _ ≤ ∑ j ∈ range m, if P j then ∑ i ∈ range m, f i else 0 := by
      refine sum_le_sum fun j _ => ?_
      split_ifs
      · exact htail j
      · exact le_rfl
    _ ≤ ∑ i ∈ range m, f i := by
      rw [sum_ite_zero (range m) P
        (fun j hj k hk => hunique j (mem_range.mp hj) k (mem_range.mp hk))]
      split_ifs
      · exact le_rfl
      · exact sum_nonneg fun i hi => hf i (mem_range.mp hi)

end Finset
