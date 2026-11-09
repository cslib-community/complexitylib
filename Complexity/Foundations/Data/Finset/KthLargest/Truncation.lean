/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Finset.KthLargest

/-!
# Upper truncation of zero-padded order statistics

Capping every value at a nonnegative threshold caps the positive-order `k`-th largest value
at the same threshold. Nonnegativity of the cap preserves the zero padding. Input values may
be negative, and the retained cardinality may be smaller than the requested rank.

## Main results

* `Finset.kthLargest_min`: upper truncation commutes with the padded order statistic.
-/

public section

namespace Finset

variable {α R : Type*} [LinearOrder R] [Zero R] {s : Finset α} {k : ℕ} {f : α → R} {t : R}

/-- An upper cap that preserves zero commutes with every positive-order padded rank. -/
theorem kthLargest_min (hk : 0 < k) (ht : 0 ≤ t) :
    kthLargest k s (fun x => min t (f x)) = min t (kthLargest k s f) := by
  classical
  apply le_antisymm
  · refine le_min (kthLargest_le ht fun _ _ => min_le_left _ _) ?_
    refine not_lt.mp fun hlt => ?_
    have hc := (lt_kthLargest_iff hk kthLargest_nonneg).mp hlt
    have hs : ({x ∈ s | kthLargest k s f < min t (f x)} : Finset α) ⊆
        {x ∈ s | kthLargest k s f < f x} := by
      intro x hx
      exact mem_filter.mpr ⟨(mem_filter.mp hx).1,
        (mem_filter.mp hx).2.trans_le (min_le_right _ _)⟩
    exact lt_irrefl _ ((lt_kthLargest_iff hk kthLargest_nonneg).mpr
      (hc.trans (card_le_card hs)))
  · by_cases hzero : min t (kthLargest k s f) ≤ 0
    · exact hzero.trans kthLargest_nonneg
    have hpos : 0 < min t (kthLargest k s f) := not_le.mp hzero
    apply (le_kthLargest_iff hk hpos).mpr
    have hc := (le_kthLargest_iff hk hpos).mp (min_le_right t (kthLargest k s f))
    apply hc.trans (card_le_card ?_)
    intro x hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1,
      le_min (min_le_left _ _) (mem_filter.mp hx).2⟩

end Finset
