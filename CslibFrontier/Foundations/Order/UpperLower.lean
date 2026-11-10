/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Order/UpperLower/Basic.lean)

public import CslibFrontier.Init
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# Indicators of lower sets

In a preorder, a lower set `A` is closed downward: if `r ≤ s` and `s ∈ A`, then `r ∈ A`. When the
codomain has `0 ≤ 1`, the indicator `A.indicator 1` is therefore antitone
(`IsLowerSet.antitone_indicator_one`).

## Main results

* `IsLowerSet.antitone_indicator_one`: the indicator of a lower set with value `1` is antitone.
-/

public section

namespace IsLowerSet

/-- The indicator of a lower set is antitone. -/
theorem antitone_indicator_one {α β : Type*} [Preorder α] [Zero β] [One β] [Preorder β]
    [ZeroLEOneClass β] {A : Set α} (hA : IsLowerSet A) : Antitone (A.indicator (1 : α → β)) := by
  intro r s hrs
  by_cases hs : s ∈ A
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hA hrs hs)]
    exact le_rfl
  · rw [Set.indicator_of_notMem hs]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) r

end IsLowerSet
