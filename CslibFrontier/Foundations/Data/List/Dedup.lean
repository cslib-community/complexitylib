/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Dedup.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.Dedup

/-!
# Filtering and removing duplicates

`List.dedup` keeps the last copy of each entry. Filtering commutes with it, as lists and not only
as sets: the copies that `dedup` removes are equal to the copy it keeps, so a filter keeps or
removes all of them together.

## Main results

* `List.dedup_filter`: removing duplicates after filtering is filtering after removing duplicates.
-/

public section

namespace List

variable {α : Type*} [DecidableEq α]

/-- Removing duplicates after filtering is filtering after removing duplicates. -/
theorem dedup_filter (p : α → Bool) (l : List α) : (l.filter p).dedup = l.dedup.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a ∈ l <;> by_cases hp : p a
    · rw [filter_cons_of_pos hp, dedup_cons_of_mem (mem_filter.mpr ⟨ha, hp⟩),
        dedup_cons_of_mem ha, ih]
    · rw [filter_cons_of_neg hp, dedup_cons_of_mem ha, ih]
    · rw [filter_cons_of_pos hp, dedup_cons_of_notMem fun h => ha (mem_filter.mp h).1,
        dedup_cons_of_notMem ha, filter_cons_of_pos hp, ih]
    · rw [filter_cons_of_neg hp, dedup_cons_of_notMem ha, filter_cons_of_neg hp, ih]

end List
