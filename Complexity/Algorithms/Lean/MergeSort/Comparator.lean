/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.MergeSort.MergeSort
import all Cslib.Algorithms.Lean.Sort.Merge

/-!
# Comparison counts of merge sort with any comparator

CSLib bounds the comparisons of `Cslib.Algorithms.Lean.TimeM.mergeSort`, which compares with `≤`
in a linear order. Clients that sort by a key, such as symbols by weight or edges by weight, call
`List.mergeSortM` with their own comparator. This file gives the same bounds for any comparator
`le : α → α → TimeM ℕ Bool` that costs at most one tick per call: merging takes at most
`xs.length + ys.length` ticks, and merge sort at most `n * ⌈log₂ n⌉`.

## Main results

* `Cslib.Algorithms.Lean.TimeM.mergeM_time`: the merge bound.
* `Cslib.Algorithms.Lean.TimeM.mergeSortM_time_le`: merge sort within the recurrence
  `Cslib.Algorithms.Lean.TimeM.timeMergeSortRec`.
* `Cslib.Algorithms.Lean.TimeM.mergeSortM_time`: merge sort within `n * ⌈log₂ n⌉` ticks.
-/

public section

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type}

/-- Merging with a comparator that costs at most one tick per call takes at most
`xs.length + ys.length` ticks. -/
theorem mergeM_time (xs ys : List α) (le : α → α → TimeM ℕ Bool)
    (hle : ∀ x y, (le x y).time ≤ 1) :
    (List.mergeM xs ys le).time ≤ xs.length + ys.length := by
  fun_induction List.mergeM xs ys le with grind

/-- Merge sort with a comparator that costs at most one tick per call stays within the
merge-sort recurrence `timeMergeSortRec`. -/
theorem mergeSortM_time_le (xs : List α) (le : α → α → TimeM ℕ Bool)
    (hle : ∀ x y, (le x y).time ≤ 1) :
    (List.mergeSortM xs le).time ≤ timeMergeSortRec xs.length := by
  fun_induction List.mergeSortM xs le with
  | case1 | case2 => grind [timeMergeSortRec]
  | case3 _ _ _ lr ih₂ ih₁ =>
    simp only [time_bind]
    have hm : (List.mergeM ⟪List.mergeSortM lr.1 le⟫ ⟪List.mergeSortM lr.2 le⟫ le).time ≤
        lr.1.1.length + lr.2.1.length := by
      refine (mergeM_time _ _ le hle).trans_eq ?_
      simp [ret_mergeSortM]
    unfold timeMergeSortRec
    grind

/-- Merge sort with a comparator that costs at most one tick per call takes at most
`n * ⌈log₂ n⌉` ticks on a list of length `n`. -/
theorem mergeSortM_time (xs : List α) (le : α → α → TimeM ℕ Bool)
    (hle : ∀ x y, (le x y).time ≤ 1) :
    (List.mergeSortM xs le).time ≤ xs.length * Nat.clog 2 xs.length :=
  (mergeSortM_time_le xs le hle).trans (timeMergeSortRec_le xs.length)

end Cslib.Algorithms.Lean.TimeM
