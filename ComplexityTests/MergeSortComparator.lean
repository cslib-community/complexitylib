/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.MergeSort.Comparator

/-!
# Tests for `List.mergeM` and `List.mergeSortM` Custom-Comparator Bounds
-/

public section

namespace ComplexityTests.MergeSortComparator

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TimeM
open scoped Cslib.Algorithms.Lean.TimeM

/-- Unit-cost comparator ordering pairs by their second coordinate. -/
@[expose] def cmpSnd (x y : ℕ × ℕ) : TimeM ℕ Bool := do
  ✓ return decide (x.2 ≤ y.2)

example :
    let m := List.mergeSortM [(1, 30), (2, 10), (3, 20), (4, 10)] cmpSnd
    (List.mergeSortM [(1, 30), (2, 10)] cmpSnd).ret = [(2, 10), (1, 30)] ∧
      m.ret.Perm [(1, 30), (2, 10), (3, 20), (4, 10)] ∧
      m.time ≤ timeMergeSortRec 4 ∧
      m.time ≤ 4 * Nat.clog 2 4 ∧
      (List.mergeM [(2, 10), (3, 20)] [(4, 10), (1, 30)] cmpSnd).time ≤ 2 + 2 := by
  refine ⟨?_, ?_,
    mergeSortM_time_le _ cmpSnd fun _ _ => le_rfl,
    mergeSortM_time _ cmpSnd fun _ _ => le_rfl,
    mergeM_time _ _ cmpSnd fun _ _ => le_rfl⟩
  · simp [cmpSnd]
  · simp only [ret_mergeSortM]
    exact List.mergeSort_perm _ _

end ComplexityTests.MergeSortComparator
