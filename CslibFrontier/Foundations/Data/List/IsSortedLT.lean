/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Sort

/-!
# A Boolean test for strictly increasing lists

`List.isSortedLT l` checks that each entry of `l` is less than the next, by comparing `l` with its
tail entry by entry. It decides Mathlib's `List.SortedLT` (`List.isSortedLT_iff`). Written with
`zip` and `all`, it is a composition of list primitives whose machine cost is already bounded, so it
is convenient inside polynomial-time certificates.

## Main definitions

* `List.isSortedLT`: whether each entry of a list is less than the next.

## Main results

* `List.isSortedLT_iff`: `List.isSortedLT` decides `List.SortedLT`.
-/

public section

namespace List

variable {α : Type*}

/-- Whether each entry of `l` is less than the next. -/
@[expose] def isSortedLT [LT α] [DecidableLT α] (l : List α) : Bool :=
  (l.zip l.tail).all fun e => decide (e.1 < e.2)

/-- `List.isSortedLT` decides `List.SortedLT`. -/
theorem isSortedLT_iff [Preorder α] [DecidableLT α] (l : List α) :
    l.isSortedLT = true ↔ l.SortedLT := by
  rw [sortedLT_iff_isChain]
  induction l with
  | nil => simp [isSortedLT]
  | cons a l ih =>
    cases l with
    | nil => simp [isSortedLT]
    | cons b l =>
      rw [isChain_cons_cons, ← ih]
      simp only [isSortedLT, tail_cons, zip_cons_cons, all_cons, Bool.and_eq_true,
        decide_eq_true_eq]

end List
