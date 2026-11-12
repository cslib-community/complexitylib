/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Sort

/-!
# Insertion, erasure, and rank in sorted lists

In a list `l` sorted by `(· ≤ ·)` over a linear order, the rank `l.countP (· < a)` of `a` gives
the exact split position at which `List.orderedInsert (· ≤ ·) a l` inserts `a` and at which
`l.erase a` removes `a` when `a ∈ l`, and characterizes the indices `i` whose entry satisfies
`l[i] < a`.

## Main results

* `List.Pairwise.orderedInsert_eq_take_append_drop`: in a sorted list, `orderedInsert (· ≤ ·) a l`
  splits `l` at `l.countP (· < a)` into `l.take k ++ a :: l.drop k`.
* `List.Pairwise.erase_eq_take_append_drop`: in a sorted list containing `a`, `l.erase a` splits
  `l` at `k = l.countP (· < a)` into `l.take k ++ l.drop (k + 1)`.
* `List.Pairwise.getElem_lt_iff_lt_countP`: in a sorted list, `l[i] < a ↔ i < l.countP (· < a)`.
-/

public section

namespace List

private theorem countP_lt_eq_zero {α : Type*} [LinearOrder α] {l : List α} {a : α}
    (h : ∀ y ∈ l, a ≤ y) : l.countP (· < a) = 0 :=
  countP_eq_zero.mpr fun y hy => by simp [not_lt.mpr (h y hy)]

/-- In a list sorted by `(· ≤ ·)`, `orderedInsert (· ≤ ·) a l` inserts `a` immediately after the
prefix of length `l.countP (· < a)` consisting of elements strictly smaller than `a`. -/
theorem Pairwise.orderedInsert_eq_take_append_drop {α : Type*} [LinearOrder α] {l : List α}
    (hl : l.Pairwise (· ≤ ·)) (a : α) :
    l.orderedInsert (· ≤ ·) a = l.take (l.countP (· < a)) ++ a :: l.drop (l.countP (· < a)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hx, hl'⟩ := pairwise_cons.mp hl
    by_cases hax : a ≤ x
    · simp [hax, not_lt.mpr hax, countP_lt_eq_zero fun y hy => hax.trans (hx y hy)]
    · simp [hax, lt_of_not_ge hax, ih hl']

/-- In a list sorted by `(· ≤ ·)`, erasing a present element `a ∈ l` removes the entry at index
`k = l.countP (· < a)` (the first occurrence of `a`), splitting `l` into
`l.take k ++ l.drop (k + 1)`. -/
theorem Pairwise.erase_eq_take_append_drop {α : Type*} [LinearOrder α] {l : List α}
    (hl : l.Pairwise (· ≤ ·)) {a : α} (ha : a ∈ l) :
    l.erase a = l.take (l.countP (· < a)) ++ l.drop (l.countP (· < a) + 1) := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    obtain ⟨hx, hl'⟩ := pairwise_cons.mp hl
    by_cases hxa : x = a
    · subst hxa
      simp [countP_lt_eq_zero hx]
    · have ha' : a ∈ l := (mem_cons.mp ha).resolve_left (Ne.symm hxa)
      simp [hxa, lt_of_le_of_ne (hx a ha') hxa, ih hl' ha']

/-- In a list sorted by `(· ≤ ·)`, the `i`-th entry is strictly below `a` if and only if `i` lies
below the rank `l.countP (· < a)` of `a`. -/
theorem Pairwise.getElem_lt_iff_lt_countP {α : Type*} [LinearOrder α] {l : List α}
    (hl : l.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < l.length) {a : α} :
    l[i] < a ↔ i < l.countP (· < a) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    obtain ⟨hx, hl'⟩ := pairwise_cons.mp hl
    by_cases hxa : x < a
    · cases i with
      | zero => simp [hxa]
      | succ i => simp [hxa, ih hl' (Nat.lt_of_succ_lt_succ hi)]
    · have hax : a ≤ x := not_lt.mp hxa
      have hall : ∀ y ∈ x :: l, a ≤ y :=
        forall_mem_cons.mpr ⟨hax, fun y hy => hax.trans (hx y hy)⟩
      simp [hxa, countP_lt_eq_zero fun y hy => hax.trans (hx y hy),
        not_lt.mpr (hall _ (getElem_mem hi))]

end List
