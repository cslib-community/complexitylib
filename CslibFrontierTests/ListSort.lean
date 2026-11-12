/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.Sort

/-!
# Tests for sorted-list insertion, erasure, and rank splitting lemmas

Exercises `List.Pairwise.orderedInsert_eq_take_append_drop`,
`List.Pairwise.erase_eq_take_append_drop`, and `List.Pairwise.getElem_lt_iff_lt_countP` across
empty lists, duplicate runs, boundary positions, and polymorphic linear orders.
-/

public section

namespace CslibFrontierTests.ListSort

/-! ### Concrete instances with duplicates and boundary ranks -/

/-- Inserting a duplicate key `3` into `[1, 3, 3, 5]` splits at rank `countP (· < 3) = 1`,
placing the new copy immediately after `[1]` and before `[3, 3, 5]`. -/
example :
    let l : List ℕ := [1, 3, 3, 5]
    l.orderedInsert (· ≤ ·) 3 = l.take (l.countP (· < 3)) ++ 3 :: l.drop (l.countP (· < 3)) ∧
      l.countP (· < 3) = 1 :=
  ⟨(by decide : ([1, 3, 3, 5] : List ℕ).Pairwise (· ≤ ·)).orderedInsert_eq_take_append_drop 3,
    rfl⟩

/-- Inserting above the maximum of `[1, 3, 3, 5]` appends at rank `4 = l.length`. -/
example :
    let l : List ℕ := [1, 3, 3, 5]
    l.orderedInsert (· ≤ ·) 9 = l.take (l.countP (· < 9)) ++ [9] :=
  ((by decide : ([1, 3, 3, 5] : List ℕ).Pairwise (· ≤ ·)).orderedInsert_eq_take_append_drop 9).trans
    rfl

/-- Erasing `3` from `[1, 3, 3, 5]` drops the first occurrence at index `countP (· < 3) = 1`,
retaining the remaining copy of `3`. -/
example :
    let l : List ℕ := [1, 3, 3, 5]
    l.erase 3 = l.take (l.countP (· < 3)) ++ l.drop (l.countP (· < 3) + 1) ∧
      l.erase 3 = [1, 3, 5] :=
  ⟨(by decide : ([1, 3, 3, 5] : List ℕ).Pairwise (· ≤ ·)).erase_eq_take_append_drop (by decide),
    rfl⟩

/-- Rank characterization distinguishes indices strictly below a duplicate block (`i < 2`) from
the first index of the block (`i = 2`). -/
example :
    let l : List ℕ := [1, 2, 4, 4, 7]
    (l[1] < 4 ∧ 1 < l.countP (· < 4)) ∧ (¬ l[2] < 4 ∧ ¬ 2 < l.countP (· < 4)) := by
  have hl : ([1, 2, 4, 4, 7] : List ℕ).Pairwise (· ≤ ·) := by decide
  have h1 := hl.getElem_lt_iff_lt_countP (i := 1) (by decide) (a := 4)
  have h2 := hl.getElem_lt_iff_lt_countP (i := 2) (by decide) (a := 4)
  exact ⟨⟨by decide, h1.mp (by decide)⟩, ⟨by decide, mt h2.mpr (by decide)⟩⟩

/-! ### Polymorphic client derivations over an arbitrary `LinearOrder` -/

/-- The entry inserted into a sorted list `l` by `orderedInsert (· ≤ ·) a` sits at index
`l.countP (· < a)`. -/
example {α : Type*} [LinearOrder α] {l : List α} (hl : l.Pairwise (· ≤ ·)) (a : α) :
    (l.orderedInsert (· ≤ ·) a)[l.countP (· < a)]? = some a := by
  have hk : (l.take (l.countP (· < a))).length = l.countP (· < a) :=
    List.length_take_of_le List.countP_le_length
  rw [hl.orderedInsert_eq_take_append_drop a, List.getElem?_append_right hk.le]
  simp [hk]

/-- For any `a ∈ l` in a sorted list `l`, `getElem_lt_iff_lt_countP` bounds its rank strictly
below `l.length` and places `a` at `l[l.countP (· < a)]`, while `erase_eq_take_append_drop`
gives `(l.erase a).length + 1 = l.length`. -/
example {α : Type*} [LinearOrder α] {l : List α} (hl : l.Pairwise (· ≤ ·)) {a : α} (ha : a ∈ l) :
    ∃ hk : l.countP (· < a) < l.length,
      l[l.countP (· < a)]'hk = a ∧
        (l.take (l.countP (· < a)) ++ l.drop (l.countP (· < a) + 1)).length + 1 = l.length := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
  have hk_le_i : l.countP (· < a) ≤ i := by
    have hnot : ¬ i < l.countP (· < a) :=
      mt (hl.getElem_lt_iff_lt_countP hi).mpr (hia ▸ lt_irrefl _)
    omega
  have hk : l.countP (· < a) < l.length := lt_of_le_of_lt hk_le_i hi
  refine ⟨hk, le_antisymm ?_ ?_, ?_⟩
  · rcases eq_or_lt_of_le hk_le_i with heq | hlt
    · simp only [heq, hia, le_refl]
    · exact hia ▸ List.pairwise_iff_getElem.mp hl _ _ hk hi hlt
  · exact not_lt.mp (mt (hl.getElem_lt_iff_lt_countP hk).mp (lt_irrefl _))
  · rw [← hl.erase_eq_take_append_drop ha, List.length_erase_of_mem ha]
    exact Nat.sub_add_cancel (List.length_pos_of_mem ha)

end CslibFrontierTests.ListSort
