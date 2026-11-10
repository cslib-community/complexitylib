/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas
-- `import all` only for the functional induction principles `List.mergeM.induct` and
-- `List.mergeSortM.induct`; CSLib does not expose the bodies of these definitions.
import all Cslib.Algorithms.Lean.Sort.Merge

/-!
# A sharper comparison bound for merge sort

CSLib bounds the comparisons of `Cslib.Query.mergeSort` by `n * ⌈log₂ n⌉`, charging
`xs.length + ys.length` comparisons to each merge. A merge of two nonempty lists in fact stops
after at most `xs.length + ys.length - 1` comparisons, because the last element is placed without
one. This file records that sharper merge bound and the recurrence it gives for merge sort. For
short lists the difference is substantial: five elements take at most `8` comparisons rather than
`15`, which is what the median-of-medians selection algorithm pays per group of five.

## Main definitions

* `Cslib.Query.mergeSortCountBound`: the recurrence `C(n) = C(⌈n/2⌉) + C(⌊n/2⌋) + n - 1` for
  `n ≥ 2`, with `C(0) = C(1) = 0`.

## Main results

* `Cslib.Query.merge_countQueries_le_sub_one`: merging takes at most
  `xs.length + ys.length - 1` comparisons.
* `Cslib.Query.mergeSort_countQueries_le_countBound`: merge sort takes at most
  `mergeSortCountBound n` comparisons on a list of length `n`.
* `Cslib.Query.mergeSortCountBound_five`: five elements are sorted with at most `8` comparisons.

## References

* [D. E. Knuth, *The Art of Computer Programming, Volume 3: Sorting and Searching*][Knuth1998],
  Section 5.2.4.
-/

public section

namespace Cslib.Query

variable {α : Type}

/-- Merging two lists takes at most `xs.length + ys.length - 1` comparisons: when one list is
empty no comparisons are made, and otherwise the last element is placed without a comparison. -/
theorem merge_countQueries_le_sub_one (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs ys : List α) :
    (merge xs ys).countQueries oracle ≤ xs.length + ys.length - 1 := by
  induction xs, ys using List.mergeM.induct (α := α) with
  | case1 ys => simp
  | case2 xs => simp
  | case3 x xs' y ys' ih_true ih_false =>
    simp only [countQueries_merge_cons_cons, List.length_cons]
    split
    · rcases xs' with _ | ⟨x', xs''⟩
      · simp
      · simp only [List.length_cons] at ih_true ⊢; omega
    · rcases ys' with _ | ⟨y', ys''⟩
      · simp
      · simp only [List.length_cons] at ih_false ⊢; omega

/-- The comparison bound of merge sort with the sharper merge bound: `0` for at most one element,
and otherwise the bounds for the two halves plus `n - 1` for the merge. -/
def mergeSortCountBound : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => mergeSortCountBound ((n + 3) / 2) + mergeSortCountBound ((n + 2) / 2) + (n + 1)

@[simp] theorem mergeSortCountBound_zero : mergeSortCountBound 0 = 0 := by
  rw [mergeSortCountBound]

@[simp] theorem mergeSortCountBound_one : mergeSortCountBound 1 = 0 := by
  rw [mergeSortCountBound]

theorem mergeSortCountBound_add_two (n : ℕ) :
    mergeSortCountBound (n + 2) =
      mergeSortCountBound ((n + 3) / 2) + mergeSortCountBound ((n + 2) / 2) + (n + 1) := by
  rw [mergeSortCountBound]

/-- Merge sort of five elements takes at most `8` comparisons. -/
theorem mergeSortCountBound_five : mergeSortCountBound 5 = 8 := by
  simp [mergeSortCountBound_add_two]

/-- Merge sort takes at most `mergeSortCountBound n` comparisons on a list of length `n`. -/
theorem mergeSort_countQueries_le_countBound (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs : List α) :
    (mergeSort xs).countQueries oracle ≤ mergeSortCountBound xs.length := by
  induction xs using List.mergeSortM.induct (α := α) with
  | case1 => simp [mergeSort]
  | case2 x => simp [mergeSort]
  | case3 x y zs halves ih_l ih_r =>
    subst halves
    simp only [List.splitInTwo_fst, List.splitInTwo_snd] at ih_l ih_r
    simp only [countQueries_mergeSort_cons_cons]
    have hml := merge_countQueries_le_sub_one oracle
      ((x :: y :: zs).split.1.mergeSort fun a b => oracle (.le a b))
      ((x :: y :: zs).split.2.mergeSort fun a b => oracle (.le a b))
    rw [List.length_mergeSort, List.length_mergeSort,
        List.split_fst_length_eq, List.split_snd_length_eq] at hml
    rw [List.split_fst_length_eq] at ih_l
    rw [List.split_snd_length_eq] at ih_r
    simp only [List.length_cons] at ih_l ih_r hml ⊢
    rw [show zs.length + 1 + 1 + 1 = zs.length + 3 by omega] at ih_l hml
    rw [show zs.length + 1 + 1 = zs.length + 2 by omega] at ih_r hml ⊢
    rw [mergeSortCountBound]
    omega

end Cslib.Query
