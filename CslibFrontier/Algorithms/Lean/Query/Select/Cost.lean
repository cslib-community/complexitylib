/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Select.Correctness
public import CslibFrontier.Algorithms.Lean.Query.Sort.Merge.CountBound
public import Cslib.Algorithms.Lean.Query.Bounds
import all CslibFrontier.Algorithms.Lean.Query.Select.Defs

/-!
# A linear comparison bound for deterministic selection

`Cslib.Query.select k xs` makes at most `37 * xs.length` comparisons, for every oracle
(`Cslib.Query.select_upperBound`). The proof solves the median-of-medians recurrence
`T(n) ≤ 8n/5 + T(⌈n/5⌉) + 2n + T(selectSideBound n)` by strong induction on `n`:

* each group of at most five elements is sorted with at most `8` comparisons, so computing the
  medians takes at most `8n/5` comparisons (`Cslib.Query.medians_countQueries_le`);
* the three-way partition takes at most `2n` comparisons
  (`Cslib.Query.partition3_countQueries_le`);
* the recursive calls are on the `⌈n/5⌉` medians and on one side of the partition, which has at
  most `selectSideBound n ≤ 7n/10 + 2` elements (checked by `select` itself, so the bound holds
  for every oracle, not only for those implementing a total preorder);
* lists of at most `selectCutoff = 730` elements are merge-sorted with at most
  `n * ⌈log₂ n⌉ ≤ 10n` comparisons.

The constant `37` is what this simple accounting gives; Blum, Floyd, Pratt, Rivest and Tarjan
analyse a refined version of the algorithm (`PICK`) with at most `5.4305n` comparisons
[BlumFloydPrattRivestTarjan1973].

## Main results

* `Cslib.Query.partition3_countQueries_le`: the partition makes at most `2n` comparisons.
* `Cslib.Query.groupMedian_countQueries_le`, `Cslib.Query.medians_countQueries_le`: the group
  medians cost at most `8n/5` comparisons.
* `Cslib.Query.select_countQueries_le`, `Cslib.Query.select_upperBound`: selection makes at most
  `37n` comparisons.

## References

* [M. Blum, R. W. Floyd, V. Pratt, R. L. Rivest and R. E. Tarjan, *Time bounds for
  selection*][BlumFloydPrattRivestTarjan1973].
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.3.
-/

public section

namespace Cslib.Query

variable {α : Type}

/-- The three-way partition makes at most two comparisons per element. -/
theorem partition3_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (p : α)
    (xs : List α) : (partition3 p xs).countQueries oracle ≤ 2 * xs.length := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    rw [partition3]
    rcases hpart : (partition3 p xs).eval oracle with ⟨L, E, G⟩
    simp only [FreeM.countQueries_bind, hpart, LEQuery.ask, FreeM.countQueries_lift,
      FreeM.eval_lift, List.length_cons]
    by_cases h1 : oracle (.le x p) <;> by_cases h2 : oracle (.le p x) <;>
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, FreeM.countQueries_bind,
        FreeM.countQueries_lift, FreeM.eval_lift, FreeM.countQueries_pure] <;>
      omega

/-- The median of a group of `xs.length + 1` elements costs at most
`mergeSortCountBound (xs.length + 1)` comparisons. -/
theorem groupMedian_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (x : α)
    (xs : List α) :
    (groupMedian x xs).countQueries oracle ≤ mergeSortCountBound (xs.length + 1) := by
  simp only [groupMedian, FreeM.countQueries_bind, FreeM.countQueries_pure, Nat.add_zero]
  exact mergeSort_countQueries_le_countBound oracle (x :: xs)

/-- Sorting a group of at most five elements costs at most `8/5` comparisons per element. -/
private theorem five_mul_mergeSortCountBound_le {j : ℕ} (hj : j ≤ 4) :
    5 * mergeSortCountBound (j + 1) ≤ 8 * (j + 1) := by
  rcases j with _ | _ | _ | _ | _ | j
  all_goals first | omega | simp [mergeSortCountBound_add_two]

/-- Computing the group medians costs at most `8/5` comparisons per element:
`5 * cost ≤ 8 * n`. -/
theorem medians_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    5 * (medians xs).countQueries oracle ≤ 8 * xs.length := by
  induction xs using medians.induct with
  | case1 => simp [medians]
  | case2 x xs ih =>
    rw [medians]
    simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, Nat.add_zero]
    have hg := groupMedian_countQueries_le oracle x (xs.take 4)
    have h5 := five_mul_mergeSortCountBound_le (j := (xs.take 4).length) (by simp)
    have htake : (xs.take 4).length + (xs.drop 4).length = xs.length := by simp; omega
    simp only [List.length_cons]
    omega

/-- Lists of at most `selectCutoff` elements are sorted with at most `10` comparisons per
element. -/
private theorem mergeSort_countQueries_le_of_le_selectCutoff
    (oracle : {ι : Type} → LEQuery α ι → ι) {xs : List α} (h : xs.length ≤ selectCutoff) :
    (mergeSort xs).countQueries oracle ≤ 10 * xs.length := by
  have hlog : Nat.clog 2 xs.length ≤ 10 :=
    Nat.clog_le_of_le_pow (h.trans (by decide))
  calc (mergeSort xs).countQueries oracle ≤ xs.length * Nat.clog 2 xs.length :=
        mergeSort_countQueries_le oracle xs
    _ ≤ xs.length * 10 := Nat.mul_le_mul_left _ hlog
    _ = 10 * xs.length := Nat.mul_comm _ _

/-- **Linear comparison bound for selection.** For every oracle, `select k xs` makes at most
`37 * xs.length` comparisons. -/
theorem select_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (k : ℕ) (xs : List α) :
    (select k xs).countQueries oracle ≤ 37 * xs.length := by
  induction h : xs.length using Nat.strong_induction_on generalizing k xs with
  | _ n ih =>
  subst h
  by_cases hsmall : xs.length ≤ selectCutoff
  · rw [select, dite_eq_left hsmall]
    simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, Nat.add_zero]
    have := mergeSort_countQueries_le_of_le_selectCutoff oracle hsmall
    omega
  have hmed := medians_countQueries_le oracle xs
  have hMlen : ((medians xs).eval oracle).length = (xs.length + 4) / 5 :=
    length_eval_medians oracle xs
  have hM : ((medians xs).eval oracle).length < xs.length := by
    simp only [selectCutoff] at hsmall
    omega
  have ihM := ih _ hM ((((medians xs).eval oracle).length - 1) / 2)
    ((medians xs).eval oracle) rfl
  rw [select, dite_eq_right hsmall]
  simp only [FreeM.countQueries_bind]
  rw [dite_eq_left hM]
  simp only [FreeM.countQueries_bind]
  rcases hp : (select ((((medians xs).eval oracle).length - 1) / 2)
    ((medians xs).eval oracle)).eval oracle with _ | p
  · simp only [FreeM.countQueries_pure]
    simp only [selectCutoff] at hsmall
    omega
  have hpart := partition3_countQueries_le oracle p xs
  rcases hLEG : (partition3 p xs).eval oracle with ⟨L, E, G⟩
  simp only [FreeM.countQueries_bind, hLEG]
  by_cases hL : L.length ≤ selectSideBound xs.length
  · by_cases hG : G.length ≤ selectSideBound xs.length
    · have hLlt : L.length < xs.length := by
        simp only [selectSideBound, selectCutoff] at hL hsmall
        omega
      have hGlt : G.length < xs.length := by
        simp only [selectSideBound, selectCutoff] at hG hsmall
        omega
      have ihL := ih _ hLlt k L rfl
      have ihG := ih _ hGlt (k - L.length - E.length) G rfl
      rw [dite_eq_left hL, dite_eq_left hG]
      simp only [selectSideBound, selectCutoff] at hL hG hsmall
      split_ifs
      · omega
      · simp only [FreeM.countQueries_pure]
        omega
      · omega
    · rw [dite_eq_left hL, dite_eq_right hG]
      simp only [FreeM.countQueries_pure, selectCutoff] at hsmall ⊢
      omega
  · rw [dite_eq_right hL]
    simp only [FreeM.countQueries_pure, selectCutoff] at hsmall ⊢
    omega

/-- **Linear comparison bound for selection**, as a query upper bound: on lists of length at most
`n`, `select k` makes at most `37 * n` comparisons for every oracle. -/
theorem select_upperBound (k : ℕ) : UpperBound (select (α := α) k) List.length (37 * ·) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left 37 h)
    fun oracle xs => select_countQueries_le oracle k xs

end Cslib.Query
