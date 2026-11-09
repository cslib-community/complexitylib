/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Sort
public import CslibFrontier.Foundations.Data.List.Counting

/-!
# Order statistics of a list

`List.IsOrderStatistic r xs k y` says that `y` is an element of `xs` of rank `k` (counting from
`0`) for a total preorder `r`: at most `k` elements of `xs` lie strictly below `y`, and more than
`k` lie at or below it. With ties, several elements of `xs` can have rank `k`; they are all
`r`-equivalent, and under an antisymmetric order the order statistic is unique and equals the
`k`-th entry of the sorted list.

## Main definitions

* `List.IsOrderStatistic`: `y` is an element of `xs` of rank `k` for `r`.

## Main results

* `List.Pairwise.length_sub_le_countP`, `List.Pairwise.add_one_le_countP`: in a sorted list, an
  element at or below (at or above) the `i`-th entry is at or below (at or above) at least
  `length - i` (`i + 1`) entries.
* `List.isOrderStatistic_getElem_of_perm`: the `k`-th entry of a sorted permutation of `xs` is an
  order statistic of rank `k`.
* `List.IsOrderStatistic.rel`, `List.IsOrderStatistic.unique`: order statistics of the same rank
  are equivalent, and equal under an antisymmetric order.
* `List.isOrderStatistic_iff_mergeSort`: in a linear order, the rank-`k` order statistic is
  `(xs.mergeSort)[k]`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Chapter 9.
-/

public section

namespace List

variable {α : Type*}

/-- `y` is an element of `xs` of rank `k` (counting from `0`) for the relation `r`: at most `k`
elements of `xs` lie strictly below `y`, and more than `k` lie at or below it. For a total
preorder `r`, "strictly below `y`" means `¬ r y x`. -/
structure IsOrderStatistic (r : α → α → Prop) [DecidableRel r] (xs : List α) (k : ℕ) (y : α) :
    Prop where
  /-- The order statistic is an element of the list. -/
  mem : y ∈ xs
  /-- At most `k` elements lie strictly below `y`. -/
  countP_lt_le : xs.countP (fun x => ¬ r y x) ≤ k
  /-- More than `k` elements lie at or below `y`. -/
  lt_countP_le : k < xs.countP (fun x => r x y)

variable {r : α → α → Prop} [DecidableRel r]

/-- An order statistic has rank below the length of the list. -/
theorem IsOrderStatistic.lt_length {xs : List α} {k : ℕ} {y : α}
    (h : xs.IsOrderStatistic r k y) : k < xs.length :=
  h.lt_countP_le.trans_le countP_le_length

/-- In a list sorted by a transitive relation, an element `p` below the `i`-th entry is below
all of the last `length - i` entries. -/
theorem Pairwise.length_sub_le_countP [IsTrans α r] {s : List α} (hs : s.Pairwise r) {i : ℕ}
    (hi : i < s.length) {p : α} (hp : r p s[i]) :
    s.length - i ≤ s.countP (fun x => r p x) := by
  have hdrop : (s.drop i).countP (fun x => r p x) = s.length - i := by
    rw [countP_eq_length.mpr, length_drop]
    intro x hx
    rw [drop_eq_getElem_cons hi, mem_cons] at hx
    rcases hx with rfl | hx
    · simpa using hp
    · have hpair : (s.drop i).Pairwise r := hs.sublist (drop_sublist _ _)
      rw [drop_eq_getElem_cons hi, pairwise_cons] at hpair
      simpa using _root_.trans hp (hpair.1 x hx)
  rw [← hdrop]
  exact (drop_sublist _ _).countP_le

/-- In a list sorted by a transitive relation, an element `p` above the `i`-th entry is above
all of the first `i + 1` entries. -/
theorem Pairwise.add_one_le_countP [IsTrans α r] {s : List α} (hs : s.Pairwise r) {i : ℕ}
    (hi : i < s.length) {p : α} (hp : r s[i] p) :
    i + 1 ≤ s.countP (fun x => r x p) := by
  have htake : (s.take (i + 1)).countP (fun x => r x p) = i + 1 := by
    rw [countP_eq_length.mpr, length_take]
    · omega
    intro x hx
    rw [mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [length_take] at hj
    rw [getElem_take]
    rcases Nat.lt_or_ge j i with hji | hji
    · have := pairwise_iff_getElem.mp hs j i (by omega) hi hji
      simpa using _root_.trans this hp
    · have hji' : j = i := by omega
      subst hji'
      simpa using hp
  rw [← htake]
  exact (take_sublist _ _).countP_le

/-- The `k`-th entry of a sorted permutation of `xs` is an order statistic of rank `k`. -/
theorem isOrderStatistic_getElem_of_perm [Std.Total r] [IsTrans α r] {xs s : List α}
    (hperm : s.Perm xs) (hs : s.Pairwise r) {k : ℕ} (hk : k < s.length) :
    xs.IsOrderStatistic r k s[k] where
  mem := hperm.subset (getElem_mem hk)
  countP_lt_le := by
    rw [← hperm.countP_eq]
    have hrefl : r s[k] s[k] := (Std.Total.total s[k] s[k]).elim id id
    have h := hs.length_sub_le_countP hk hrefl
    have hsum := s.length_eq_countP_add_countP (fun x => decide (r s[k] x))
    simp only [Bool.decide_eq_true, decide_not] at hsum ⊢
    omega
  lt_countP_le := by
    rw [← hperm.countP_eq]
    have hrefl : r s[k] s[k] := (Std.Total.total s[k] s[k]).elim id id
    have h := hs.add_one_le_countP hk hrefl
    omega

/-- Two order statistics of the same rank are related, so under a total preorder they are
equivalent. -/
theorem IsOrderStatistic.rel [IsTrans α r] {xs : List α} {k : ℕ} {y y' : α}
    (h : xs.IsOrderStatistic r k y) (h' : xs.IsOrderStatistic r k y') : r y y' := by
  by_contra hyy
  -- Everything at or below `y'` is strictly below `y`.
  have hle : xs.countP (fun x => r x y') ≤ xs.countP (fun x => ¬ r y x) := by
    refine countP_mono_left fun x _ hx => ?_
    simp only [decide_eq_true_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hx ⊢
    exact fun hyx => hyy (_root_.trans hyx hx)
  have := h'.lt_countP_le
  have := h.countP_lt_le
  omega

/-- Under an antisymmetric transitive relation, order statistics are unique. -/
theorem IsOrderStatistic.unique [IsTrans α r] [Std.Antisymm r] {xs : List α} {k : ℕ}
    {y y' : α} (h : xs.IsOrderStatistic r k y) (h' : xs.IsOrderStatistic r k y') : y = y' :=
  Std.Antisymm.antisymm _ _ (h.rel h') (h'.rel h)

/-- An order statistic of `xs.filter q` is an order statistic of `xs` of the same rank when every
element of `xs` strictly below it satisfies `q`. -/
theorem IsOrderStatistic.of_filter {q : α → Prop} [DecidablePred q] {xs : List α} {k : ℕ}
    {y : α} (h : (xs.filter (fun x => q x)).IsOrderStatistic r k y)
    (hq : ∀ x ∈ xs, ¬ r y x → q x) : xs.IsOrderStatistic r k y where
  mem := (mem_filter.mp h.mem).1
  countP_lt_le := by
    have h1 := h.countP_lt_le
    rw [countP_filter] at h1
    refine le_of_eq_of_le (countP_congr fun x hx => ?_) h1
    simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, decide_eq_true_eq, iff_self_and]
    exact hq x hx
  lt_countP_le := h.lt_countP_le.trans_le (filter_sublist).countP_le

/-- An order statistic of `xs.filter q` is an order statistic of `xs` whose rank is shifted by
the number of rejected elements, when every rejected element is at or below it. -/
theorem IsOrderStatistic.of_filter_add {q : α → Prop} [DecidablePred q] {xs : List α} {k : ℕ}
    {y : α} (h : (xs.filter (fun x => q x)).IsOrderStatistic r k y)
    (hq : ∀ x ∈ xs, ¬ q x → r x y) :
    xs.IsOrderStatistic r (k + xs.countP (fun x => ¬ q x)) y where
  mem := (mem_filter.mp h.mem).1
  countP_lt_le := by
    have h1 := h.countP_lt_le
    rw [countP_filter] at h1
    have hsplit := countP_and_not_add_countP_and (fun x => ¬ r y x) (fun x => q x) xs
    have hmono : xs.countP (fun x => ¬ q x ∧ ¬ r y x) ≤ xs.countP (fun x => ¬ q x) :=
      countP_mono_left fun x _ hx => by simp_all
    have hcongr : xs.countP (fun x => ¬ r y x ∧ q x) =
        xs.countP (fun x => decide (¬ r y x) && decide (q x)) :=
      countP_congr fun x _ => by simp
    omega
  lt_countP_le := by
    have h1 := h.lt_countP_le
    rw [countP_filter] at h1
    have hsplit := countP_and_not_add_countP_and (fun x => r x y) (fun x => q x) xs
    have hcongr₁ : xs.countP (fun x => ¬ q x ∧ r x y) = xs.countP (fun x => ¬ q x) :=
      countP_congr fun x hx => by
        simp only [decide_eq_true_eq, and_iff_left_iff_imp]
        exact hq x hx
    have hcongr₂ : xs.countP (fun x => r x y ∧ q x) =
        xs.countP (fun x => decide (r x y) && decide (q x)) :=
      countP_congr fun x _ => by simp
    omega

/-- In a linear order, the rank-`k` order statistic of `xs` is the `k`-th entry of
`xs.mergeSort`. -/
theorem isOrderStatistic_iff_mergeSort {β : Type*} [LinearOrder β] {xs : List β} {k : ℕ}
    {y : β} : xs.IsOrderStatistic (· ≤ ·) k y ↔ xs.mergeSort[k]? = some y := by
  have hperm : (xs.mergeSort).Perm xs := mergeSort_perm xs _
  have hsorted : (xs.mergeSort).Pairwise (· ≤ ·) := by
    simpa using pairwise_mergeSort' (· ≤ ·) xs
  constructor
  · intro h
    have hk : k < xs.mergeSort.length := by
      rw [hperm.length_eq]
      exact h.lt_length
    rw [getElem?_eq_getElem hk, Option.some_inj]
    exact (isOrderStatistic_getElem_of_perm hperm hsorted hk).unique h
  · intro h
    obtain ⟨hk, rfl⟩ := getElem?_eq_some_iff.mp h
    exact isOrderStatistic_getElem_of_perm hperm hsorted hk

end List
