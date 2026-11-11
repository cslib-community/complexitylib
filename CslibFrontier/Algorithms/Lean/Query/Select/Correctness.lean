/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Select.Defs
public import CslibFrontier.Foundations.Data.List.OrderStatistic
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas
import all CslibFrontier.Algorithms.Lean.Query.Select.Defs

/-!
# Correctness of deterministic selection

Against an oracle implementing a total preorder `r`, `Cslib.Query.select k xs` returns an element
of rank `k` of `xs` when `k < xs.length`, and `none` otherwise. For a linear order the result is
`xs.mergeSort[k]?`.

The heart of the argument is the median-of-medians counting bound
(`Cslib.Query.length_filter_lt_le_selectSideBound`): if `p` has rank `⌊(g - 1) / 2⌋` among the
`g = ⌈n / 5⌉` group medians of a list of `n` elements, then at least `3 * ⌊(g - 1) / 2⌋ + 1`
elements lie at or above `p` and as many at or below it, so at most `selectSideBound n` elements
lie strictly on either side. This is the counting step of [CLRS2009], Section 9.3, with the
partial group and the pivot itself accounted exactly.

## Main results

* `Cslib.Query.eval_groupMedian`, `Cslib.Query.eval_partition3`: evaluation of the building
  blocks; `Cslib.Query.eval_partition3_of_total`: against a total preorder, the partition splits
  the list into the elements strictly below, equivalent to, and strictly above the pivot.
* `Cslib.Query.length_eval_medians`, `Cslib.Query.mem_of_mem_eval_medians`: the medians list has
  `⌈n / 5⌉` entries, all from the input.
* `Cslib.Query.three_mul_countP_eval_medians_rel_le`,
  `Cslib.Query.three_mul_countP_eval_medians_rel_le'`: each group median above (below) `p`
  contributes three elements of its group above (below) `p`.
* `Cslib.Query.length_filter_lt_le_selectSideBound`,
  `Cslib.Query.length_filter_gt_le_selectSideBound`: the median-of-medians counting bound.
* `Cslib.Query.select_isOrderStatistic`, `Cslib.Query.eval_select_eq_none`: correctness of
  `select` against a total preorder.
* `Cslib.Query.eval_select_eq_getElem?_mergeSort`: for a linear order, `select k xs` returns
  `xs.mergeSort[k]?`.

## References

* [M. Blum, R. W. Floyd, V. Pratt, R. L. Rivest and R. E. Tarjan, *Time bounds for
  selection*][BlumFloydPrattRivestTarjan1973].
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.3.
-/

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Building blocks -/

/-- The group median is the entry at index `xs.length / 2` of the sorted group. -/
@[simp] theorem eval_groupMedian (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) (xs : List α) :
    (groupMedian x xs).eval oracle =
      ((x :: xs).mergeSort fun a b => oracle (.le a b)).getD (xs.length / 2) x := by
  simp [groupMedian]

/-- The group median is an element of the group. -/
theorem eval_groupMedian_mem (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) (xs : List α) :
    (groupMedian x xs).eval oracle ∈ x :: xs := by
  rw [eval_groupMedian]
  have hperm := List.mergeSort_perm (x :: xs) fun a b => oracle (.le a b)
  have hk : xs.length / 2 < ((x :: xs).mergeSort fun a b => oracle (.le a b)).length := by
    rw [hperm.length_eq, List.length_cons]
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact hperm.subset (List.getElem_mem hk)

/-- Against a total preorder, an element `p` at or below the median of a group of `s` elements is
at or below at least `⌈s / 2⌉` of them, and an element at or above the median is at or above
at least `⌈s / 2⌉` of them. -/
theorem le_countP_of_rel_eval_groupMedian (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (x : α) (xs : List α) (p : α) :
    (r p ((groupMedian x xs).eval oracle) →
      (xs.length + 2) / 2 ≤ (x :: xs).countP (fun y => r p y)) ∧
    (r ((groupMedian x xs).eval oracle) p →
      (xs.length + 2) / 2 ≤ (x :: xs).countP (fun y => r y p)) := by
  have hperm := mergeSort_perm oracle (x :: xs)
  have hsorted := mergeSort_sorted r oracle horacle (x :: xs)
  rw [eval_mergeSort] at hperm hsorted
  have hk : xs.length / 2 < ((x :: xs).mergeSort fun a b => oracle (.le a b)).length := by
    rw [hperm.length_eq, List.length_cons]
    omega
  have hlen : ((x :: xs).mergeSort fun a b => oracle (.le a b)).length = xs.length + 1 := by
    rw [hperm.length_eq, List.length_cons]
  rw [eval_groupMedian, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  constructor
  · intro hp
    have h := hsorted.length_sub_le_countP hk hp
    rw [hperm.countP_eq, hlen] at h
    omega
  · intro hp
    have h := hsorted.add_one_le_countP hk hp
    rw [hperm.countP_eq] at h
    omega

/-- The medians list of a list of `n` elements has `⌈n / 5⌉` entries, for every oracle. -/
@[simp] theorem length_eval_medians (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    ((medians xs).eval oracle).length = (xs.length + 4) / 5 := by
  induction xs using medians.induct with
  | case1 => simp [medians]
  | case2 x xs ih =>
    rw [medians]
    simp only [FreeM.eval_bind, FreeM.eval_pure, List.length_cons, ih, List.length_drop]
    omega

/-- Every group median is an element of the input, for every oracle. -/
theorem mem_of_mem_eval_medians (oracle : {ι : Type} → LEQuery α ι → ι) {xs : List α} {m : α}
    (hm : m ∈ (medians xs).eval oracle) : m ∈ xs := by
  induction xs using medians.induct with
  | case1 => simp [medians] at hm
  | case2 x xs ih =>
    rw [medians] at hm
    simp only [FreeM.eval_bind, FreeM.eval_pure, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact (List.cons_sublist_cons.mpr (List.take_sublist 4 xs)).subset
        (eval_groupMedian_mem oracle x (xs.take 4))
    · exact List.mem_cons_of_mem x ((List.drop_sublist 4 xs).subset (ih hm))

/-- Each group median satisfying `P` contributes `3` elements of its group satisfying `P`, up to
the partial last group. -/
private theorem three_mul_countP_eval_medians_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (P : α → Prop) [DecidablePred P]
    (hgroup : ∀ x xs, P ((groupMedian x xs).eval oracle) →
      (xs.length + 2) / 2 ≤ (x :: xs).countP (fun y => P y))
    (xs : List α) :
    3 * ((medians xs).eval oracle).countP (fun y => P y) ≤ xs.countP (fun y => P y) + 2 := by
  induction xs using medians.induct with
  | case1 => simp [medians]
  | case2 x xs ih =>
    rw [medians]
    simp only [FreeM.eval_bind, FreeM.eval_pure]
    have hsplit : (x :: xs).countP (fun y => P y) =
        (x :: xs.take 4).countP (fun y => P y) + (xs.drop 4).countP (fun y => P y) := by
      conv_lhs => rw [← List.take_append_drop 4 xs]
      rw [← List.cons_append, List.countP_append]
    rw [List.countP_cons (l := (medians (xs.drop 4)).eval oracle), hsplit]
    have hg := hgroup x (xs.take 4)
    by_cases h4 : 4 ≤ xs.length
    · have hlen : (xs.take 4).length = 4 := by simp [h4]
      rw [hlen] at hg
      by_cases hP : P ((groupMedian x (xs.take 4)).eval oracle)
      · have := hg hP
        simp only [hP, decide_true, ↓reduceIte]
        omega
      · simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
        omega
    · have hdrop : xs.drop 4 = [] := List.drop_eq_nil_of_le (by omega)
      have hms : ((medians (xs.drop 4)).eval oracle) = [] := by
        rw [hdrop, medians]
        rfl
      rw [hms]
      by_cases hP : P ((groupMedian x (xs.take 4)).eval oracle)
      · have := hg hP
        simp only [hP, decide_true, ↓reduceIte, List.countP_nil]
        omega
      · simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte, List.countP_nil]
        omega

/-- Each group median at or above `p` contributes three elements of its group at or above `p`:
`3 * #{medians ≥ p} ≤ #{xs ≥ p} + 2`. -/
theorem three_mul_countP_eval_medians_rel_le (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (p : α) (xs : List α) :
    3 * ((medians xs).eval oracle).countP (fun y => r p y) ≤ xs.countP (fun y => r p y) + 2 :=
  three_mul_countP_eval_medians_le oracle (fun y => r p y)
    (fun x xs => (le_countP_of_rel_eval_groupMedian r oracle horacle x xs p).1) xs

/-- Each group median at or below `p` contributes three elements of its group at or below `p`:
`3 * #{medians ≤ p} ≤ #{xs ≤ p} + 2`. -/
theorem three_mul_countP_eval_medians_rel_le' (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (p : α) (xs : List α) :
    3 * ((medians xs).eval oracle).countP (fun y => r y p) ≤ xs.countP (fun y => r y p) + 2 :=
  three_mul_countP_eval_medians_le oracle (fun y => r y p)
    (fun x xs => (le_countP_of_rel_eval_groupMedian r oracle horacle x xs p).2) xs

/-- The three-way partition, as filters by the oracle's answers. -/
@[simp] theorem eval_partition3 (oracle : {ι : Type} → LEQuery α ι → ι) (p : α) (xs : List α) :
    (partition3 p xs).eval oracle =
      (xs.filter (fun x => oracle (.le x p) && !oracle (.le p x)),
        xs.filter (fun x => oracle (.le x p) && oracle (.le p x)),
        xs.filter (fun x => !oracle (.le x p))) := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    rw [partition3]
    simp only [FreeM.eval_bind, ih]
    by_cases h1 : oracle (.le x p) <;> by_cases h2 : oracle (.le p x) <;>
      simp [h1, h2]

/-- Against a total preorder, the three-way partition splits `xs` into the elements strictly below,
equivalent to, and strictly above the pivot. -/
theorem eval_partition3_of_total (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (p : α) (xs : List α) :
    (partition3 p xs).eval oracle =
      (xs.filter (fun x => ¬ r p x), xs.filter (fun x => r x p ∧ r p x),
        xs.filter (fun x => ¬ r x p)) := by
  rw [eval_partition3]
  simp only [horacle, Prod.mk.injEq]
  refine ⟨List.filter_congr fun x _ => ?_, List.filter_congr fun x _ => ?_,
    List.filter_congr fun x _ => ?_⟩
  · by_cases h2 : r p x
    · simp [h2]
    · have h1 : r x p := (Std.Total.total x p).resolve_right h2
      simp [h1, h2]
  · simp
  · simp

/-! ## The median-of-medians counting bound -/

/-- **The median-of-medians counting bound, lower side.** Against a total preorder, if `p` has
rank `⌊(g - 1) / 2⌋` among the `g = ⌈n / 5⌉` group medians of a list of `n` elements, then at most
`selectSideBound n = n - 3 * ⌊(g - 1) / 2⌋ - 1` elements lie strictly below `p`. -/
theorem length_filter_lt_le_selectSideBound (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) {xs : List α} {p : α}
    (hp : ((medians xs).eval oracle).IsOrderStatistic r (((xs.length + 4) / 5 - 1) / 2) p) :
    (xs.filter (fun x => ¬ r p x)).length ≤ selectSideBound xs.length := by
  have h3 := three_mul_countP_eval_medians_rel_le r oracle horacle p xs
  have hlt := hp.countP_lt_le
  have hsumM := ((medians xs).eval oracle).length_eq_countP_add_countP (fun x => decide (r p x))
  have hsum := xs.length_eq_countP_add_countP (fun x => decide (r p x))
  rw [length_eval_medians] at hsumM
  rw [← List.countP_eq_length_filter]
  simp only [Bool.decide_eq_true, decide_not] at hsumM hsum hlt ⊢
  simp only [selectSideBound]
  omega

/-- **The median-of-medians counting bound, upper side.** Against a total preorder, if `p` has
rank `⌊(g - 1) / 2⌋` among the `g = ⌈n / 5⌉` group medians of a list of `n` elements, then at most
`selectSideBound n = n - 3 * ⌊(g - 1) / 2⌋ - 1` elements lie strictly above `p`. -/
theorem length_filter_gt_le_selectSideBound (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) {xs : List α} {p : α}
    (hp : ((medians xs).eval oracle).IsOrderStatistic r (((xs.length + 4) / 5 - 1) / 2) p) :
    (xs.filter (fun x => ¬ r x p)).length ≤ selectSideBound xs.length := by
  have h3 := three_mul_countP_eval_medians_rel_le' r oracle horacle p xs
  have hlt := hp.lt_countP_le
  have hsum := xs.length_eq_countP_add_countP (fun x => decide (r x p))
  rw [← List.countP_eq_length_filter]
  simp only [Bool.decide_eq_true, decide_not] at hsum hlt ⊢
  simp only [selectSideBound]
  omega

/-! ## Correctness of `select` -/

/-- On a short list, `select` sorts and reads off the `k`-th entry. -/
private theorem eval_select_of_le (oracle : {ι : Type} → LEQuery α ι → ι) (k : ℕ) {xs : List α}
    (h : xs.length ≤ selectCutoff) :
    (select k xs).eval oracle = (xs.mergeSort fun a b => oracle (.le a b))[k]? := by
  rw [select, dite_eq_left h]
  simp

/-- On a long list, once the pivot is found and both sides pass the size check, `select` recurses
into the side holding rank `k`. -/
private theorem eval_select_of_lt (oracle : {ι : Type} → LEQuery α ι → ι) (k : ℕ) {xs : List α}
    (hsmall : ¬ xs.length ≤ selectCutoff) {p : α}
    (hp : (select ((((medians xs).eval oracle).length - 1) / 2)
      ((medians xs).eval oracle)).eval oracle = some p)
    {L E G : List α} (hpart : (partition3 p xs).eval oracle = (L, E, G))
    (hL : L.length ≤ selectSideBound xs.length) (hG : G.length ≤ selectSideBound xs.length) :
    (select k xs).eval oracle =
      if k < L.length then (select k L).eval oracle
      else if k < L.length + E.length then some p
      else (select (k - L.length - E.length) G).eval oracle := by
  have hM : ((medians xs).eval oracle).length < xs.length := by
    rw [length_eval_medians]
    simp only [selectCutoff] at hsmall
    omega
  rw [select, dite_eq_right hsmall]
  simp only [FreeM.eval_bind]
  rw [dite_eq_left hM]
  simp only [FreeM.eval_bind, hp, hpart]
  rw [dite_eq_left hL, dite_eq_left hG]
  split_ifs <;> rfl

/-- The correctness invariant of `select`, by strong induction on the length of the list. -/
private theorem select_correct (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (n : ℕ) : ∀ (k : ℕ) (xs : List α), xs.length = n →
      (k < xs.length → ∃ y, (select k xs).eval oracle = some y ∧ xs.IsOrderStatistic r k y) ∧
      (xs.length ≤ k → (select k xs).eval oracle = none) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k xs hn
  subst hn
  by_cases hsmall : xs.length ≤ selectCutoff
  · rw [eval_select_of_le oracle k hsmall]
    have hperm := mergeSort_perm oracle xs
    have hsorted := mergeSort_sorted r oracle horacle xs
    rw [eval_mergeSort] at hperm hsorted
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · have hk' : k < (xs.mergeSort fun a b => oracle (.le a b)).length := by
        rw [hperm.length_eq]
        exact hk
      exact ⟨_, List.getElem?_eq_getElem hk',
        List.isOrderStatistic_getElem_of_perm hperm hsorted hk'⟩
    · rw [List.getElem?_eq_none_iff, hperm.length_eq]
      exact hk
  -- The pivot is an order statistic of the medians, by induction.
  have hMlen : ((medians xs).eval oracle).length = (xs.length + 4) / 5 :=
    length_eval_medians oracle xs
  obtain ⟨p, hp, hpos⟩ := (ih _ (by simp only [selectCutoff] at hsmall; omega)
    ((((medians xs).eval oracle).length - 1) / 2) ((medians xs).eval oracle) rfl).1
    (by simp only [selectCutoff] at hsmall; omega)
  rw [hMlen] at hpos
  have hL := length_filter_lt_le_selectSideBound r oracle horacle hpos
  have hG := length_filter_gt_le_selectSideBound r oracle horacle hpos
  rw [eval_select_of_lt oracle k hsmall hp (eval_partition3_of_total r oracle horacle p xs) hL hG]
  -- Sizes of the three parts.
  have hcL : xs.countP (fun x => ¬ r p x) = (xs.filter (fun x => ¬ r p x)).length :=
    List.countP_eq_length_filter
  have hcLE : xs.countP (fun x => r x p) =
      (xs.filter (fun x => ¬ r p x)).length + (xs.filter (fun x => r x p ∧ r p x)).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
      ← List.countP_and_not_add_countP_and (fun x => r x p) (fun x => r p x) xs]
    congr 1
    refine List.countP_congr fun x _ => ?_
    simp only [decide_eq_true_eq, and_iff_left_iff_imp]
    exact fun h => (Std.Total.total x p).resolve_right h
  have hsum : xs.length = xs.countP (fun x => r x p) + (xs.filter (fun x => ¬ r x p)).length := by
    rw [← List.countP_eq_length_filter,
      List.length_eq_countP_add_countP (fun x => decide (r x p))]
    simp only [Bool.decide_eq_true, decide_not]
  have hLlt : (xs.filter (fun x => ¬ r p x)).length < xs.length := by
    simp only [selectSideBound, selectCutoff] at hL hsmall
    omega
  have hGlt : (xs.filter (fun x => ¬ r x p)).length < xs.length := by
    simp only [selectSideBound, selectCutoff] at hG hsmall
    omega
  set L := xs.filter (fun x => ¬ r p x) with hLdef
  set E := xs.filter (fun x => r x p ∧ r p x) with hEdef
  set G := xs.filter (fun x => ¬ r x p) with hGdef
  split_ifs with hkL hkE
  · -- Rank `k` lies strictly below the pivot.
    refine ⟨fun _ => ?_, fun hk => by omega⟩
    obtain ⟨y, hy, hyos⟩ := (ih _ hLlt k L rfl).1 hkL
    refine ⟨y, hy, hyos.of_filter fun x _ hyx hpx => hyx ?_⟩
    have hpy : ¬ r p y := of_decide_eq_true (List.mem_filter.mp hyos.mem).2
    exact _root_.trans ((Std.Total.total y p).resolve_right hpy) hpx
  · -- Rank `k` is held by the pivot's equivalence class.
    refine ⟨fun _ => ⟨p, rfl, ?_⟩, fun hk => by omega⟩
    exact {
      mem := mem_of_mem_eval_medians oracle hpos.mem
      countP_lt_le := by omega
      lt_countP_le := by omega }
  · -- Rank `k` lies strictly above the pivot.
    obtain ⟨h1, h2⟩ := ih _ hGlt (k - L.length - E.length) G rfl
    refine ⟨fun hk => ?_, fun hk => h2 (by omega)⟩
    obtain ⟨y, hy, hyos⟩ := h1 (by omega)
    refine ⟨y, hy, ?_⟩
    have h : xs.IsOrderStatistic r (k - L.length - E.length + xs.countP (fun x => ¬ ¬ r x p)) y :=
      hyos.of_filter_add fun x _ hx => by
        have hyp : ¬ r y p := of_decide_eq_true (List.mem_filter.mp hyos.mem).2
        exact _root_.trans (not_not.mp hx) ((Std.Total.total y p).resolve_left hyp)
    have hc : xs.countP (fun x => ¬ ¬ r x p) = xs.countP (fun x => r x p) :=
      List.countP_congr fun x _ => by simp
    rwa [hc, show k - L.length - E.length + xs.countP (fun x => r x p) = k by omega] at h

/-- **Correctness of selection.** Against an oracle implementing a total preorder `r`,
`select k xs` returns an element of rank `k` of `xs` whenever `k < xs.length`. -/
theorem select_isOrderStatistic (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {k : ℕ} {xs : List α} (hk : k < xs.length) :
    ∃ y, (select k xs).eval oracle = some y ∧ xs.IsOrderStatistic r k y :=
  (select_correct r oracle horacle xs.length k xs rfl).1 hk

/-- Against an oracle implementing a total preorder, `select k xs` returns `none` when
`xs.length ≤ k`. -/
theorem eval_select_eq_none (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {k : ℕ} {xs : List α} (hk : xs.length ≤ k) : (select k xs).eval oracle = none :=
  (select_correct r oracle horacle xs.length k xs rfl).2 hk

/-- **Correctness of selection in a linear order.** Against the oracle answering `a ≤ b`,
`select k xs` returns the `k`-th entry of `xs.mergeSort`, or `none` when `xs.length ≤ k`. -/
theorem eval_select_eq_getElem?_mergeSort {β : Type} [LinearOrder β]
    (oracle : {ι : Type} → LEQuery β ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (a ≤ b))
    (k : ℕ) (xs : List β) : (select k xs).eval oracle = xs.mergeSort[k]? := by
  by_cases hk : k < xs.length
  · obtain ⟨y, hy, hyos⟩ := select_isOrderStatistic (· ≤ ·) oracle horacle hk
    rw [hy, List.isOrderStatistic_iff_mergeSort.mp hyos]
  · rw [eval_select_eq_none (· ≤ ·) oracle horacle (Nat.le_of_not_lt hk), eq_comm,
      List.getElem?_eq_none_iff, List.length_mergeSort]
    exact Nat.le_of_not_lt hk

end Cslib.Query
