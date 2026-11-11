/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Foundations.Data.List.OrderStatistic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Order statistics and medians of finite families

Defines rank-`k` order statistics (`Fintype.IsOrderStatistic`, `Fintype.orderStatistic`), lower
median `x_((n - 1) / 2)` (`Fintype.lowerMedian`), and upper median `x_(n / 2)`
(`Fintype.upperMedian`) for finite families `x : ι → α`, bridging to `List.IsOrderStatistic` and
proving that any median minimizes `∑ i, |x i - y|` over `ℝ`.

## Main definitions

* `Fintype.IsOrderStatistic`: `y` is the `k`-th order statistic (0-indexed) of `x : ι → α`.
* `Fintype.orderStatistic`: the `k`-th order statistic of `x : ι → α` (clamped at `|ι| - 1`).
* `Fintype.lowerMedian`, `Fintype.upperMedian`: the lower and upper medians of `x : ι → α`.

## Main results

* `Fintype.IsOrderStatistic.unique`, `Fintype.orderStatistic_isOrderStatistic`,
  `Fintype.orderStatistic_eq_of_isOrderStatistic`, `Fintype.orderStatistic_fin_eq_mergeSort`:
  uniqueness, rank characterization, and merge-sort correspondence.
* `Fintype.sum_abs_sub_le_of_median_counts`, `Fintype.sum_abs_sub_lowerMedian_le`,
  `Fintype.sum_abs_sub_upperMedian_le`: on `ℝ`, any point with at most `|ι| / 2` elements strictly
  on each side (and in particular `lowerMedian x` and `upperMedian x`) minimizes `∑ i, |x i - y|`.
-/

public section

namespace Fintype

open Finset
open scoped BigOperators

section OrderStatistic

open Classical in
/-- `y` is the `k`-th order statistic (0-indexed) of the profile `x : ι → α`: `y` lies in the
image of `x`, at most `k` indices satisfy `x i < y`, and strictly more than `k` satisfy
`x i ≤ y`. -/
@[expose] def IsOrderStatistic {ι α : Type*} [Fintype ι] [LinearOrder α] (x : ι → α)
    (k : ℕ) (y : α) : Prop :=
  (∃ i : ι, x i = y) ∧
    (Finset.univ.filter fun i => x i < y).card ≤ k ∧
    k < (Finset.univ.filter fun i => x i ≤ y).card

open Classical in
/-- The `k`-th order statistic (0-indexed) of `x : ι → α`, clamped to `Fintype.card ι - 1` when
`k ≥ Fintype.card ι`. -/
noncomputable def orderStatistic {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) (k : ℕ) : α :=
  ((Finset.univ.val.map x).sort (· ≤ ·))[min k (Fintype.card ι - 1)]'(by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ]
    exact Nat.lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt Fintype.card_pos zero_lt_one))

/-- The lower median `x_((n - 1) / 2)` of a nonempty finite family `x`. -/
noncomputable def lowerMedian {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) : α :=
  orderStatistic x ((Fintype.card ι - 1) / 2)

/-- The upper median `x_(n / 2)` of a nonempty finite family `x`. -/
noncomputable def upperMedian {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) : α :=
  orderStatistic x (Fintype.card ι / 2)

theorem lowerMedian_def {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α] (x : ι → α) :
    lowerMedian x = orderStatistic x ((Fintype.card ι - 1) / 2) := by
  unfold lowerMedian
  rfl

theorem upperMedian_def {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α] (x : ι → α) :
    upperMedian x = orderStatistic x (Fintype.card ι / 2) := by
  unfold upperMedian
  rfl

theorem orderStatistic_eq_min {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) (k : ℕ) :
    orderStatistic x k = orderStatistic x (min k (Fintype.card ι - 1)) := by
  simp only [orderStatistic, min_assoc, min_self]

section Lemmas

open Classical in
private theorem countP_sorted_eq_card_filter {ι α : Type*} [Fintype ι] [LinearOrder α]
    (x : ι → α) (p : α → Bool) :
    ((Finset.univ.val.map x).sort (· ≤ ·)).countP p =
      (Finset.univ.filter fun i => p (x i)).card := by
  have hp : p = fun a => decide (p a = true) := funext fun a => by cases p a <;> rfl
  rw [hp, ← Multiset.coe_countP, Multiset.sort_eq, Multiset.countP_map, ← Finset.filter_val]
  simp only [Bool.decide_eq_true]
  rfl

open Classical in
private theorem isOrderStatistic_iff_list {ι α : Type*} [Fintype ι] [LinearOrder α]
    {x : ι → α} {k : ℕ} {y : α} :
    IsOrderStatistic x k y ↔
      ((Finset.univ.val.map x).sort (· ≤ ·)).IsOrderStatistic (· ≤ ·) k y := by
  set s := (Finset.univ.val.map x).sort (· ≤ ·)
  have hmem : (∃ i : ι, x i = y) ↔ y ∈ s := by
    rw [Multiset.mem_sort, Multiset.mem_map]
    simp only [Finset.mem_val, Finset.mem_univ, true_and]
  have hlt : (Finset.univ.filter fun i => x i < y).card = s.countP (fun a => ¬ y ≤ a) := by
    rw [countP_sorted_eq_card_filter x (fun a => decide (¬ y ≤ a))]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, not_le]
  have hle : (Finset.univ.filter fun i => x i ≤ y).card = s.countP (fun a => a ≤ y) := by
    rw [countP_sorted_eq_card_filter x (fun a => decide (a ≤ y))]
    simp only [decide_eq_true_eq]
  rw [IsOrderStatistic, hmem, hlt, hle]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun h => ⟨h.mem, h.countP_lt_le, h.lt_countP_le⟩⟩

variable {ι α : Type*} [Fintype ι] [LinearOrder α]

theorem IsOrderStatistic.unique {x : ι → α} {k : ℕ} {y y' : α}
    (h : IsOrderStatistic x k y) (h' : IsOrderStatistic x k y') : y = y' :=
  (isOrderStatistic_iff_list.1 h).unique (isOrderStatistic_iff_list.1 h')

theorem orderStatistic_isOrderStatistic [Nonempty ι] (x : ι → α) {k : ℕ}
    (hk : k < Fintype.card ι) : IsOrderStatistic x k (orderStatistic x k) := by
  classical
  rw [isOrderStatistic_iff_list]
  have hlen : k < ((Finset.univ.val.map x).sort (· ≤ ·)).length := by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ]
    exact hk
  have hmin : min k (Fintype.card ι - 1) = k := min_eq_left (Nat.le_pred_of_lt hk)
  have hlist := List.isOrderStatistic_getElem_of_perm (List.Perm.refl _)
    (Multiset.pairwise_sort _ _) hlen
  simpa only [orderStatistic, hmin] using hlist

theorem orderStatistic_eq_of_isOrderStatistic [Nonempty ι] {x : ι → α} {k : ℕ}
    (hk : k < Fintype.card ι) {y : α} (h : IsOrderStatistic x k y) :
    orderStatistic x k = y :=
  (orderStatistic_isOrderStatistic x hk).unique h

theorem orderStatistic_fin_eq_mergeSort {n : ℕ} (x : Fin (n + 1) → α) {k : ℕ} (hk : k < n + 1) :
    (List.ofFn x).mergeSort[k]? = some (orderStatistic x k) := by
  classical
  rw [← List.isOrderStatistic_iff_mergeSort]
  have hcard : k < Fintype.card (Fin (n + 1)) := by simpa only [Fintype.card_fin] using hk
  have hos := orderStatistic_isOrderStatistic x hcard
  have hlist := isOrderStatistic_iff_list.1 hos
  have huniv : (Finset.univ : Finset (Fin (n + 1))).val = ↑(List.finRange (n + 1)) := by
    rw [Fin.univ_def]
  have hperm : (List.ofFn x).Perm ((Finset.univ.val.map x).sort (· ≤ ·)) := by
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq, huniv, List.ofFn_eq_map]
    rfl
  refine ⟨hperm.symm.subset hlist.mem, ?_, ?_⟩
  · rw [hperm.countP_eq]
    exact hlist.countP_lt_le
  · rw [hperm.countP_eq]
    exact hlist.lt_countP_le

end Lemmas

end OrderStatistic

section RealMedian

/-- Any point `y : ℝ` having at most `|ι| / 2` points strictly to its left and at most `|ι| / 2`
points strictly to its right minimizes `∑ i, |x i - y|`. -/
theorem sum_abs_sub_le_of_median_counts {ι : Type*} [Fintype ι] {x : ι → ℝ} {y : ℝ}
    (hlt : 2 * (Finset.univ.filter fun i => x i < y).card ≤ Fintype.card ι)
    (hgt : 2 * (Finset.univ.filter fun i => y < x i).card ≤ Fintype.card ι) (z : ℝ) :
    ∑ i, |x i - y| ≤ ∑ i, |x i - z| := by
  classical
  rcases le_total z y with hzy | hyz
  · set L := Finset.univ.filter fun i => x i < y
    set R := Finset.univ.filter fun i => ¬ x i < y
    have hcard : L.card + R.card = Fintype.card ι := by
      simpa only [Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => x i < y)
    have hLR : (L.card : ℝ) ≤ R.card := by exact_mod_cast (by omega : L.card ≤ R.card)
    have hL : ∑ i ∈ L, |x i - y| ≤ ∑ i ∈ L, |x i - z| + (L.card : ℝ) * (y - z) := by
      calc ∑ i ∈ L, |x i - y|
          ≤ ∑ i ∈ L, (|x i - z| + (y - z)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have htri : |x i - y| ≤ |x i - z| + |z - y| := abs_sub_le (x i) z y
            rwa [abs_of_nonpos (sub_nonpos.2 hzy), neg_sub] at htri
        _ = ∑ i ∈ L, |x i - z| + (L.card : ℝ) * (y - z) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hR : ∑ i ∈ R, |x i - y| = ∑ i ∈ R, |x i - z| - (R.card : ℝ) * (y - z) := by
      have hterm : ∀ i ∈ R, |x i - y| = |x i - z| - (y - z) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        have hxi : y ≤ x i := not_lt.1 hi.2
        rw [abs_of_nonneg (sub_nonneg.2 hxi), abs_of_nonneg (sub_nonneg.2 (hzy.trans hxi))]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hsplit_y : ∑ i, |x i - y| = ∑ i ∈ L, |x i - y| + ∑ i ∈ R, |x i - y| :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i < y)
        (fun i => |x i - y|)).symm
    have hsplit_z : ∑ i, |x i - z| = ∑ i ∈ L, |x i - z| + ∑ i ∈ R, |x i - z| :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i < y)
        (fun i => |x i - z|)).symm
    have hdiff : ((L.card : ℝ) - R.card) * (y - z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hLR) (sub_nonneg.2 hzy)
    linarith
  · set L := Finset.univ.filter fun i => x i ≤ y
    set R := Finset.univ.filter fun i => ¬ x i ≤ y
    have hReq : R = Finset.univ.filter fun i => y < x i := by
      ext i
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    have hcard : L.card + R.card = Fintype.card ι := by
      simpa only [Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => x i ≤ y)
    have hRL : (R.card : ℝ) ≤ L.card := by
      have hcard' : L.card + (Finset.univ.filter fun i => y < x i).card = Fintype.card ι := by
        simpa only [hReq] using hcard
      exact_mod_cast (by omega : R.card ≤ L.card)
    have hL : ∑ i ∈ L, |x i - y| = ∑ i ∈ L, |x i - z| - (L.card : ℝ) * (z - y) := by
      have hterm : ∀ i ∈ L, |x i - y| = |x i - z| - (z - y) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [abs_of_nonpos (sub_nonpos.2 hi.2), abs_of_nonpos (sub_nonpos.2 (hi.2.trans hyz))]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hR : ∑ i ∈ R, |x i - y| ≤ ∑ i ∈ R, |x i - z| + (R.card : ℝ) * (z - y) := by
      calc ∑ i ∈ R, |x i - y|
          ≤ ∑ i ∈ R, (|x i - z| + (z - y)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have htri : |x i - y| ≤ |x i - z| + |z - y| := abs_sub_le (x i) z y
            rwa [abs_of_nonneg (sub_nonneg.2 hyz)] at htri
        _ = ∑ i ∈ R, |x i - z| + (R.card : ℝ) * (z - y) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hsplit_y : ∑ i, |x i - y| = ∑ i ∈ L, |x i - y| + ∑ i ∈ R, |x i - y| :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i ≤ y)
        (fun i => |x i - y|)).symm
    have hsplit_z : ∑ i, |x i - z| = ∑ i ∈ L, |x i - z| + ∑ i ∈ R, |x i - z| :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i ≤ y)
        (fun i => |x i - z|)).symm
    have hdiff : ((R.card : ℝ) - L.card) * (z - y) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hRL) (sub_nonneg.2 hyz)
    linarith

private theorem sum_abs_sub_orderStatistic_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) {k : ℕ} (hk : k < Fintype.card ι) (hle : 2 * k ≤ Fintype.card ι)
    (hge : Fintype.card ι ≤ 2 * (k + 1)) (z : ℝ) :
    ∑ i, |x i - orderStatistic x k| ≤ ∑ i, |x i - z| := by
  classical
  have hos := orderStatistic_isOrderStatistic x hk
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i => x i ≤ orderStatistic x k)
  have hgt_eq : (Finset.univ.filter fun i => orderStatistic x k < x i) =
      Finset.univ.filter fun i => ¬ x i ≤ orderStatistic x k := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  rw [Finset.card_univ, ← hgt_eq] at hsplit
  refine sum_abs_sub_le_of_median_counts ?_ ?_ z
  · have := hos.2.1; omega
  · have := hos.2.2; omega

/-- The lower median minimizes `∑ i, |x i - y|` over `ℝ`. -/
theorem sum_abs_sub_lowerMedian_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (z : ℝ) :
    ∑ i, |x i - lowerMedian x| ≤ ∑ i, |x i - z| := by
  have hk : (Fintype.card ι - 1) / 2 < Fintype.card ι :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (Nat.sub_lt Fintype.card_pos zero_lt_one)
  have hpos := Fintype.card_pos (α := ι)
  exact sum_abs_sub_orderStatistic_le x hk (by omega) (by omega) z

/-- The upper median minimizes `∑ i, |x i - y|` over `ℝ`. -/
theorem sum_abs_sub_upperMedian_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (z : ℝ) :
    ∑ i, |x i - upperMedian x| ≤ ∑ i, |x i - z| := by
  have hk : Fintype.card ι / 2 < Fintype.card ι :=
    Nat.div_lt_self Fintype.card_pos (by decide)
  exact sum_abs_sub_orderStatistic_le x hk (by omega) (by omega) z

end RealMedian

end Fintype
