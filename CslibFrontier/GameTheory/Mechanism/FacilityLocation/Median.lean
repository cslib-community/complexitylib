/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
import CslibFrontier.Foundations.Data.List.OrderStatistic
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.Linarith

/-!
# Median and order-statistic facility-location mechanisms on ℝ

On the real line `ℝ`, any fixed `k`-th order statistic (`orderStatisticMechanism k`) is strongly
group strategyproof (`orderStatisticMechanism_isGroupStrategyProof`, [Moulin1980],
[ProcacciaTennenholtz2013]). Moreover, both the lower median `x_((n - 1) / 2)` and the upper
median `x_(n / 2)` minimize the social cost `∑ i, |x i - y|` over all `y : ℝ`
(`lowerMedian_isOptimal`, `upperMedian_isOptimal`). Consequently `medianMechanism` (the lower
median) is simultaneously group strategyproof (`medianMechanism_isGroupStrategyProof`) and
`1`-approximate, i.e., socially optimal (`medianMechanism_hasApproxRatio_one`,
[ProcacciaTennenholtz2013]).

By contrast, `meanMechanism` fails strategyproofness whenever there are at least two agents
(`not_isStrategyProof_meanMechanism`), and for even `n` the average of the two middle order
statistics also fails strategyproofness (see `CslibFrontierTests.FacilityLocation`).

## Main definitions

* `Cslib.GameTheory.FacilityLocation.IsOrderStatistic`: `y` is the `k`-th order statistic of
  `x : ι → α` (reusing `List.IsOrderStatistic` for uniqueness and sorting).
* `Cslib.GameTheory.FacilityLocation.orderStatistic`: the `k`-th order statistic of `x : ι → α`.
* `Cslib.GameTheory.FacilityLocation.lowerMedian`,
  `Cslib.GameTheory.FacilityLocation.upperMedian`: the lower and upper medians.
* `Cslib.GameTheory.FacilityLocation.orderStatisticMechanism`,
  `Cslib.GameTheory.FacilityLocation.medianMechanism`: deterministic mechanisms on `ℝ`.
* `Cslib.GameTheory.FacilityLocation.mean`,
  `Cslib.GameTheory.FacilityLocation.meanMechanism`: the arithmetic-mean mechanism on `ℝ`.

## Main results

* `Cslib.GameTheory.FacilityLocation.orderStatistic_isOrderStatistic`,
  `Cslib.GameTheory.FacilityLocation.orderStatistic_eq_of_isOrderStatistic`: characterization of
  `orderStatistic`.
* `Cslib.GameTheory.FacilityLocation.orderStatisticMechanism_isGroupStrategyProof`: every fixed
  order-statistic mechanism on `ℝ` is strongly group strategyproof.
* `Cslib.GameTheory.FacilityLocation.medianMechanism_isGroupStrategyProof`,
  `Cslib.GameTheory.FacilityLocation.medianMechanism_isStrategyProof`: the median mechanism on `ℝ`
  is group strategyproof and strategyproof.
* `Cslib.GameTheory.FacilityLocation.isOptimal_of_median_counts`,
  `Cslib.GameTheory.FacilityLocation.lowerMedian_isOptimal`,
  `Cslib.GameTheory.FacilityLocation.upperMedian_isOptimal`: optimality of the lower and upper
  medians for `socialCost` on `ℝ`.
* `Cslib.GameTheory.FacilityLocation.medianMechanism_hasApproxRatio_one`,
  `Cslib.GameTheory.FacilityLocation.expectedSocialCost_medianMechanism_eq_optSocialCost`: the
  median mechanism on `ℝ` is `1`-approximate (socially optimal).
* `Cslib.GameTheory.FacilityLocation.not_isStrategyProof_meanMechanism`: the mean mechanism is not
  strategyproof for `2 ≤ Fintype.card ι`.

## References

* [H. Moulin, *On Strategy-Proofness and Single Peakedness*][Moulin1980]
* [A. D. Procaccia and M. Tennenholtz, *Approximate Mechanism Design without
  Money*][ProcacciaTennenholtz2013]
-/

public section

namespace Cslib.GameTheory.FacilityLocation

open MeasureTheory Finset
open scoped BigOperators

/-! ### Order statistics on finite profiles -/

section OrderStatistic

open Classical in
/-- `y` is the `k`-th order statistic (0-indexed) of the profile `x : ι → α`: `y` is in the image
of `x`, at most `k` agents lie strictly below `y`, and strictly more than `k` agents lie at or
below `y`. -/
@[expose] def IsOrderStatistic {ι α : Type*} [Fintype ι] [LinearOrder α] (x : ι → α)
    (k : ℕ) (y : α) : Prop :=
  (∃ i : ι, x i = y) ∧
    (Finset.univ.filter fun i => x i < y).card ≤ k ∧
    k < (Finset.univ.filter fun i => x i ≤ y).card

open Classical in
/-- The `k`-th order statistic (0-indexed) of `x : ι → α`, clamped to `Fintype.card ι - 1` when
`k ≥ Fintype.card ι`. -/
@[expose] noncomputable def orderStatistic {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) (k : ℕ) : α :=
  ((Finset.univ.val.map x).sort (· ≤ ·))[min k (Fintype.card ι - 1)]'(by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ]
    exact Nat.lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt Fintype.card_pos zero_lt_one))

/-- The lower median `x_((n - 1) / 2)` of a nonempty finite profile `x`. -/
@[expose] noncomputable def lowerMedian {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) : α :=
  orderStatistic x ((Fintype.card ι - 1) / 2)

/-- The upper median `x_(n / 2)` of a nonempty finite profile `x`. -/
@[expose] noncomputable def upperMedian {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) : α :=
  orderStatistic x (Fintype.card ι / 2)

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

/-! ### Strategyproofness and optimality on ℝ -/

section RealMechanisms

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The deterministic `k`-th order-statistic mechanism on `ℝ`. -/
@[expose] noncomputable def orderStatisticMechanism (k : ℕ) : Mechanism ι ℝ :=
  Mechanism.deterministic fun x => orderStatistic x k

/-- The deterministic **median mechanism** on `ℝ`, using the lower median `x_((n - 1) / 2)`. -/
@[expose] noncomputable def medianMechanism : Mechanism ι ℝ :=
  Mechanism.deterministic lowerMedian

/-- Every fixed `k`-th order-statistic mechanism on `ℝ` (`k < n`) is strongly group strategyproof
([Moulin1980], [ProcacciaTennenholtz2013]): if a coalition moves the facility from `y` to
`y' < y`, all agents at or above `y` strictly lose and therefore cannot belong to the coalition,
leaving at most `k` agents at or below `y'` (contradicting that `y'` has rank `k`); symmetrically
for `y < y'`. -/
theorem orderStatisticMechanism_isGroupStrategyProof [DecidableEq ι] {k : ℕ}
    (hk : k < Fintype.card ι) : (orderStatisticMechanism (ι := ι) k).IsGroupStrategyProof := by
  classical
  rw [orderStatisticMechanism, Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨hle, j, hj, hlt⟩
  set y := orderStatistic x k
  set x' := A.piecewise z x
  set y' := orderStatistic x' k
  have hy := orderStatistic_isOrderStatistic x hk
  change IsOrderStatistic x k y at hy
  have hy' := orderStatistic_isOrderStatistic x' hk
  change IsOrderStatistic x' k y' at hy'
  have hne : y' ≠ y := fun heq => by rw [heq] at hlt; exact (lt_irrefl _ hlt)
  rcases hne.lt_or_gt with hlt_y | hgt_y
  · -- If `y' < y`, every agent `i` with `y ≤ x i` strictly loses under `y'`, so `i ∉ A`.
    have hnotmem : ∀ i : ι, y ≤ x i → i ∉ A := by
      intro i hxi hiA
      have hcost := hle i hiA
      change |x i - y'| ≤ |x i - y| at hcost
      rw [abs_of_nonneg (sub_nonneg.2 hxi),
        abs_of_nonneg (sub_nonneg.2 (hlt_y.le.trans hxi))] at hcost
      linarith
    have hdisj : Disjoint (Finset.univ.filter fun i => y ≤ x i)
        (Finset.univ.filter fun i => x' i ≤ y') := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [Finset.mem_filter] at hi1 hi2
      have hxi : x' i = x i := Finset.piecewise_eq_of_notMem _ _ _ (hnotmem i hi1.2)
      rw [hxi] at hi2
      linarith [hi1.2, hi2.2]
    have hsum_le : (Finset.univ.filter fun i => y ≤ x i).card +
        (Finset.univ.filter fun i => x' i ≤ y').card ≤ Fintype.card ι := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_univ _
    have hsplit : (Finset.univ.filter fun i => x i < y).card +
        (Finset.univ.filter fun i => y ≤ x i).card = Fintype.card ι := by
      have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun i => x i < y)
      simpa only [Finset.card_univ, not_lt] using hc
    have h1 := hy.2.1
    have h2 := hy'.2.2
    omega
  · -- If `y < y'`, every agent `i` with `x i ≤ y` strictly loses under `y'`, so `i ∉ A`.
    have hnotmem : ∀ i : ι, x i ≤ y → i ∉ A := by
      intro i hxi hiA
      have hcost := hle i hiA
      change |x i - y'| ≤ |x i - y| at hcost
      rw [abs_of_nonpos (sub_nonpos.2 hxi),
        abs_of_nonpos (sub_nonpos.2 (hxi.trans hgt_y.le))] at hcost
      linarith
    have hsub : (Finset.univ.filter fun i => x i ≤ y) ⊆
        Finset.univ.filter fun i => x' i < y' := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ i, ?_⟩
      dsimp only [x']
      rw [Finset.piecewise_eq_of_notMem _ _ _ (hnotmem i hi.2)]
      exact hi.2.trans_lt hgt_y
    have hcard_le := Finset.card_le_card hsub
    have h1 := hy.2.2
    have h2 := hy'.2.1
    omega

theorem orderStatisticMechanism_isStrategyProof [DecidableEq ι] {k : ℕ}
    (hk : k < Fintype.card ι) : (orderStatisticMechanism (ι := ι) k).IsStrategyProof :=
  (orderStatisticMechanism_isGroupStrategyProof hk).isStrategyProof

/-- The median mechanism on `ℝ` is strongly group strategyproof. -/
theorem medianMechanism_isGroupStrategyProof [DecidableEq ι] :
    (medianMechanism (ι := ι)).IsGroupStrategyProof := by
  have hk : (Fintype.card ι - 1) / 2 < Fintype.card ι :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (Nat.sub_lt Fintype.card_pos zero_lt_one)
  exact orderStatisticMechanism_isGroupStrategyProof hk

/-- The median mechanism on `ℝ` is strategyproof ([ProcacciaTennenholtz2013]). -/
theorem medianMechanism_isStrategyProof [DecidableEq ι] :
    (medianMechanism (ι := ι)).IsStrategyProof :=
  medianMechanism_isGroupStrategyProof.isStrategyProof

omit [Nonempty ι] in
/-- Any point `y` having at most `n / 2` agents strictly to its left and at most `n / 2` agents
strictly to its right minimizes `socialCost x` on `ℝ`. -/
theorem isOptimal_of_median_counts {x : ι → ℝ} {y : ℝ}
    (hlt : 2 * (Finset.univ.filter fun i => x i < y).card ≤ Fintype.card ι)
    (hgt : 2 * (Finset.univ.filter fun i => y < x i).card ≤ Fintype.card ι) :
    IsOptimal x y := by
  classical
  intro z
  change ∑ i, |x i - y| ≤ ∑ i, |x i - z|
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
            have htri : |x i - y| ≤ |x i - z| + |z - y| := by
              simpa only [Real.dist_eq] using dist_triangle (x i) z y
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
            have htri : |x i - y| ≤ |x i - z| + |z - y| := by
              simpa only [Real.dist_eq] using dist_triangle (x i) z y
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

private theorem orderStatistic_isOptimal (x : ι → ℝ) {k : ℕ} (hk : k < Fintype.card ι)
    (hle : 2 * k ≤ Fintype.card ι) (hge : Fintype.card ι ≤ 2 * (k + 1)) :
    IsOptimal x (orderStatistic x k) := by
  classical
  have hos := orderStatistic_isOrderStatistic x hk
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i => x i ≤ orderStatistic x k)
  have hgt_eq : (Finset.univ.filter fun i => orderStatistic x k < x i) =
      Finset.univ.filter fun i => ¬ x i ≤ orderStatistic x k := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  rw [Finset.card_univ, ← hgt_eq] at hsplit
  refine isOptimal_of_median_counts ?_ ?_
  · have := hos.2.1; omega
  · have := hos.2.2; omega

/-- The lower median minimizes social cost on `ℝ`. -/
theorem lowerMedian_isOptimal (x : ι → ℝ) : IsOptimal x (lowerMedian x) := by
  have hk : (Fintype.card ι - 1) / 2 < Fintype.card ι :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (Nat.sub_lt Fintype.card_pos zero_lt_one)
  have hpos := Fintype.card_pos (α := ι)
  exact orderStatistic_isOptimal x hk (by omega) (by omega)

/-- The upper median minimizes social cost on `ℝ`. -/
theorem upperMedian_isOptimal (x : ι → ℝ) : IsOptimal x (upperMedian x) := by
  have hk : Fintype.card ι / 2 < Fintype.card ι :=
    Nat.div_lt_self Fintype.card_pos (by decide)
  exact orderStatistic_isOptimal x hk (by omega) (by omega)

/-- The median mechanism on `ℝ` is `1`-approximate (socially optimal)
([ProcacciaTennenholtz2013]). -/
theorem medianMechanism_hasApproxRatio_one :
    (medianMechanism (ι := ι)).HasApproxRatio 1 := by
  rw [medianMechanism, Mechanism.hasApproxRatio_deterministic_iff _ zero_le_one]
  intro x
  rw [one_mul, (lowerMedian_isOptimal x).socialCost_eq_optSocialCost]

theorem expectedSocialCost_medianMechanism_eq_optSocialCost (x : ι → ℝ) :
    expectedSocialCost (medianMechanism x) x = optSocialCost x := by
  rw [medianMechanism, Mechanism.expectedSocialCost_deterministic,
    (lowerMedian_isOptimal x).socialCost_eq_optSocialCost]

/-! ### Non-strategyproofness of the mean mechanism -/

omit [Nonempty ι] in
/-- The arithmetic mean of the reported locations on `ℝ`. -/
@[expose] noncomputable def mean (x : ι → ℝ) : ℝ :=
  (∑ i, x i) / Fintype.card ι

omit [Nonempty ι] in
/-- The deterministic **mean mechanism** on `ℝ`. -/
@[expose] noncomputable def meanMechanism : Mechanism ι ℝ :=
  Mechanism.deterministic mean

omit [Nonempty ι] in
/-- For two or more agents on `ℝ`, the mean mechanism is not strategyproof: an agent at `0` facing
`n - 1` agents at `1` reduces its distance to the facility from `(n - 1) / n` to `0` by reporting
`1 - n`. -/
theorem not_isStrategyProof_meanMechanism [DecidableEq ι] (hcard : 2 ≤ Fintype.card ι) :
    ¬ (meanMechanism (ι := ι)).IsStrategyProof := by
  classical
  rw [meanMechanism, Mechanism.isStrategyProof_deterministic_iff]
  intro hsp
  have hpos : 0 < Fintype.card ι := lt_of_lt_of_le (by decide) hcard
  have hi₀ : Nonempty ι := Fintype.card_pos_iff.1 hpos
  obtain ⟨i₀⟩ := hi₀
  let x : ι → ℝ := fun j => if j = i₀ then 0 else 1
  let z : ℝ := 1 - (Fintype.card ι : ℝ)
  have hones : ∑ _j ∈ Finset.univ.erase i₀, (1 : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_sub hpos, Nat.cast_one]
  have hsum : ∑ j ∈ Finset.univ.erase i₀, x j = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.sum_congr rfl (fun j hj =>
      show x j = 1 by simp only [x, Finset.ne_of_mem_erase hj, ite_false]), hones]
  have hmean_x : mean x = ((Fintype.card ι : ℝ) - 1) / Fintype.card ι := by
    rw [mean, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have hx0 : x i₀ = 0 := by simp only [x, ite_true]
    rw [hx0, zero_add, hsum]
  have hmean_upd : mean (Function.update x i₀ z) = 0 := by
    rw [mean, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), Function.update_self]
    have hupd : ∑ j ∈ Finset.univ.erase i₀, Function.update x i₀ z j =
        ∑ j ∈ Finset.univ.erase i₀, x j :=
      Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) z x
    rw [hupd, hsum]
    simp only [z]
    ring_nf
  have hle := hsp x i₀ z
  have hx0 : x i₀ = 0 := by simp only [x, ite_true]
  rw [hx0, hmean_x, hmean_upd] at hle
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_zero] at hle
  have hcard_r : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hlt : 0 < |((Fintype.card ι : ℝ) - 1) / Fintype.card ι| :=
    abs_pos.2 (div_ne_zero (by linarith) (by positivity))
  exact hlt.not_ge hle

end RealMechanisms

end Cslib.GameTheory.FacilityLocation
