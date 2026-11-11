/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Fintype.OrderStatistic
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
import Mathlib.Tactic.Linarith

/-!
# Median and order-statistic facility-location mechanisms on ℝ

On the real line `ℝ`, any fixed `k`-th order statistic (`orderStatisticMechanism k`, clamped at
`Fintype.card ι - 1`) is strongly group strategyproof
(`orderStatisticMechanism_isGroupStrategyProof`). [ProcacciaTennenholtz2013] (§3.1, pp. 18:7–18:8)
note that any `k`-th order statistic is weakly group strategyproof (attributing this to
[Moulin1980], which is not directly inspected here); the strong variant proved in
`orderStatisticMechanism_isGroupStrategyProof` implies both weak group strategyproofness and
strategyproofness.

Moreover, both the lower median `x_((n - 1) / 2)` (`Fintype.lowerMedian`) and the upper median
`x_(n / 2)` (`Fintype.upperMedian`) minimize the social cost `∑ i, |x i - y|` over all `y : ℝ`
(`lowerMedian_isOptimal`, `upperMedian_isOptimal`). Following [ProcacciaTennenholtz2013] (§3.1,
p. 18:7), `medianMechanism` picks the lower median `x_((n - 1) / 2)` (the leftmost optimal point
for even `n`), and is simultaneously group strategyproof (`medianMechanism_isGroupStrategyProof`)
and `1`-approximate, i.e., socially optimal (`medianMechanism_hasApproxRatio_one`).

By contrast, `meanMechanism` fails strategyproofness whenever there are at least two agents
(`not_isStrategyProof_meanMechanism`), and for even `n` the average of the two middle order
statistics also fails strategyproofness (see `CslibFrontierTests.FacilityLocation`).

## Main definitions

* `Cslib.GameTheory.FacilityLocation.orderStatisticMechanism`,
  `Cslib.GameTheory.FacilityLocation.medianMechanism`: deterministic mechanisms on `ℝ` built from
  `Fintype.orderStatistic` and `Fintype.lowerMedian`.
* `Cslib.GameTheory.FacilityLocation.mean`,
  `Cslib.GameTheory.FacilityLocation.meanMechanism`: the arithmetic-mean mechanism on `ℝ`.

## Main results

* `Cslib.GameTheory.FacilityLocation.orderStatisticMechanism_isGroupStrategyProof`,
  `Cslib.GameTheory.FacilityLocation.orderStatisticMechanism_isStrategyProof`: every fixed
  order-statistic mechanism on `ℝ` is strongly group strategyproof (and hence strategyproof).
* `Cslib.GameTheory.FacilityLocation.medianMechanism_isGroupStrategyProof`,
  `Cslib.GameTheory.FacilityLocation.medianMechanism_isStrategyProof`: the median mechanism on `ℝ`
  is group strategyproof and strategyproof.
* `Cslib.GameTheory.FacilityLocation.lowerMedian_isOptimal`,
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

/-! ### Strategyproofness and optimality on ℝ -/

section RealMechanisms

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The deterministic `k`-th order-statistic mechanism on `ℝ` (clamped at `Fintype.card ι - 1`). -/
@[expose] noncomputable def orderStatisticMechanism (k : ℕ) : Mechanism ι ℝ :=
  Mechanism.deterministic fun x => Fintype.orderStatistic x k

/-- The deterministic **median mechanism** on `ℝ`, using the lower median `x_((n - 1) / 2)`
([ProcacciaTennenholtz2013] §3.1, p. 18:7). -/
@[expose] noncomputable def medianMechanism : Mechanism ι ℝ :=
  Mechanism.deterministic Fintype.lowerMedian

/-- Every fixed `k`-th order-statistic mechanism on `ℝ` (clamped at `n - 1` when `k ≥ n`) is
strongly group strategyproof (strengthening the weak group strategyproofness noted in
[ProcacciaTennenholtz2013] §3.1, p. 18:7, attributed there to [Moulin1980]): if a coalition moves
the facility from `y` to `y' < y`, all agents at or above `y` strictly lose and therefore cannot
belong to the coalition, leaving at most `min k (n - 1)` agents at or below `y'` (contradicting
that `y'` has rank `min k (n - 1)`); symmetrically for `y < y'`. -/
theorem orderStatisticMechanism_isGroupStrategyProof [DecidableEq ι] (k : ℕ) :
    (orderStatisticMechanism (ι := ι) k).IsGroupStrategyProof := by
  classical
  rw [orderStatisticMechanism, Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨hle, j, hj, hlt⟩
  set m := min k (Fintype.card ι - 1)
  have hm : m < Fintype.card ι :=
    Nat.lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt Fintype.card_pos zero_lt_one)
  set y := Fintype.orderStatistic x k
  set x' := A.piecewise z x
  set y' := Fintype.orderStatistic x' k
  have hy : Fintype.IsOrderStatistic x m y := by
    rw [show y = Fintype.orderStatistic x m from Fintype.orderStatistic_eq_min x k]
    exact Fintype.orderStatistic_isOrderStatistic x hm
  have hy' : Fintype.IsOrderStatistic x' m y' := by
    rw [show y' = Fintype.orderStatistic x' m from Fintype.orderStatistic_eq_min x' k]
    exact Fintype.orderStatistic_isOrderStatistic x' hm
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

theorem orderStatisticMechanism_isStrategyProof [DecidableEq ι] (k : ℕ) :
    (orderStatisticMechanism (ι := ι) k).IsStrategyProof :=
  (orderStatisticMechanism_isGroupStrategyProof k).isStrategyProof

/-- The median mechanism on `ℝ` is strongly group strategyproof. -/
theorem medianMechanism_isGroupStrategyProof [DecidableEq ι] :
    (medianMechanism (ι := ι)).IsGroupStrategyProof := by
  simpa only [medianMechanism, funext Fintype.lowerMedian_def, orderStatisticMechanism] using
    orderStatisticMechanism_isGroupStrategyProof (ι := ι) ((Fintype.card ι - 1) / 2)

/-- The median mechanism on `ℝ` is strategyproof ([ProcacciaTennenholtz2013] §3.1, p. 18:7). -/
theorem medianMechanism_isStrategyProof [DecidableEq ι] :
    (medianMechanism (ι := ι)).IsStrategyProof :=
  medianMechanism_isGroupStrategyProof.isStrategyProof

/-- The lower median minimizes social cost on `ℝ` ([ProcacciaTennenholtz2013] §3.1, pp. 18:7–8). -/
theorem lowerMedian_isOptimal (x : ι → ℝ) : IsOptimal x (Fintype.lowerMedian x) := fun z =>
  Fintype.sum_abs_sub_lowerMedian_le x z

/-- The upper median minimizes social cost on `ℝ`. -/
theorem upperMedian_isOptimal (x : ι → ℝ) : IsOptimal x (Fintype.upperMedian x) := fun z =>
  Fintype.sum_abs_sub_upperMedian_le x z

/-- The median mechanism on `ℝ` is `1`-approximate (socially optimal)
([ProcacciaTennenholtz2013] §3.1, pp. 18:7–18:8). -/
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
noncomputable def mean (x : ι → ℝ) : ℝ :=
  (∑ i, x i) / Fintype.card ι

omit [Nonempty ι] in
theorem mean_def (x : ι → ℝ) : mean x = (∑ i, x i) / Fintype.card ι := by
  unfold mean
  rfl

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
    rw [mean_def, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have hx0 : x i₀ = 0 := by simp only [x, ite_true]
    rw [hx0, zero_add, hsum]
  have hmean_upd : mean (Function.update x i₀ z) = 0 := by
    rw [mean_def, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), Function.update_self]
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
