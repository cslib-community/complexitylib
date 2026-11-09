/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.Expect
public import CslibFrontier.Init
public import CslibFrontier.Probability.KWiseIndependent
import CslibFrontier.Foundations.Data.Nat.Factorial
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variance-sensitive moment concentration under `k`-wise independence

For a `2m`-wise independent hash family `h : ι → X → Y` (`Cslib.Probability.IsKWiseIndependentHash`)
and `[0, 1]`-valued score functions `g z : Y → ℝ` on a finite set `R : Finset X` whose total mean
`∑ z ∈ R, 𝔼 y, g z y` is at most `μ`, `IsKWiseIndependentHash.expect_sum_pow_le` in
`CslibFrontier.Probability.KWiseIndependent` bounds the `2m`-th central moment by
`m ^ (2 * m) * (#R) ^ m`, scaling with the number of summands `#R` rather than `μ`. When individual
means are small (`μ ≪ #R`, such as indicator variables for balls landing in one of many bins), that
bound loses the `μ / #R` variance factor.

This module proves an elementary variance-sensitive `2m`-th central moment bound and Markov tail
inequalities in the spirit of the limited-independence moment method of Bellare and Rompel
[BellareRompel1994] and Theorem 5 of Schmidt, Siegel, and Srinivasan
[SchmidtSiegelSrinivasan1995]:
* Grouping `2m`-tuples `t : Fin (2 * m) → R` by image cardinality `r = #(univ.image t) ∈ [1, m]`,
  every tuple whose image has a singleton fiber has zero centered expectation, while on every tuple
  where each distinct coordinate appears `c ≥ 2` times we have
  `|𝔼 y, (g z y - 𝔼 y', g z y') ^ c| ≤ 𝔼 y, g z y`.
* Counting `r`-image tuples with product weight via `r ^ r ≤ 3 ^ r * r!`
  (`Nat.pow_self_le_three_pow_mul_factorial`) and summing a geometric factor `(1 / 2) ^ (m - r)`
  when `2 * m ≤ 3 * μ` yields
  `𝔼 i, (∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)) ^ (2 * m) ≤ 2 * (3 * m * μ) ^ m`
  (`expect_sum_sub_expect_pow_le`) and tail density at most `2 * (3 * m * μ / a ^ 2) ^ m`
  (`dens_abs_sum_sub_expect_le`).

## Main results

* `Cslib.Probability.expect_sum_sub_expect_pow_le`: variance-sensitive `2m`-th central moment bound
  for `[0, 1]`-valued sums under `2m`-wise independence.
* `Cslib.Probability.dens_abs_sum_sub_expect_le`: Markov tail bound
  `2 * (3 * m * μ / a ^ 2) ^ m` for `2m`-wise independent `[0, 1]` sums.
* `Cslib.Probability.dens_abs_sum_sub_expect_le_two_pow`: exponential `2 * (1 / 2) ^ m`
  specialization when `6 * m * μ ≤ a ^ 2` and `a ≤ μ`.

## References

* [J. P. Schmidt, A. Siegel, and A. Srinivasan, *Chernoff–Hoeffding Bounds for Applications with
  Limited Independence*][SchmidtSiegelSrinivasan1995]
* [M. Bellare and J. Rompel, *Randomness-Efficient Oblivious Sampling*][BellareRompel1994]
* [S. P. Vadhan, *Pseudorandomness*, Section 3.5][Vadhan2012]
-/

public section

namespace Cslib.Probability

open Finset Fintype
open scoped BigOperators

private theorem abs_expect_sub_expect_pow_le {Y : Type*} [Fintype Y] [Nonempty Y]
    (g : Y → ℝ) (hg : ∀ y, g y ∈ Set.Icc 0 1) {c : ℕ} (hc : 2 ≤ c) :
    |𝔼 y, (g y - 𝔼 y', g y') ^ c| ≤ 𝔼 y, g y := by
  set p : ℝ := 𝔼 y, g y
  have hp0 : 0 ≤ p := expect_nonneg fun y _ => (hg y).1
  have hp1 : p ≤ 1 := expect_le univ_nonempty fun y _ => (hg y).2
  have hpt (y : Y) : |g y - p| ^ c ≤ g y - 2 * p * g y + p ^ 2 := by
    have hz1 : |g y - p| ≤ 1 := abs_le.mpr ⟨by linarith [(hg y).1], by linarith [(hg y).2]⟩
    calc |g y - p| ^ c ≤ |g y - p| ^ 2 := pow_le_pow_of_le_one (abs_nonneg _) hz1 hc
      _ = (g y - p) ^ 2 := sq_abs _
      _ ≤ g y - 2 * p * g y + p ^ 2 := by nlinarith [(hg y).1, (hg y).2]
  have hlin : (𝔼 y, (g y - 2 * p * g y + p ^ 2)) = p - 2 * p * p + p ^ 2 := by
    rw [expect_add_distrib, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  calc |𝔼 y, (g y - p) ^ c|
      ≤ 𝔼 y, |(g y - p) ^ c| := abs_expect_le _ _
    _ = 𝔼 y, |g y - p| ^ c := by simp only [abs_pow]
    _ ≤ 𝔼 y, (g y - 2 * p * g y + p ^ 2) := expect_le_expect fun y _ => hpt y
    _ = p - 2 * p * p + p ^ 2 := hlin
    _ ≤ p := by nlinarith

private theorem sum_prod_image_card_eq_le {X : Type*} [DecidableEq X]
    (R : Finset X) (p : X → ℝ) (hp : ∀ z ∈ R, 0 ≤ p z) (n_tup r : ℕ) :
    (r.factorial : ℝ) *
      ∑ t ∈ {t ∈ piFinset (fun _ : Fin n_tup => R) | #(univ.image t) = r},
        ∏ z ∈ univ.image t, p z ≤
      (r : ℝ) ^ n_tup * (∑ z ∈ R, p z) ^ r := by
  let Tr := {t ∈ piFinset (fun _ : Fin n_tup => R) | #(univ.image t) = r}
  let Dom := Tr ×ˢ (univ : Finset (Equiv.Perm (Fin r)))
  let Cod := (univ : Finset (Fin n_tup → Fin r)) ×ˢ piFinset (fun _ : Fin r => R)
  let eqvOf (t : Fin n_tup → X) (ht : #(univ.image t) = r) : univ.image t ≃ Fin r :=
    (univ.image t).equivFin.trans (finCongr ht)
  let htOf (item : {pair // pair ∈ Dom}) : #(univ.image item.1.1) = r :=
    (mem_filter.mp (mem_product.mp item.2).1).2
  let Ψ (item : {pair // pair ∈ Dom}) : (Fin n_tup → Fin r) × (Fin r → X) :=
    let t := item.1.1
    let σ := item.1.2
    let e := eqvOf t (htOf item)
    (fun j => σ (e ⟨t j, mem_image_of_mem t (mem_univ j)⟩),
     fun k => (e.symm (σ.symm k)).1)
  have hmaps : Dom.attach.image Ψ ⊆ Cod := by
    intro qv hqv
    obtain ⟨item, -, rfl⟩ := mem_image.mp hqv
    refine mem_product.mpr ⟨mem_univ _, mem_piFinset.mpr fun k => ?_⟩
    have htR := mem_piFinset.mp (mem_filter.mp (mem_product.mp item.2).1).1
    obtain ⟨j, -, hj⟩ := mem_image.mp ((eqvOf item.1.1 (htOf item)).symm (item.1.2.symm k)).2
    simpa only [Ψ, ← hj] using htR j
  have hinj : Set.InjOn Ψ (Dom.attach : Set {pair // pair ∈ Dom}) := by
    intro item₁ _ item₂ _ heq
    have hq := congrArg Prod.fst heq
    have hv := congrArg Prod.snd heq
    have ht_eq : item₁.1.1 = item₂.1.1 := by
      funext j
      have hj₁ : (Ψ item₁).2 ((Ψ item₁).1 j) = item₁.1.1 j := by
        simp [Ψ]
      have hj₂ : (Ψ item₂).2 ((Ψ item₂).1 j) = item₂.1.1 j := by
        simp [Ψ]
      rw [← hj₁, ← hj₂, hq, hv]
    rcases item₁ with ⟨⟨t₁, σ₁⟩, h₁⟩
    rcases item₂ with ⟨⟨t₂, σ₂⟩, h₂⟩
    dsimp only at ht_eq
    subst ht_eq
    apply Subtype.ext
    refine Prod.ext rfl ?_
    have hsymm : σ₁.symm = σ₂.symm := by
      refine Equiv.ext fun k => ?_
      have hk := congrFun hv k
      dsimp only [Ψ, htOf] at hk
      have ht₁ : #(univ.image t₁) = r := (mem_filter.mp (mem_product.mp h₁).1).2
      have hsub : (eqvOf t₁ ht₁).symm (σ₁.symm k) =
          (eqvOf t₁ (mem_filter.mp (mem_product.mp h₂).1).2).symm (σ₂.symm k) :=
        Subtype.ext hk
      exact (eqvOf t₁ ht₁).symm.injective hsub
    exact Equiv.symm_bijective.injective hsymm
  have hwt (item : {pair // pair ∈ Dom}) :
      ∏ k : Fin r, p ((Ψ item).2 k) = ∏ z ∈ univ.image item.1.1, p z := by
    dsimp only [Ψ]
    rw [Equiv.prod_comp item.1.2.symm (fun j => p ((eqvOf item.1.1 (htOf item)).symm j).1),
      Equiv.prod_comp (eqvOf item.1.1 (htOf item)).symm (fun x => p x.1), prod_coe_sort]
  have hnonneg : ∀ qv ∈ Cod, qv ∉ Dom.attach.image Ψ → 0 ≤ ∏ k : Fin r, p (qv.2 k) := by
    intro qv hqv _
    have hvR := mem_piFinset.mp (mem_product.mp hqv).2
    exact prod_nonneg fun k _ => hp (qv.2 k) (hvR k)
  calc (r.factorial : ℝ) * ∑ t ∈ Tr, ∏ z ∈ univ.image t, p z
      = ∑ pair ∈ Dom, ∏ z ∈ univ.image pair.1, p z := by
          rw [sum_product]
          simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
          exact mul_sum Tr _ _
    _ = ∑ item ∈ Dom.attach, ∏ k : Fin r, p ((Ψ item).2 k) := by
          rw [← sum_attach Dom (fun pair => ∏ z ∈ univ.image pair.1, p z)]
          exact sum_congr rfl fun item _ => (hwt item).symm
    _ = ∑ qv ∈ Dom.attach.image Ψ, ∏ k : Fin r, p (qv.2 k) :=
          (sum_image (f := fun qv : (Fin n_tup → Fin r) × (Fin r → X) =>
            ∏ k : Fin r, p (qv.2 k)) hinj).symm
    _ ≤ ∑ qv ∈ Cod, ∏ k : Fin r, p (qv.2 k) := sum_le_sum_of_subset_of_nonneg hmaps hnonneg
    _ = (r : ℝ) ^ n_tup * (∑ z ∈ R, p z) ^ r := by
          rw [sum_product]
          simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_pow, sum_pow']

/-- **Variance-sensitive `2m`-th central moment bound under `2m`-wise independence**
(cf. [BellareRompel1994]; [SchmidtSiegelSrinivasan1995, Theorem 5]): for `1 ≤ m`, a `2m`-wise
independent family `h : ι → X → Y`, scores `g z : Y → [0, 1]` on `R : Finset X` with total mean at
most `μ`, and `2 * m ≤ 3 * μ`,
`𝔼 i, (∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)) ^ (2 * m) ≤ 2 * (3 * m * μ) ^ m`. -/
theorem expect_sum_sub_expect_pow_le {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] {m : ℕ} (hm : 1 ≤ m) {h : ι → X → Y}
    (hh : IsKWiseIndependentHash (2 * m) h) (R : Finset X) (g : X → Y → ℝ)
    (hg : ∀ z ∈ R, ∀ y, g z y ∈ Set.Icc 0 1) {μ : ℝ}
    (hmean : ∑ z ∈ R, (𝔼 y, g z y) ≤ μ) (hmμ : 2 * (m : ℝ) ≤ 3 * μ) :
    𝔼 i, (∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)) ^ (2 * m) ≤ 2 * (3 * (m : ℝ) * μ) ^ m := by
  classical
  have := hh.nonempty
  let p (z : X) : ℝ := 𝔼 y, g z y
  let Z (z : X) (y : Y) : ℝ := g z y - p z
  have hp0 : ∀ z ∈ R, 0 ≤ p z := fun z hz => expect_nonneg fun y _ => (hg z hz y).1
  have hsum_p0 : 0 ≤ ∑ z ∈ R, p z := sum_nonneg hp0
  have hμ0 : 0 ≤ μ := hsum_p0.trans hmean
  simp only [sum_pow']
  rw [expect_sum_comm]
  have hterm : ∀ t ∈ piFinset (fun _ : Fin (2 * m) => R),
      𝔼 i, ∏ j, Z (t j) (h i (t j)) ≤
        if #(univ.image t) ≤ m then ∏ z ∈ univ.image t, p z else 0 := by
    intro t ht
    have htR : ∀ z ∈ univ.image t, z ∈ R := by
      intro z hz
      obtain ⟨j, -, rfl⟩ := mem_image.mp hz
      exact mem_piFinset.mp ht j
    have hprod (i : ι) : ∏ j, Z (t j) (h i (t j)) =
        ∏ z ∈ univ.image t, Z z (h i z) ^ #{j | t j = z} :=
      prod_comp (fun z => Z z (h i z)) t
    simp only [hprod]
    rw [hh.expect_prod (card_image_le.trans (by simp)) fun z y => Z z y ^ #{j | t j = z}]
    split_ifs with hI
    · by_cases hall2 : ∀ z ∈ univ.image t, 2 ≤ #{j | t j = z}
      · refine (le_abs_self _).trans ?_
        rw [abs_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun z hz =>
          abs_expect_sub_expect_pow_le (g z) (hg z (htR z hz)) (hall2 z hz)
      · push Not at hall2
        obtain ⟨z, hz, hlt2⟩ := hall2
        obtain ⟨j, -, rfl⟩ := mem_image.mp hz
        have hpos : 0 < #{j' | t j' = t j} := card_pos.mpr ⟨j, by simp⟩
        have hc1 : #{j' | t j' = t j} = 1 := by omega
        rw [prod_eq_zero hz (by simp only [hc1, pow_one, Z, p]; exact Fintype.expect_balance _)]
        exact prod_nonneg fun w hw => hp0 w (htR w hw)
    · obtain ⟨z, hz, hc⟩ : ∃ z ∈ univ.image t, #{j | t j = z} = 1 := by
        by_contra hne
        push Not at hne
        have hsum := card_eq_sum_card_image t (univ : Finset (Fin (2 * m)))
        have h2 : ∑ z ∈ univ.image t, 2 ≤ ∑ z ∈ univ.image t, #{j | t j = z} := by
          refine sum_le_sum fun z hz => ?_
          obtain ⟨j, -, rfl⟩ := mem_image.mp hz
          have hpos : 0 < #{j' | t j' = t j} := card_pos.mpr ⟨j, by simp⟩
          have := hne (t j) hz
          omega
        rw [← hsum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
        omega
      rw [prod_eq_zero hz (by simp only [hc, pow_one, Z, p]; exact Fintype.expect_balance _)]
  have hpart :
      (∑ t ∈ piFinset (fun _ : Fin (2 * m) => R),
        if #(univ.image t) ≤ m then ∏ z ∈ univ.image t, p z else 0) =
      ∑ r ∈ Icc 1 m,
        ∑ t ∈ {t ∈ piFinset (fun _ : Fin (2 * m) => R) | #(univ.image t) = r},
          ∏ z ∈ univ.image t, p z := by
    rw [← sum_filter, ← sum_biUnion]
    · refine sum_congr ?_ fun _ _ => rfl
      ext t
      simp only [mem_filter, mem_biUnion, mem_Icc]
      refine ⟨fun ⟨ht, hle⟩ => ⟨#(univ.image t), ⟨?_, hle⟩, ht, rfl⟩,
        fun ⟨r, ⟨_, hrm⟩, ht, hcard⟩ => ⟨ht, hcard.le.trans hrm⟩⟩
      have hne_img : (univ.image t).Nonempty :=
        ⟨t ⟨0, by omega⟩, mem_image_of_mem t (mem_univ _)⟩
      exact card_pos.mpr hne_img
    · intro r₁ _ r₂ _ hne s hs₁ hs₂ t ht
      have h1 := (mem_filter.mp (hs₁ ht)).2
      have h2 := (mem_filter.mp (hs₂ ht)).2
      exact False.elim (hne (h1.symm.trans h2))
  have hr_bound : ∀ r ∈ Icc 1 m,
      ∑ t ∈ {t ∈ piFinset (fun _ : Fin (2 * m) => R) | #(univ.image t) = r},
        ∏ z ∈ univ.image t, p z ≤
      ((1 : ℝ) / 2) ^ (m - r) * (3 * (m : ℝ) * μ) ^ m := by
    intro r hr
    rcases mem_Icc.mp hr with ⟨hr1, hrm⟩
    have hfac_pos : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    have hstep := sum_prod_image_card_eq_le R p hp0 (2 * m) r
    have hpow_μ : (∑ z ∈ R, p z) ^ r ≤ μ ^ r := pow_le_pow_left₀ hsum_p0 hmean r
    have hr_pow : r ^ (2 * m) ≤ 3 ^ r * r.factorial * m ^ (2 * m - r) := by
      have hsplit : 2 * m = r + (2 * m - r) := by omega
      calc r ^ (2 * m) = r ^ r * r ^ (2 * m - r) := by
            conv_lhs => rw [hsplit]
            rw [pow_add]
        _ ≤ (3 ^ r * r.factorial) * m ^ (2 * m - r) :=
            Nat.mul_le_mul (Nat.pow_self_le_three_pow_mul_factorial r)
              (Nat.pow_le_pow_left hrm _)
    have hr_real : (r : ℝ) ^ (2 * m) * (∑ z ∈ R, p z) ^ r ≤
        (r.factorial : ℝ) * ((3 : ℝ) ^ r * (m : ℝ) ^ (2 * m - r) * μ ^ r) := by
      calc (r : ℝ) ^ (2 * m) * (∑ z ∈ R, p z) ^ r
          ≤ (r : ℝ) ^ (2 * m) * μ ^ r := by gcongr
        _ ≤ ((3 ^ r * r.factorial * m ^ (2 * m - r) : ℕ) : ℝ) * μ ^ r := by
            gcongr; exact_mod_cast hr_pow
        _ = (r.factorial : ℝ) * ((3 : ℝ) ^ r * (m : ℝ) ^ (2 * m - r) * μ ^ r) := by
            push_cast; ring
    have hdiv : ∑ t ∈ {t ∈ piFinset (fun _ : Fin (2 * m) => R) | #(univ.image t) = r},
          ∏ z ∈ univ.image t, p z ≤
        (3 : ℝ) ^ r * (m : ℝ) ^ (2 * m - r) * μ ^ r :=
      le_of_mul_le_mul_left (hstep.trans hr_real) hfac_pos
    refine hdiv.trans ?_
    have h2mr : 2 * m - r = m + (m - r) := by omega
    have hm_sub : (2 * (m : ℝ)) ^ (m - r) * (3 * μ) ^ r ≤ (3 * μ) ^ m := by
      calc (2 * (m : ℝ)) ^ (m - r) * (3 * μ) ^ r
          ≤ (3 * μ) ^ (m - r) * (3 * μ) ^ r := by gcongr
        _ = (3 * μ) ^ m := by rw [← pow_add, Nat.sub_add_cancel hrm]
    have hhalf : (m : ℝ) ^ (m - r) * (3 * μ) ^ r ≤ ((1 : ℝ) / 2) ^ (m - r) * (3 * μ) ^ m := by
      have hpos2 : (0 : ℝ) < 2 ^ (m - r) := by positivity
      apply le_of_mul_le_mul_left _ hpos2
      calc (2 : ℝ) ^ (m - r) * ((m : ℝ) ^ (m - r) * (3 * μ) ^ r)
          = (2 * (m : ℝ)) ^ (m - r) * (3 * μ) ^ r := by rw [mul_pow]; ring
        _ ≤ (3 * μ) ^ m := hm_sub
        _ = (2 : ℝ) ^ (m - r) * (((1 : ℝ) / 2) ^ (m - r) * (3 * μ) ^ m) := by
            rw [← mul_assoc, ← mul_pow]; norm_num
    calc (3 : ℝ) ^ r * (m : ℝ) ^ (2 * m - r) * μ ^ r
        = (m : ℝ) ^ m * ((m : ℝ) ^ (m - r) * (3 * μ) ^ r) := by
          rw [h2mr, pow_add, mul_pow]; ring
      _ ≤ (m : ℝ) ^ m * (((1 : ℝ) / 2) ^ (m - r) * (3 * μ) ^ m) := by gcongr
      _ = ((1 : ℝ) / 2) ^ (m - r) * (3 * (m : ℝ) * μ) ^ m := by rw [mul_pow]; ring
  have hgeom : ∑ r ∈ Icc 1 m, ((1 : ℝ) / 2) ^ (m - r) ≤ 2 := by
    have hbij : ∑ r ∈ Icc 1 m, ((1 : ℝ) / 2) ^ (m - r) = ∑ j ∈ range m, ((1 : ℝ) / 2) ^ j := by
      refine sum_nbij' (fun r => m - r) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
      · intro r hr; rw [mem_Icc] at hr; rw [mem_range]; omega
      · intro j hj; rw [mem_range] at hj; rw [mem_Icc]; omega
      · intro r hr; rw [mem_Icc] at hr; omega
      · intro j hj; rw [mem_range] at hj; omega
      · intro _ _; rfl
    rw [hbij]
    exact sum_geometric_two_le m
  calc ∑ t ∈ piFinset (fun _ : Fin (2 * m) => R), 𝔼 i, ∏ j, Z (t j) (h i (t j))
      ≤ ∑ t ∈ piFinset (fun _ : Fin (2 * m) => R),
          if #(univ.image t) ≤ m then ∏ z ∈ univ.image t, p z else 0 := sum_le_sum hterm
    _ = ∑ r ∈ Icc 1 m,
          ∑ t ∈ {t ∈ piFinset (fun _ : Fin (2 * m) => R) | #(univ.image t) = r},
            ∏ z ∈ univ.image t, p z := hpart
    _ ≤ ∑ r ∈ Icc 1 m, ((1 : ℝ) / 2) ^ (m - r) * (3 * (m : ℝ) * μ) ^ m := sum_le_sum hr_bound
    _ = (∑ r ∈ Icc 1 m, ((1 : ℝ) / 2) ^ (m - r)) * (3 * (m : ℝ) * μ) ^ m := (sum_mul _ _ _).symm
    _ ≤ 2 * (3 * (m : ℝ) * μ) ^ m := by gcongr

/-- **Markov tail bound for `2m`-wise independent `[0, 1]` sums**
(cf. [SchmidtSiegelSrinivasan1995, Theorem 5]): when `1 ≤ m`, `2 * m ≤ 3 * μ`, and `0 < a`, the sum
`∑ z ∈ R, g z (h i z)` deviates from its mean by at least `a` with seed density at most
`2 * (3 * m * μ / a ^ 2) ^ m`. -/
theorem dens_abs_sum_sub_expect_le {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] {m : ℕ} (hm : 1 ≤ m) {h : ι → X → Y}
    (hh : IsKWiseIndependentHash (2 * m) h) (R : Finset X) (g : X → Y → ℝ)
    (hg : ∀ z ∈ R, ∀ y, g z y ∈ Set.Icc 0 1) {μ a : ℝ}
    (hmean : ∑ z ∈ R, (𝔼 y, g z y) ≤ μ) (hmμ : 2 * (m : ℝ) ≤ 3 * μ) (ha : 0 < a) :
    (dens {i | a ≤ |∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)|} : ℝ) ≤
      2 * (3 * (m : ℝ) * μ / a ^ 2) ^ m := by
  have hmarkov := Fintype.mul_dens_filter_le_expect
    (f := fun i => (∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)) ^ (2 * m))
    (fun _ => (even_two_mul m).pow_nonneg _) (a ^ (2 * m))
  have hsub : ({i | a ≤ |∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)|} : Finset ι) ⊆
      ({i | a ^ (2 * m) ≤ (∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)) ^ (2 * m)} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [← (even_two_mul m).pow_abs (∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y))]
    exact pow_le_pow_left₀ ha.le hi _
  have hdens : (dens {i | a ≤ |∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)|} : ℝ) ≤
      dens {i | a ^ (2 * m) ≤ (∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)) ^ (2 * m)} := by
    exact_mod_cast dens_le_dens hsub
  have hpow : 0 < a ^ (2 * m) := pow_pos ha _
  calc (dens {i | a ≤ |∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)|} : ℝ)
      ≤ 2 * (3 * (m : ℝ) * μ) ^ m / a ^ (2 * m) := by
        rw [le_div_iff₀ hpow, mul_comm]
        exact (mul_le_mul_of_nonneg_left hdens hpow.le).trans
          (hmarkov.trans (expect_sum_sub_expect_pow_le hm hh R g hg hmean hmμ))
    _ = 2 * (3 * (m : ℝ) * μ / a ^ 2) ^ m := by
        rw [mul_div_assoc, div_pow, ← pow_mul, mul_comm 2 m]

/-- Exponential `2 * (1 / 2) ^ m` specialization of `dens_abs_sum_sub_expect_le` when
`6 * m * μ ≤ a ^ 2` and `a ≤ μ`. -/
theorem dens_abs_sum_sub_expect_le_two_pow {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] {m : ℕ} (hm : 1 ≤ m) {h : ι → X → Y}
    (hh : IsKWiseIndependentHash (2 * m) h) (R : Finset X) (g : X → Y → ℝ)
    (hg : ∀ z ∈ R, ∀ y, g z y ∈ Set.Icc 0 1) {μ a : ℝ}
    (hmean : ∑ z ∈ R, (𝔼 y, g z y) ≤ μ) (ha : 0 < a) (haμ : a ≤ μ)
    (h6 : 6 * (m : ℝ) * μ ≤ a ^ 2) :
    (dens {i | a ≤ |∑ z ∈ R, (g z (h i z) - 𝔼 y, g z y)|} : ℝ) ≤ 2 * ((1 : ℝ) / 2) ^ m := by
  have hμ_pos : 0 < μ := ha.trans_le haμ
  have hmμ : 2 * (m : ℝ) ≤ 3 * μ := by
    have hsq : a ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ ha.le haμ 2
    nlinarith
  have hrat : 3 * (m : ℝ) * μ / a ^ 2 ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ (pow_pos ha 2)]
    linarith
  exact (dens_abs_sum_sub_expect_le hm hh R g hg hmean hmμ ha).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hrat m) (by norm_num))

end Cslib.Probability
