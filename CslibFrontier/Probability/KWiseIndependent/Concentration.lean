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

/-- A `[0, 1]`-valued score with mean `p` has `|𝔼 (g - p) ^ c| ≤ p` for every `c ≥ 2`: the centered
value lies in `[-1, 1]`, so its `c`-th power is at most its square, whose mean `p - p ^ 2` is at
most `p`. -/
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

/-- Counting tuples with exactly `r` distinct entries, weighted by the product of `p` over their
image: relabelling the image by `Fin r` in all `r!` ways maps each such tuple injectively to a
pattern `Fin n_tup → Fin r` together with a list of values `Fin r → R`, so
`r! * ∑ t, ∏ z ∈ image t, p z ≤ r ^ n_tup * (∑ z ∈ R, p z) ^ r`. -/
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

/-- **One tuple of the expanded moment.** For a `2m`-tuple `t` of keys in `R`, the centered product
`∏ j, (g (t j) (h i (t j)) - 𝔼 g (t j))` has seed average zero when some key occurs exactly once,
since that key's centered factor averages to zero. Otherwise every key occurs at least twice, so at
most `m` distinct keys occur, and the average is at most the product of their means. -/
private theorem expect_prod_sub_expect_le {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] [DecidableEq X] {m : ℕ} {h : ι → X → Y} (hh : IsKWiseIndependentHash (2 * m) h)
    (R : Finset X) (g : X → Y → ℝ) (hg : ∀ z ∈ R, ∀ y, g z y ∈ Set.Icc 0 1)
    {t : Fin (2 * m) → X} (ht : t ∈ piFinset fun _ => R) :
    𝔼 i, ∏ j, (g (t j) (h i (t j)) - 𝔼 y, g (t j) y) ≤
      if #(univ.image t) ≤ m then ∏ z ∈ univ.image t, 𝔼 y, g z y else 0 := by
  have htR : ∀ z ∈ univ.image t, z ∈ R := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := mem_image.mp hz
    exact mem_piFinset.mp ht j
  -- Group the `2m` factors by key; `2m`-wise independence factors the average over keys.
  have hprod (i : ι) : ∏ j, (g (t j) (h i (t j)) - 𝔼 y, g (t j) y) =
      ∏ z ∈ univ.image t, (g z (h i z) - 𝔼 y, g z y) ^ #{j | t j = z} :=
    prod_comp (fun z => g z (h i z) - 𝔼 y, g z y) t
  simp only [hprod]
  rw [hh.expect_prod (card_image_le.trans (by simp))
    fun z y => (g z y - 𝔼 y', g z y') ^ #{j | t j = z}]
  have hmean0 : 0 ≤ ∏ z ∈ univ.image t, 𝔼 y, g z y :=
    prod_nonneg fun z hz => expect_nonneg fun y _ => (hg z (htR z hz) y).1
  by_cases hsingle : ∃ z ∈ univ.image t, #{j | t j = z} = 1
  · -- A key occurring once contributes the centered average `𝔼 (g z - 𝔼 g z) = 0`.
    obtain ⟨z, hz, hc⟩ := hsingle
    have hzero : 𝔼 y, (g z y - 𝔼 y', g z y') ^ #{j | t j = z} = 0 := by
      simp only [hc, pow_one]
      exact Fintype.expect_balance _
    rw [prod_eq_zero hz hzero]
    split_ifs
    exacts [hmean0, le_rfl]
  · -- Every key occurs at least twice, so at most `m` distinct keys occur.
    push Not at hsingle
    have htwice : ∀ z ∈ univ.image t, 2 ≤ #{j | t j = z} := by
      intro z hz
      obtain ⟨j, -, rfl⟩ := mem_image.mp hz
      have hpos : 0 < #{j' | t j' = t j} := card_pos.mpr ⟨j, by simp⟩
      have := hsingle (t j) hz
      omega
    have hcard : 2 * #(univ.image t) ≤ 2 * m :=
      (mul_card_image_le_card univ 2 htwice).trans_eq (Finset.card_fin _)
    rw [ite_eq_left (by omega)]
    refine (le_abs_self _).trans ?_
    rw [abs_prod]
    exact prod_le_prod₀ (fun _ _ => abs_nonneg _) fun z hz =>
      abs_expect_sub_expect_pow_le (g z) (hg z (htR z hz)) (htwice z hz)

/-- **Tuples with `r ≤ m` distinct keys.** For `2 * m ≤ 3 * μ`, the tuples of
`Fin (2 * m) → R` with exactly `r` distinct keys contribute at most
`(1 / 2) ^ (m - r) * (3 * m * μ) ^ m` to the expanded moment: there are at most
`r ^ (2 * m) / r!` relabelled patterns per weighted choice of keys, `r ^ r ≤ 3 ^ r * r!`, and each
of the `m - r` missing keys trades a factor `2 * m ≤ 3 * μ` for a factor `1 / 2`. -/
private theorem sum_prod_image_card_eq_le_half_pow {X : Type*} [DecidableEq X] (R : Finset X)
    (p : X → ℝ) (hp : ∀ z ∈ R, 0 ≤ p z) {m r : ℕ} (hrm : r ≤ m) {μ : ℝ}
    (hmean : ∑ z ∈ R, p z ≤ μ) (hmμ : 2 * (m : ℝ) ≤ 3 * μ) :
    ∑ t ∈ {t ∈ piFinset (fun _ : Fin (2 * m) => R) | #(univ.image t) = r},
        ∏ z ∈ univ.image t, p z ≤
      ((1 : ℝ) / 2) ^ (m - r) * (3 * (m : ℝ) * μ) ^ m := by
  have hsum0 : 0 ≤ ∑ z ∈ R, p z := sum_nonneg hp
  have hμ0 : 0 ≤ μ := hsum0.trans hmean
  -- `r ^ (2 * m) = r ^ r * r ^ (2 * m - r) ≤ (3 ^ r * r!) * m ^ (2 * m - r)`.
  have hr_pow : r ^ (2 * m) ≤ 3 ^ r * r.factorial * m ^ (2 * m - r) := by
    calc r ^ (2 * m) = r ^ r * r ^ (2 * m - r) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      _ ≤ (3 ^ r * r.factorial) * m ^ (2 * m - r) :=
        Nat.mul_le_mul (Nat.pow_self_le_three_pow_mul_factorial r) (Nat.pow_le_pow_left hrm _)
  have hcount : ∑ t ∈ {t ∈ piFinset (fun _ : Fin (2 * m) => R) | #(univ.image t) = r},
        ∏ z ∈ univ.image t, p z ≤ (3 : ℝ) ^ r * (m : ℝ) ^ (2 * m - r) * μ ^ r := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < r.factorial)
    calc (r.factorial : ℝ) *
          ∑ t ∈ {t ∈ piFinset (fun _ : Fin (2 * m) => R) | #(univ.image t) = r},
            ∏ z ∈ univ.image t, p z
        ≤ (r : ℝ) ^ (2 * m) * (∑ z ∈ R, p z) ^ r := sum_prod_image_card_eq_le R p hp (2 * m) r
      _ ≤ ((3 ^ r * r.factorial * m ^ (2 * m - r) : ℕ) : ℝ) * μ ^ r := by
        gcongr
        exact_mod_cast hr_pow
      _ = (r.factorial : ℝ) * ((3 : ℝ) ^ r * (m : ℝ) ^ (2 * m - r) * μ ^ r) := by
        push_cast
        ring
  -- Each of the `m - r` missing keys trades `m` for `(1 / 2) * (3 * μ)`.
  have hmissing : (m : ℝ) ^ (m - r) ≤ ((1 : ℝ) / 2) ^ (m - r) * (3 * μ) ^ (m - r) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) _
  calc _ ≤ (3 : ℝ) ^ r * (m : ℝ) ^ (2 * m - r) * μ ^ r := hcount
    _ = (m : ℝ) ^ m * (m : ℝ) ^ (m - r) * (3 * μ) ^ r := by
      rw [show 2 * m - r = m + (m - r) by omega, pow_add, mul_pow]
      ring
    _ ≤ (m : ℝ) ^ m * (((1 : ℝ) / 2) ^ (m - r) * (3 * μ) ^ (m - r)) * (3 * μ) ^ r := by gcongr
    _ = ((1 : ℝ) / 2) ^ (m - r) * ((m : ℝ) ^ m * ((3 * μ) ^ (m - r) * (3 * μ) ^ r)) := by ring
    _ = ((1 : ℝ) / 2) ^ (m - r) * (3 * (m : ℝ) * μ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hrm, ← mul_pow]
      ring

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
  let p (z : X) : ℝ := 𝔼 y, g z y
  have hp0 : ∀ z ∈ R, 0 ≤ p z := fun z hz => expect_nonneg fun y _ => (hg z hz y).1
  have hμ0 : 0 ≤ μ := (sum_nonneg hp0).trans hmean
  let S := piFinset fun _ : Fin (2 * m) => R
  -- Group the tuples with at most `m` distinct keys by their number `r ∈ [1, m]` of keys.
  have hpart : (∑ t ∈ S, if #(univ.image t) ≤ m then ∏ z ∈ univ.image t, p z else 0) =
      ∑ r ∈ Icc 1 m, ∑ t ∈ {t ∈ S | #(univ.image t) = r}, ∏ z ∈ univ.image t, p z := by
    rw [← sum_filter, ← sum_fiberwise_of_maps_to (g := fun t => #(univ.image t)) (t := Icc 1 m)]
    · refine sum_congr rfl fun r hr => ?_
      rw [filter_filter]
      refine sum_congr (filter_congr fun t _ => ?_) fun _ _ => rfl
      exact ⟨And.right, fun hcard => ⟨hcard.le.trans (mem_Icc.mp hr).2, hcard⟩⟩
    · intro t ht
      refine mem_Icc.mpr ⟨card_pos.mpr ⟨t ⟨0, by omega⟩, mem_image_of_mem t (mem_univ _)⟩, ?_⟩
      exact (mem_filter.mp ht).2
  -- The geometric factors `(1 / 2) ^ (m - r)` over `r ∈ [1, m]` sum to at most `2`.
  have hgeom : ∑ r ∈ Icc 1 m, ((1 : ℝ) / 2) ^ (m - r) ≤ 2 := by
    have hreflect : ∑ r ∈ Icc 1 m, ((1 : ℝ) / 2) ^ (m - r) =
        ∑ j ∈ range m, ((1 : ℝ) / 2) ^ j := by
      refine sum_nbij' (fun r => m - r) (fun j => m - j) ?_ ?_ ?_ ?_ fun _ _ => rfl
      · intro r hr
        simp only [mem_Icc, mem_range] at hr ⊢
        omega
      · intro j hj
        simp only [mem_Icc, mem_range] at hj ⊢
        omega
      · intro r hr
        simp only [mem_Icc] at hr
        omega
      · intro j hj
        simp only [mem_range] at hj
        omega
    rw [hreflect]
    exact sum_geometric_two_le m
  simp only [sum_pow']
  rw [expect_sum_comm]
  calc ∑ t ∈ S, 𝔼 i, ∏ j, (g (t j) (h i (t j)) - 𝔼 y, g (t j) y)
      ≤ ∑ t ∈ S, if #(univ.image t) ≤ m then ∏ z ∈ univ.image t, p z else 0 :=
        sum_le_sum fun t ht => expect_prod_sub_expect_le hh R g hg ht
    _ = ∑ r ∈ Icc 1 m, ∑ t ∈ {t ∈ S | #(univ.image t) = r}, ∏ z ∈ univ.image t, p z := hpart
    _ ≤ ∑ r ∈ Icc 1 m, ((1 : ℝ) / 2) ^ (m - r) * (3 * (m : ℝ) * μ) ^ m :=
        sum_le_sum fun r hr =>
          sum_prod_image_card_eq_le_half_pow R p hp0 (mem_Icc.mp hr).2 hmean hmμ
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
