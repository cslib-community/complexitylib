/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/MeanInequalities.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.ConjExponents
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.MeanInequalities

/-!
# Hölder's inequality for uniform averages

For nonnegative functions `f`, `g` on a finite type and Hölder conjugate exponents `p`, `q`,
`𝔼 f g ≤ (𝔼 f ^ p) ^ (1 / p) (𝔼 g ^ q) ^ (1 / q)` (`Fintype.expect_mul_le_rpow_mul_rpow`): this
is **Hölder's inequality** for the uniform distribution, the averaged form of Mathlib's
`Real.inner_le_Lp_mul_Lq_of_nonneg`. Its consequence used for hypercontractivity is the
**log-convexity of moments**: for `0 < θ < 1` and `p, q ≥ 0`,
`𝔼 f ^ (θ p + (1 - θ) q) ≤ (𝔼 f ^ p) ^ θ (𝔼 f ^ q) ^ (1 - θ)`
(`Fintype.expect_rpow_le_rpow_mul_rpow`), the "general version of Hölder's inequality" in
O'Donnell's proof of Theorem 9.22 [O'Donnell, Section 9.5][ODonnell2014]. Both are stated first
for averages `𝔼 i ∈ s` over a finset `s`, with nonnegativity required only on `s`, and the
uniform-average forms are their instances at `s = univ`.

## Main results

* `Finset.expect_mul_le_rpow_mul_rpow`: Hölder's inequality for averages over a finset.
* `Finset.expect_rpow_le_rpow_mul_rpow`: log-convexity of moments over a finset.
* `Fintype.expect_mul_le_rpow_mul_rpow`: Hölder's inequality for uniform averages.
* `Fintype.expect_rpow_le_rpow_mul_rpow`: log-convexity of moments.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open Finset
open scoped BigOperators

namespace Finset

variable {ι : Type*}

/-- **Hölder's inequality** for averages over a finset: for `f`, `g` nonnegative on `s` and Hölder
conjugate exponents `p`, `q`,
`𝔼_s f g ≤ (𝔼_s f ^ p) ^ (1 / p) (𝔼_s g ^ q) ^ (1 / q)`. -/
theorem expect_mul_le_rpow_mul_rpow (s : Finset ι) {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) {p q : ℝ} (hpq : p.HolderConjugate q) :
    𝔼 i ∈ s, f i * g i ≤ (𝔼 i ∈ s, f i ^ p) ^ (1 / p) * (𝔼 i ∈ s, g i ^ q) ^ (1 / q) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [expect_empty]
    positivity
  · have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
    have hH := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq hf hg
    simp only [expect_eq_sum_div_card]
    rw [Real.div_rpow (sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _) hN.le,
      Real.div_rpow (sum_nonneg fun i hi => Real.rpow_nonneg (hg i hi) _) hN.le,
      div_mul_div_comm, ← Real.rpow_add hN, hpq.one_div_add_one_div, one_div_one, Real.rpow_one]
    exact div_le_div_of_nonneg_right hH hN.le

/-- **Log-convexity of moments** for averages over a finset: for `f` nonnegative on `s`,
`0 < θ < 1` and `p, q ≥ 0`, `𝔼_s f ^ (θ p + (1 - θ) q) ≤ (𝔼_s f ^ p) ^ θ (𝔼_s f ^ q) ^ (1 - θ)`.
This is Hölder's inequality with the exponents `1 / θ` and `1 / (1 - θ)`. -/
theorem expect_rpow_le_rpow_mul_rpow (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    {θ p q : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    𝔼 i ∈ s, f i ^ (θ * p + (1 - θ) * q) ≤
      (𝔼 i ∈ s, f i ^ p) ^ θ * (𝔼 i ∈ s, f i ^ q) ^ (1 - θ) := by
  have hθ' : 0 < 1 - θ := by linarith
  have hpq : (1 / θ).HolderConjugate (1 / (1 - θ)) :=
    { inv_add_inv_eq_inv := by simp only [one_div, inv_inv, inv_one]; ring
      left_pos := by positivity
      right_pos := by positivity }
  have h : 𝔼 i ∈ s, f i ^ (θ * p) * f i ^ ((1 - θ) * q) ≤
      (𝔼 i ∈ s, (f i ^ (θ * p)) ^ (1 / θ)) ^ (1 / (1 / θ)) *
        (𝔼 i ∈ s, (f i ^ ((1 - θ) * q)) ^ (1 / (1 - θ))) ^ (1 / (1 / (1 - θ))) :=
    expect_mul_le_rpow_mul_rpow s (fun i hi => Real.rpow_nonneg (hf i hi) _)
      (fun i hi => Real.rpow_nonneg (hf i hi) _) hpq
  have e1 : 𝔼 i ∈ s, f i ^ (θ * p) * f i ^ ((1 - θ) * q) =
      𝔼 i ∈ s, f i ^ (θ * p + (1 - θ) * q) :=
    expect_congr rfl fun i hi =>
      (Real.rpow_add_of_nonneg (hf i hi) (by positivity) (by positivity)).symm
  have e2 : 𝔼 i ∈ s, (f i ^ (θ * p)) ^ (1 / θ) = 𝔼 i ∈ s, f i ^ p :=
    expect_congr rfl fun i hi => by
      rw [← Real.rpow_mul (hf i hi), mul_comm θ p, mul_assoc, mul_one_div_cancel hθ₀.ne',
        mul_one]
  have e3 : 𝔼 i ∈ s, (f i ^ ((1 - θ) * q)) ^ (1 / (1 - θ)) = 𝔼 i ∈ s, f i ^ q :=
    expect_congr rfl fun i hi => by
      rw [← Real.rpow_mul (hf i hi), mul_comm (1 - θ) q, mul_assoc, mul_one_div_cancel hθ'.ne',
        mul_one]
  rwa [e1, e2, e3, one_div_one_div, one_div_one_div] at h

end Finset

namespace Fintype

variable {α : Type*} [Fintype α]

/-- **Hölder's inequality** for uniform averages: for nonnegative `f`, `g` and Hölder conjugate
exponents `p`, `q`, `𝔼 f g ≤ (𝔼 f ^ p) ^ (1 / p) (𝔼 g ^ q) ^ (1 / q)`. -/
theorem expect_mul_le_rpow_mul_rpow {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    𝔼 x, f x * g x ≤ (𝔼 x, f x ^ p) ^ (1 / p) * (𝔼 x, g x ^ q) ^ (1 / q) :=
  Finset.expect_mul_le_rpow_mul_rpow univ (fun x _ => hf x) (fun x _ => hg x) hpq

/-- **Log-convexity of moments**: for nonnegative `f`, `0 < θ < 1` and `p, q ≥ 0`,
`𝔼 f ^ (θ p + (1 - θ) q) ≤ (𝔼 f ^ p) ^ θ (𝔼 f ^ q) ^ (1 - θ)`. This is Hölder's inequality with
the exponents `1 / θ` and `1 / (1 - θ)`. -/
theorem expect_rpow_le_rpow_mul_rpow {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) {θ p q : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    𝔼 x, f x ^ (θ * p + (1 - θ) * q) ≤ (𝔼 x, f x ^ p) ^ θ * (𝔼 x, f x ^ q) ^ (1 - θ) :=
  Finset.expect_rpow_le_rpow_mul_rpow univ (fun x _ => hf x) hθ₀ hθ₁ hp hq

end Fintype
