/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/MeanInequalities.lean`)

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
O'Donnell's proof of Theorem 9.22 [O'Donnell, Section 9.5][ODonnell2014].

## Main results

* `Fintype.expect_mul_le_rpow_mul_rpow`: Hölder's inequality for uniform averages.
* `Fintype.expect_rpow_le_rpow_mul_rpow`: log-convexity of moments.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open Finset
open scoped BigOperators

namespace Fintype

variable {α : Type*} [Fintype α]

/-- **Hölder's inequality** for uniform averages: for nonnegative `f`, `g` and Hölder conjugate
exponents `p`, `q`, `𝔼 f g ≤ (𝔼 f ^ p) ^ (1 / p) (𝔼 g ^ q) ^ (1 / q)`. -/
theorem expect_mul_le_rpow_mul_rpow {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    𝔼 x, f x * g x ≤ (𝔼 x, f x ^ p) ^ (1 / p) * (𝔼 x, g x ^ q) ^ (1 / q) := by
  cases isEmpty_or_nonempty α with
  | inl h =>
    simp only [univ_eq_empty, expect_empty]
    positivity
  | inr h =>
    have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    have hH := Real.inner_le_Lp_mul_Lq_of_nonneg univ hpq (fun x _ => hf x) (fun x _ => hg x)
    simp only [Fintype.expect_eq_sum_div_card]
    rw [Real.div_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hf x) _) hN.le,
      Real.div_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hg x) _) hN.le,
      div_mul_div_comm, ← Real.rpow_add hN, hpq.one_div_add_one_div, one_div_one, Real.rpow_one]
    exact div_le_div_of_nonneg_right hH hN.le

/-- **Log-convexity of moments**: for nonnegative `f`, `0 < θ < 1` and `p, q ≥ 0`,
`𝔼 f ^ (θ p + (1 - θ) q) ≤ (𝔼 f ^ p) ^ θ (𝔼 f ^ q) ^ (1 - θ)`. This is Hölder's inequality with
the exponents `1 / θ` and `1 / (1 - θ)`. -/
theorem expect_rpow_le_rpow_mul_rpow {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) {θ p q : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    𝔼 x, f x ^ (θ * p + (1 - θ) * q) ≤ (𝔼 x, f x ^ p) ^ θ * (𝔼 x, f x ^ q) ^ (1 - θ) := by
  have hθ' : 0 < 1 - θ := by linarith
  have hpq : (1 / θ).HolderConjugate (1 / (1 - θ)) :=
    { inv_add_inv_eq_inv := by simp only [one_div, inv_inv, inv_one]; ring
      left_pos := by positivity
      right_pos := by positivity }
  have h := expect_mul_le_rpow_mul_rpow (f := fun x => f x ^ (θ * p))
    (g := fun x => f x ^ ((1 - θ) * q)) (fun x => Real.rpow_nonneg (hf x) _)
    (fun x => Real.rpow_nonneg (hf x) _) hpq
  have e1 (x : α) : f x ^ (θ * p) * f x ^ ((1 - θ) * q) = f x ^ (θ * p + (1 - θ) * q) :=
    (Real.rpow_add_of_nonneg (hf x) (by positivity) (by positivity)).symm
  have e2 (x : α) : (f x ^ (θ * p)) ^ (1 / θ) = f x ^ p := by
    rw [← Real.rpow_mul (hf x), mul_comm θ p, mul_assoc, mul_one_div_cancel hθ₀.ne', mul_one]
  have e3 (x : α) : (f x ^ ((1 - θ) * q)) ^ (1 / (1 - θ)) = f x ^ q := by
    rw [← Real.rpow_mul (hf x), mul_comm (1 - θ) q, mul_assoc, mul_one_div_cancel hθ'.ne',
      mul_one]
  simp only [e1, e2, e3, one_div_one_div] at h
  exact h

end Fintype
