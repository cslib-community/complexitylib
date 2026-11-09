/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
import Mathlib.Tactic.Ring

/-!
# Decomposing a function along one coordinate

The function on the cube that reads `f₁` where bit `i` is `true` and `f₀` where it is `false` is
`(f₀ + f₁) / 2 + χ_{i} (f₀ - f₁) / 2` (`BitString.cond_eq_add_chi_mul`), so its Fourier
coefficient on `S` mixes the coefficients of `f₀` and `f₁` on `S` and on `{i} ∆ S`
(`BitString.fourierCoeff_cond`). This is the step behind inductions on decision trees in Fourier
analysis [O'Donnell, Section 3.2][ODonnell2014]. Taking for `f₀` and `f₁` the function `f` with
bit `i` set to `false` and to `true` gives the decomposition `f = Eᵢ f + χ_{i} Dᵢ f` of `f` into
its average over bit `i` and its derivative in `i` (`BitString.eq_add_chi_mul_derivative`)
[O'Donnell, Section 2.2][ODonnell2014].

Averaging over the cube the values of a function at bit `i` equal to `false` and to `true` is
averaging the function (`BitString.expect_update_false_add_update_true`). The coefficient of `f`
on `{i}` is the average of its derivative in `i`
(`BitString.fourierCoeff_singleton_eq_expect_derivative`).

## Main results

* `Cslib.BitString.cond_eq_add_chi_mul`, `Cslib.BitString.fourierCoeff_cond`: the decomposition
  of a branch on bit `i`, and its Fourier coefficients.
* `Cslib.BitString.eq_add_chi_mul_derivative`: the decomposition `f = Eᵢ f + χ_{i} Dᵢ f`.
* `Cslib.BitString.expect_update_false_add_update_true`: averaging over one bit.
* `Cslib.BitString.fourierCoeff_singleton_eq_expect_derivative`: the coefficient on `{i}` is the
  average derivative in `i`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*}

/-- **Decomposition along a bit**: reading `f₁` where bit `i` is `true` and `f₀` where it is
`false` is the average of `f₀` and `f₁` plus `χ_{i}` times half their difference. -/
theorem cond_eq_add_chi_mul (i : ι) (f₀ f₁ : (ι → Bool) → ℝ) (x : ι → Bool) :
    cond (x i) (f₁ x) (f₀ x) = (f₀ x + f₁ x) / 2 + chi ℝ {i} x * ((f₀ x - f₁ x) / 2) := by
  rw [chi_singleton]
  cases x i
  · rw [Bool.cond_false, signVal_false]
    ring
  · rw [Bool.cond_true, signVal_true]
    ring

section DecidableEq

variable [DecidableEq ι]

/-- **The decomposition `f = Eᵢ f + χ_{i} Dᵢ f`**: a function is its average over bit `i` plus
`χ_{i}` times its derivative in `i` [O'Donnell, Section 2.2][ODonnell2014]. -/
theorem eq_add_chi_mul_derivative (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    f x = (f (update x i false) + f (update x i true)) / 2 + chi ℝ {i} x * derivative i f x := by
  have h := cond_eq_add_chi_mul i (fun y => f (update y i false)) (fun y => f (update y i true)) x
  rw [derivative, ← h]
  cases hx : x i
  · rw [Bool.cond_false, update_eq_self_iff.2 hx.symm]
  · rw [Bool.cond_true, update_eq_self_iff.2 hx.symm]

variable [Fintype ι]

/-- **The Fourier coefficients of a branch on bit `i`**: the coefficient on `S` of the function
reading `f₁` where bit `i` is `true` and `f₀` where it is `false` is the average of the
coefficients of `f₀` and `f₁` on `S`, plus half the difference of their coefficients on
`{i} ∆ S`. -/
theorem fourierCoeff_cond (i : ι) (f₀ f₁ : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => cond (x i) (f₁ x) (f₀ x)) S =
      (fourierCoeff f₀ S + fourierCoeff f₁ S) / 2 +
        (fourierCoeff f₀ (symmDiff {i} S) - fourierCoeff f₁ (symmDiff {i} S)) / 2 := by
  have h : (fun x => cond (x i) (f₁ x) (f₀ x)) = fun x =>
      2⁻¹ * (f₀ x + f₁ x) + chi ℝ {i} x * (2⁻¹ * (f₀ x - f₁ x)) := by
    funext x
    rw [cond_eq_add_chi_mul]
    ring
  rw [h, fourierCoeff_add, fourierCoeff_const_mul, fourierCoeff_add, fourierCoeff_chi_mul,
    fourierCoeff_const_mul, fourierCoeff_sub]
  ring

/-- **Averaging over one bit**: averaging over the cube the sum of the values of `φ` at bit `i`
equal to `false` and to `true` gives twice the average of `φ`. -/
theorem expect_update_false_add_update_true (φ : (ι → Bool) → ℝ) (i : ι) :
    𝔼 x, (φ (update x i false) + φ (update x i true)) = 2 * 𝔼 x, φ x := by
  have hpt (x : ι → Bool) : φ (update x i false) + φ (update x i true) =
      φ x + φ (update x i (!x i)) := by
    cases hx : x i
    · rw [show update x i false = x from update_eq_self_iff.2 hx.symm, Bool.not_false]
    · rw [show update x i true = x from update_eq_self_iff.2 hx.symm, Bool.not_true, add_comm]
  have hflip : 𝔼 x, φ (update x i (!x i)) = 𝔼 x, φ x :=
    Fintype.expect_bijective _ (Involutive.bijective fun x => by simp) _ _ fun _ => rfl
  simp only [hpt, expect_add_distrib, hflip]
  ring

/-- The Fourier coefficient of `f` on `{i}` is the average of the derivative of `f` in `i`. -/
theorem fourierCoeff_singleton_eq_expect_derivative (i : ι) (f : (ι → Bool) → ℝ) :
    fourierCoeff f {i} = 𝔼 x, derivative i f x := by
  rw [← fourierCoeff_empty, fourierCoeff_derivative, ite_eq_right (notMem_empty i), insert_empty]

end DecidableEq

end Cslib.BitString
