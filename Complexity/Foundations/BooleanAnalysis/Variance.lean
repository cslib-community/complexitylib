/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Fourier
import Complexity.Foundations.Data.Finset.Variance
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Variance and covariance on the Boolean cube

The covariance of two real functions on the cube is the sum of the products of their Fourier
coefficients on the nonempty sets (`BitString.expect_sub_expect_mul_sub_expect_eq_sum`)
[O'Donnell, Proposition 1.16][ODonnell2014], as the variance is their Fourier weight on the
nonempty sets (`BitString.expect_sub_expect_sq_eq_sum_fourierCoeff_sq`).

For a Boolean function `f` read as the signs `F = (-1) ^ f`, write `dist(f, b)` for the relative
Hamming distance `hammingDist f (fun _ => b) / 2 ^ n` from `f` to the constant `b`; the constant
`false` reads as the sign `1`. The two distances sum to one
(`BitString.hammingDist_false_div_add_hammingDist_true_div`), the mean of `F` is
`1 - 2 dist(f, false)` (`BitString.expect_signVal`), and the variance of `F` is
`1 - (𝔼 F) ^ 2 = 4 dist(f, false) dist(f, true)` (`BitString.expect_sub_expect_sq_signVal`,
`BitString.expect_sub_expect_sq_signVal_eq_four_mul`) [O'Donnell, Fact 1.14][ODonnell2014]. So
the variance is within a factor two of four times the distance `ε` to the nearer constant,
`2 ε ≤ Var[F] ≤ 4 ε` (`BitString.two_mul_min_le_expect_sub_expect_sq_signVal`,
`BitString.expect_sub_expect_sq_signVal_le_four_mul_min`)
[O'Donnell, Proposition 1.15][ODonnell2014].

## Main results

* `Cslib.BitString.expect_sub_expect_mul_sub_expect_eq_sum`: the covariance is the sum of the
  products of the Fourier coefficients on the nonempty sets.
* `Cslib.BitString.expect_sub_expect_sq_signVal`,
  `Cslib.BitString.expect_sub_expect_sq_signVal_eq_four_mul`: the variance of a Boolean function
  read as signs.
* `Cslib.BitString.two_mul_min_le_expect_sub_expect_sq_signVal`,
  `Cslib.BitString.expect_sub_expect_sq_signVal_le_four_mul_min`: the variance is between twice and
  four times the distance to the nearer constant.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The covariance is the sum of the products of the Fourier coefficients on the nonempty
sets** [O'Donnell, Proposition 1.16][ODonnell2014]. -/
theorem expect_sub_expect_mul_sub_expect_eq_sum (f g : (ι → Bool) → ℝ) :
    𝔼 x, (f x - 𝔼 y, f y) * (g x - 𝔼 y, g y) =
      ∑ S with S ≠ ∅, fourierCoeff f S * fourierCoeff g S := by
  rw [expect_mul_eq_sum_fourierCoeff_mul, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_sub, fourierCoeff_sub, fourierCoeff_const, fourierCoeff_const,
    ← fourierCoeff_empty, ← fourierCoeff_empty]
  by_cases hS : S = ∅ <;> simp [hS]

/-- The mean of a Boolean function read as signs is one minus twice its relative Hamming distance
to the constant `false`, whose sign is `1`. -/
theorem expect_signVal (f : (ι → Bool) → Bool) :
    𝔼 x, signVal (f x) = 1 - 2 * hammingDist f (fun _ => false) / 2 ^ Fintype.card ι := by
  simpa using expect_signVal_mul_signVal f fun _ => false

/-- The relative Hamming distances from a Boolean function to the two constants sum to one. -/
theorem hammingDist_false_div_add_hammingDist_true_div (f : (ι → Bool) → Bool) :
    (hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι +
      hammingDist f (fun _ => true) / 2 ^ Fintype.card ι = 1 := by
  have h₀ := expect_signVal f
  have h₁ := expect_signVal_mul_signVal f fun _ => true
  simp only [signVal_true, mul_neg, mul_one, expect_neg_distrib] at h₁
  rw [mul_div_assoc] at h₀ h₁
  linarith

/-- **The variance of a Boolean function** read as signs is one minus its squared mean
[O'Donnell, Fact 1.14][ODonnell2014]. -/
theorem expect_sub_expect_sq_signVal (f : (ι → Bool) → Bool) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 = 1 - (𝔼 x, signVal (f x)) ^ 2 := by
  rw [Fintype.expect_sub_expect_sq]
  simp only [sq, signVal_mul_self, Fintype.expect_const]

/-- **The variance of a Boolean function** read as signs is four times the product of its
relative Hamming distances to the two constants [O'Donnell, Fact 1.14][ODonnell2014]. -/
theorem expect_sub_expect_sq_signVal_eq_four_mul (f : (ι → Bool) → Bool) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 =
      4 * ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι) *
        (hammingDist f (fun _ => true) / 2 ^ Fintype.card ι) := by
  have h := hammingDist_false_div_add_hammingDist_true_div f
  rw [expect_sub_expect_sq_signVal, expect_signVal, mul_div_assoc]
  linear_combination (-4 * ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι)) * h

/-- For `a, b ≥ 0` with `a + b = 1`, `4 a b` is between twice and four times `min a b`. -/
private theorem two_mul_min_le_four_mul_mul_and_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 2 * min a b ≤ 4 * a * b ∧ 4 * a * b ≤ 4 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    exact ⟨by nlinarith, by nlinarith⟩
  · rw [min_eq_right h]
    exact ⟨by nlinarith, by nlinarith⟩

/-- The relative Hamming distance from a Boolean function to a constant is nonnegative. -/
private theorem hammingDist_div_nonneg (f : (ι → Bool) → Bool) (b : Bool) :
    0 ≤ (hammingDist f (fun _ => b) : ℝ) / 2 ^ Fintype.card ι := by
  positivity

/-- **The variance is at least twice the distance to the nearer constant**: a Boolean function
read as signs has variance at least `2 ε`, where `ε` is its relative Hamming distance to the
nearer constant [O'Donnell, Proposition 1.15][ODonnell2014]. -/
theorem two_mul_min_le_expect_sub_expect_sq_signVal (f : (ι → Bool) → Bool) :
    2 * min ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι)
        (hammingDist f (fun _ => true) / 2 ^ Fintype.card ι) ≤
      𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 := by
  rw [expect_sub_expect_sq_signVal_eq_four_mul]
  exact (two_mul_min_le_four_mul_mul_and_le (hammingDist_div_nonneg f false)
    (hammingDist_div_nonneg f true) (hammingDist_false_div_add_hammingDist_true_div f)).1

/-- **The variance is at most four times the distance to the nearer constant**: a Boolean function
read as signs has variance at most `4 ε`, where `ε` is its relative Hamming distance to the
nearer constant [O'Donnell, Proposition 1.15][ODonnell2014]. -/
theorem expect_sub_expect_sq_signVal_le_four_mul_min (f : (ι → Bool) → Bool) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ≤
      4 * min ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι)
        (hammingDist f (fun _ => true) / 2 ^ Fintype.card ι) := by
  rw [expect_sub_expect_sq_signVal_eq_four_mul]
  exact (two_mul_min_le_four_mul_mul_and_le (hammingDist_div_nonneg f false)
    (hammingDist_div_nonneg f true) (hammingDist_false_div_add_hammingDist_true_div f)).2

end Cslib.BitString
