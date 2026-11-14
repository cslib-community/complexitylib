/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Monotone
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
import CslibFrontier.Foundations.Data.BitString.Balanced
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Majority maximizes the sum of the degree-one coefficients

The degree-one Fourier coefficients of a real function `f` on the cube sum to its correlation with
`x₁ + ⋯ + xₙ`, the sum of the signs of the bits (`BitString.sum_fourierCoeff_singleton_eq_expect`
in `BooleanAnalysis.LevelWeight`) [O'Donnell, equation (2.3)][ODonnell2014]. For a Boolean
function read as signs `F` viewed as a two-candidate voting rule, this gives the expected number
of voters who agree with the outcome, `n / 2 + ½ ∑ᵢ F̂(i)` (`BitString.expect_card_agree`)
[O'Donnell, Proposition 2.32][ODonnell2014].

Since `F(x) (x₁ + ⋯ + xₙ) ≤ |x₁ + ⋯ + xₙ|`, the sum `∑ᵢ F̂(i)` is at most `𝔼 |x₁ + ⋯ + xₙ|`
(`BitString.sum_fourierCoeff_singleton_signVal_le`), with equality exactly for the *majority
functions*, those with `F(x) = sgn(x₁ + ⋯ + xₙ)` wherever `x₁ + ⋯ + xₙ ≠ 0`, that is,
`F(x) (x₁ + ⋯ + xₙ) ≥ 0` everywhere (`BitString.sum_fourierCoeff_singleton_signVal_eq_iff`).
So the majority functions are the unique maximizers of `∑ᵢ F̂(i)`
[O'Donnell, Definition 2.1, Theorem 2.33 and its proof][ODonnell2014]. The library's
`Cslib.majority n` is a majority function for every `n`, breaking ties towards `true`, the book's
`-1` (`BitString.signVal_majority_mul_sum_signVal_nonneg`); for odd `n` it is the book's `Majₙ`.
So it maximizes `∑ᵢ F̂(i)` (`BitString.sum_fourierCoeff_singleton_le_majority`), uniquely for odd
`n` (`BitString.sum_fourierCoeff_singleton_eq_majority_iff`).

A monotone Boolean function has total influence `∑ᵢ F̂(i)`
(`BitString.totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone`)
[O'Donnell, Proposition 2.31][ODonnell2014], so among monotone functions the majority has the
largest total influence (`BitString.totalInfluence_le_majority_of_monotone`)
[O'Donnell, Theorem 2.33][ODonnell2014]. The asymptotic value `I[Majₙ] = √(2/π) √n + O(n^{-1/2})`
of the book's statement is not part of this module.

## Main results

* `Cslib.BitString.expect_card_agree`: the expected number of voters agreeing with the outcome.
* `Cslib.BitString.sum_fourierCoeff_singleton_signVal_le`,
  `Cslib.BitString.sum_fourierCoeff_singleton_signVal_eq_iff`: the majority functions are the
  maximizers of `∑ᵢ F̂(i)`.
* `Cslib.BitString.sum_fourierCoeff_singleton_le_majority`: the majority maximizes `∑ᵢ F̂(i)`.
* `Cslib.BitString.sum_fourierCoeff_singleton_eq_majority_iff`: for odd `n` it is the unique
  maximizer.
* `Cslib.BitString.totalInfluence_le_majority_of_monotone`: monotone functions have total
  influence at most that of the majority.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The expected number of voters agreeing with the outcome**: for a Boolean function `f` as a
two-candidate voting rule, the expected number of coordinates `i` with `xᵢ = f(x)` is
`n / 2 + ½ ∑ᵢ F̂(i)` [O'Donnell, Proposition 2.32][ODonnell2014]. -/
theorem expect_card_agree (f : (ι → Bool) → Bool) :
    𝔼 x, (#{i | x i = f x} : ℝ) =
      Fintype.card ι / 2 + (∑ i, fourierCoeff (fun x => signVal (f x)) {i}) / 2 := by
  have h (x : ι → Bool) : (#{i | x i = f x} : ℝ) =
      Fintype.card ι / 2 + signVal (f x) * (∑ i, signVal (x i)) / 2 := by
    rw [natCast_card_filter]
    calc ∑ i, (if x i = f x then (1 : ℝ) else 0)
        = ∑ i, (1 + signVal (f x) * signVal (x i)) / 2 :=
          sum_congr rfl fun i _ => by cases f x <;> cases x i <;> norm_num
      _ = Fintype.card ι / 2 + signVal (f x) * (∑ i, signVal (x i)) / 2 := by
          rw [← sum_div, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← mul_sum,
            add_div]
  rw [sum_fourierCoeff_singleton_eq_expect, expect_div]
  simp only [h, expect_add_distrib, Fintype.expect_const]

/-- The degree-one Fourier coefficients of a Boolean function read as signs sum to at most
`𝔼 |x₁ + ⋯ + xₙ|` [O'Donnell, proof of Theorem 2.33][ODonnell2014]. -/
theorem sum_fourierCoeff_singleton_signVal_le (f : (ι → Bool) → Bool) :
    ∑ i, fourierCoeff (fun x => signVal (f x)) {i} ≤ 𝔼 x : ι → Bool, |∑ i, signVal (x i)| := by
  rw [sum_fourierCoeff_singleton_eq_expect]
  exact expect_le_expect fun x _ => signVal_mul_le_abs _ _

/-- **The majority functions are the maximizers**: the degree-one Fourier coefficients of a
Boolean function read as signs sum to `𝔼 |x₁ + ⋯ + xₙ|`, their maximum, exactly when it is a
majority function, `F(x) (x₁ + ⋯ + xₙ) ≥ 0` everywhere, that is, `F(x) = sgn(x₁ + ⋯ + xₙ)`
wherever the sum is nonzero
[O'Donnell, Definition 2.1, Theorem 2.33 and its proof][ODonnell2014]. -/
theorem sum_fourierCoeff_singleton_signVal_eq_iff (f : (ι → Bool) → Bool) :
    ∑ i, fourierCoeff (fun x => signVal (f x)) {i} = 𝔼 x : ι → Bool, |∑ i, signVal (x i)| ↔
      ∀ x, 0 ≤ signVal (f x) * ∑ i, signVal (x i) := by
  rw [sum_fourierCoeff_singleton_eq_expect]
  constructor
  · intro h x
    have hz := (Fintype.expect_eq_zero_iff_of_nonneg fun y =>
      sub_nonneg.2 (signVal_mul_le_abs (f y) (∑ i, signVal (y i)))).1
      (by rw [expect_sub_distrib, h, sub_self])
    exact (sub_eq_zero.1 (congrFun hz x)) ▸ abs_nonneg _
  · intro h
    exact expect_congr rfl fun x _ => by rw [← abs_of_nonneg (h x), abs_mul, abs_signVal, one_mul]

/-- **The majority is a majority function**: for every `n`, the majority of `n` bits read as
signs satisfies `F(x) (x₁ + ⋯ + xₙ) ≥ 0`; on a tie it is `true`, the book's `-1`
[O'Donnell, Definition 2.1][ODonnell2014]. -/
theorem signVal_majority_mul_sum_signVal_nonneg {n : ℕ} (x : BitString n) :
    0 ≤ signVal (majority n x) * ∑ i, signVal (x i) := by
  rw [sum_signVal_eq_card_sub_two_mul_weight, Fintype.card_fin]
  by_cases h : (n + 1) / 2 ≤ weight x
  · rw [majority_eq_true_iff.2 h, signVal_true, neg_one_mul, neg_nonneg, sub_nonpos]
    exact_mod_cast (by omega : n ≤ 2 * weight x)
  · rw [Bool.eq_false_iff.2 (mt majority_eq_true_iff.1 h), signVal_false, one_mul, sub_nonneg]
    exact_mod_cast (by omega : 2 * weight x ≤ n)

/-- The degree-one Fourier coefficients of the majority of `n` bits, read as signs, sum to
`𝔼 |x₁ + ⋯ + xₙ|`. -/
theorem sum_fourierCoeff_singleton_majority (n : ℕ) :
    ∑ i, fourierCoeff (fun x => signVal (majority n x)) {i} =
      𝔼 x : BitString n, |∑ i, signVal (x i)| :=
  (sum_fourierCoeff_singleton_signVal_eq_iff _).2 signVal_majority_mul_sum_signVal_nonneg

/-- **The majority maximizes the sum of the degree-one coefficients**: every Boolean function of
`n` bits, read as signs, has degree-one Fourier coefficients summing to at most those of the
majority [O'Donnell, Theorem 2.33][ODonnell2014]. -/
theorem sum_fourierCoeff_singleton_le_majority {n : ℕ} (f : BooleanFunction n) :
    ∑ i, fourierCoeff (fun x => signVal (f x)) {i} ≤
      ∑ i, fourierCoeff (fun x => signVal (majority n x)) {i} :=
  (sum_fourierCoeff_singleton_signVal_le f).trans_eq (sum_fourierCoeff_singleton_majority n).symm

/-- **For odd `n` the majority is the unique maximizer**: a Boolean function of an odd number of
bits, read as signs, has degree-one Fourier coefficients summing to those of the majority only if
it is the majority [O'Donnell, Theorem 2.33][ODonnell2014]. -/
theorem sum_fourierCoeff_singleton_eq_majority_iff {n : ℕ} (hn : Odd n) (f : BooleanFunction n) :
    ∑ i, fourierCoeff (fun x => signVal (f x)) {i} =
        ∑ i, fourierCoeff (fun x => signVal (majority n x)) {i} ↔ f = majority n := by
  refine ⟨fun h => funext fun x => ?_, fun h => h ▸ rfl⟩
  rw [sum_fourierCoeff_singleton_majority, sum_fourierCoeff_singleton_signVal_eq_iff] at h
  -- The sum of an odd number of signs is odd, so it is not zero.
  have hS : ∑ i, signVal (x i) ≠ 0 := by
    rw [sum_signVal_eq_card_sub_two_mul_weight, Fintype.card_fin, sub_ne_zero]
    intro h'
    obtain ⟨k, hk⟩ := hn
    have : n = 2 * weight x := by exact_mod_cast h'
    omega
  have h1 := h x
  have h2 := signVal_majority_mul_sum_signVal_nonneg x
  cases hf : f x <;> cases hm : majority n x <;>
    simp only [hf, hm, signVal_true, signVal_false, one_mul, neg_one_mul, neg_nonneg] at h1 h2 ⊢ <;>
    exact (hS (by linarith)).elim

/-- **The majority has the largest total influence among monotone functions**: a monotone Boolean
function of `n` bits has total influence at most that of the majority, the inequality of
[O'Donnell, Theorem 2.33][ODonnell2014]; the asymptotic value of `I[Majₙ]` is not part of this
module.
For even `n` the comparison is with the majority breaking ties towards `true`, the book's `-1`. -/
theorem totalInfluence_le_majority_of_monotone {n : ℕ} {f : BooleanFunction n}
    (hf : Monotone f) :
    totalInfluence (fun x => signVal (f x)) ≤ totalInfluence (fun x => signVal (majority n x)) := by
  rw [totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone hf,
    totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone monotone_majority]
  exact sum_fourierCoeff_singleton_le_majority f

end Cslib.BitString
