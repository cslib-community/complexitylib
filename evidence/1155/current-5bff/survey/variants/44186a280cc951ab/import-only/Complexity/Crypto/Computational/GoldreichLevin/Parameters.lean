/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GoldreichLevin.Reduction
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
public import Mathlib.Data.Nat.Log
public import Complexity.Crypto.Game
import Complexity.Crypto.Negligible.Basic


import Diag1155.Measure
/-!
# Goldreich–Levin parameters and the asymptotic reduction

The decoder uses `maskCount n p = log₂ (2 * n * p² + 1) + 1` base masks at precision `1 / p`.
For `p > 0` this satisfies the finite recovery bound. At every precision it enumerates at most
`4 * n * p² + 2` guesses.
For the fixed-degree precision `(n + 1)^degree`, both the list size and random-mask length are
polynomially bounded. These are explicit size bounds, not machine-runtime certificates.

The prediction advantage is at most `1 / p + 8 * inversion_success`. Consequently, if the
inverter at each fixed precision degree has negligible success, prediction bias is negligible.
Each degree defines one inverter for all lengths. No length-dependent choice of adversary or
sign of the bias is used. One-wayness can discharge these success hypotheses once the
word-based game correspondence and uniform PPT certificates for the inverters are proved.
Adapted from the cslib `crypto` branch at `5ff69ca`.

## Main definitions

* `maskCount`: the logarithmic number of base masks.
* `precision`: a fixed inverse-polynomial accuracy denominator.

## Main results

* `guessCount_maskCount_le`, `maskCount_sufficient`: output-size and recovery bounds.
* `guessCount_polynomial`, `randomMaskBits_polynomial`: polynomially bounded enumeration and coins.
* `negligible_prediction_of_negligible_inversion`: each fixed-precision inverter's negligible
  success implies negligible prediction bias, in the shared nonnegative game API.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [L. Trevisan, *CS276 Lecture 12: Goldreich–Levin*][Trevisan2009GL]
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin
open Probability

/-- A computable number of base masks sufficient for prediction bias at least `1 / precision`. -/
def maskCount (n precision : ℕ) : ℕ := Nat.log 2 (2 * n * precision ^ 2 + 1) + 1

/-- At least one base mask is used, including at dimension zero. -/
theorem maskCount_pos (n precision : ℕ) : 0 < maskCount n precision := by
  simp [maskCount]

/-- The subset masks meet the recovery theorem's required count. -/
theorem subsetCount_maskCount_ge (n precision : ℕ) :
    2 * n * precision ^ 2 ≤ 2 ^ maskCount n precision - 1 := by
  have h := Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * n * precision ^ 2 + 1)
  change 2 * n * precision ^ 2 + 1 < 2 ^ maskCount n precision at h
  lia

/-- Rounding the mask count up costs at most a factor of two in the number of guesses. -/
theorem guessCount_maskCount_le (n precision : ℕ) :
    2 ^ maskCount n precision ≤ 4 * n * precision ^ 2 + 2 := by
  have h := Nat.pow_log_le_self 2 (x := 2 * n * precision ^ 2 + 1) (by lia)
  unfold maskCount
  rw [pow_succ]
  calc
    _ ≤ (2 * n * precision ^ 2 + 1) * 2 := Nat.mul_le_mul_right 2 h
    _ = _ := by ring

/-- A simple polynomial upper bound also controls the base-mask count. -/
theorem maskCount_le (n precision : ℕ) : maskCount n precision ≤ 2 * n * precision ^ 2 + 1 := by
  have h := Nat.log_lt_self 2 (x := 2 * n * precision ^ 2 + 1) (by lia)
  unfold maskCount
  lia

/-- The chosen count satisfies the exact real-valued inequality used by the finite reduction. -/
theorem maskCount_sufficient (n precision : ℕ) (hp : 0 < precision) :
    (n : ℝ) ≤ 2 * ((1 / (precision : ℝ)) / 2) ^ 2 *
      (2 ^ maskCount n precision - 1 : ℕ) := by
  have h := subsetCount_maskCount_ge n precision
  have hreal : 2 * (n : ℝ) * (precision : ℝ) ^ 2 ≤
      (2 ^ maskCount n precision - 1 : ℕ) := by exact_mod_cast h
  have hpReal : (0 : ℝ) < precision := by exact_mod_cast hp
  have heq : 2 * ((1 / (precision : ℝ)) / 2) ^ 2 *
      (2 ^ maskCount n precision - 1 : ℕ) =
      (2 ^ maskCount n precision - 1 : ℕ) / (2 * (precision : ℝ) ^ 2) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  nlinarith

/-- Signed parity correlation is bounded by decoder success and its chosen accuracy.
This pointwise form allows auxiliary input to be guessed in later reductions. -/
theorem correlation_le_invertFixed {n : ℕ} {Image : Type*} [DecidableEq Image]
    (f : BitString n → Image) (predictor : BitString n → Bool) (x : BitString n)
    (precision : ℕ) (hp : 0 < precision) :
    2 * agreement predictor x - 1 ≤ 1 / (precision : ℝ) +
      2 * (((invertFixed f predictor (maskCount n precision) (f x)).map
        (fun z => f z == f x)) true).toReal := by
  have hpReal : (0 : ℝ) < precision := by exact_mod_cast hp
  by_cases h : 1 / 2 + (1 / (precision : ℝ)) / 2 ≤ agreement predictor x
  · have hsuccess := invertFixed_success_ge_half f predictor x _
      (by positivity : 0 < (1 / (precision : ℝ)) / 2) (maskCount_pos n precision) h
      (maskCount_sufficient n precision hp)
    linarith [agreement_le_one predictor x, one_div_pos.mpr hpReal]
  · have hsuccess : 0 ≤ (((invertFixed f predictor (maskCount n precision) (f x)).map
        (fun z => f z == f x)) true).toReal := ENNReal.toReal_nonneg
    linarith

/-- The same inverter bounds all prediction biases, with an additive error of `1 / precision`.
When the actual bias exceeds that error, the recovery bound applies to the actual bias itself. -/
theorem invertSigned_advantage_le {n : ℕ} {Image : Type*} [DecidableEq Image]
    {Coins : Image → Type*} [∀ image, Finite (Coins image)]
    (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) (precision : ℕ) (hp : 0 < precision) :
    |(predictionExperiment f predictor coins true).toReal - 1 / 2| ≤
      1 / (precision : ℝ) +
        8 * (inversionExperiment f
          (invertSigned f predictor coins (maskCount n precision)) true).toReal := by
  let bias := |(predictionExperiment f predictor coins true).toReal - 1 / 2|
  have hpReal : (0 : ℝ) < precision := by exact_mod_cast hp
  have hsuccess : 0 ≤ (inversionExperiment f
      (invertSigned f predictor coins (maskCount n precision)) true).toReal :=
    ENNReal.toReal_nonneg
  by_cases h : 1 / (precision : ℝ) ≤ bias
  · have hb : 0 < bias := lt_of_lt_of_le (by positivity) h
    have hsize : (n : ℝ) ≤
        2 * (bias / 2) ^ 2 * (2 ^ maskCount n precision - 1 : ℕ) := by
      apply (maskCount_sufficient n precision hp).trans
      gcongr
    have hi := invertSigned_success_ge f predictor coins bias hb
      (maskCount_pos n precision) le_rfl hsize
    change bias ≤ _
    linarith [one_div_pos.mpr hpReal]
  · change bias ≤ _
    linarith

/-- A fixed degree selects an inverse-polynomial accuracy for every input length. -/
def precision (degree n : ℕ) : ℕ := (n + 1) ^ degree

/-- The precision denominator never vanishes. -/
theorem precision_pos (degree n : ℕ) : 0 < precision degree n := by
  simp [precision]

/-- Enumerating the guesses uses a polynomial-size list at any fixed precision degree. -/
theorem guessCount_polynomial (degree : ℕ) :
    PolynomiallyBounded (fun n => 2 ^ maskCount n (precision degree n)) := by
  have hbound : PolynomiallyBounded (fun n => 4 * n * precision degree n ^ 2 + 2) := by
    unfold precision
    fun_prop
  exact hbound.mono_of_le (fun n => guessCount_maskCount_le n _)

/-- The logarithmic mask count is polynomially bounded at each fixed precision degree. -/
theorem maskCount_polynomial (degree : ℕ) :
    PolynomiallyBounded (fun n => maskCount n (precision degree n)) := by
  unfold maskCount precision
  fun_prop

/-- Storing all base masks uses polynomially many bits at any fixed precision degree. -/
theorem randomMaskBits_polynomial (degree : ℕ) :
    PolynomiallyBounded (fun n => n * maskCount n (precision degree n)) :=
  PolynomiallyBounded.id.mul (maskCount_polynomial degree)

/-- If every fixed-precision inverter has negligible success, prediction bias is negligible.
For each power, multiply the pointwise reduction by that power of the parameter. The precision
term is at most one and the inversion term tends to zero, giving superpolynomial decay. -/
theorem negligible_prediction_of_negligible_inversion
    {Image : ℕ → Type*} [∀ n, DecidableEq (Image n)]
    {Coins : (n : ℕ) → Image n → Type*} [∀ n image, Finite (Coins n image)]
    (f : (n : ℕ) → BitString n → Image n)
    (predictor : (n : ℕ) → (image : Image n) → Coins n image → BitString n → Bool)
    (coins : (n : ℕ) → (image : Image n) → PMF (Coins n image))
    (hinversion : ∀ degree, Negligible (fun n =>
      Game.succProbability (inversionExperiment (f n)
        (invertSigned (f n) (predictor n) (coins n)
          (maskCount n (precision degree n)))))) :
    Negligible (fun n => Game.guessingAdvantage
      (predictionExperiment (f n) (predictor n) (coins n))) := by
  apply negligible_iff_coe.mpr
  simp only [Game.coe_guessingAdvantage]
  apply (Asymptotics.superpolynomialDecay_iff_abs_isBoundedUnder _
    tendsto_natCast_atTop_atTop).mpr
  intro degree
  refine ⟨9, Filter.eventually_map.mpr ?_⟩
  filter_upwards [((negligible_iff_coe.mp (hinversion degree)) degree).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)] with n hsmall
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) (abs_nonneg _))]
  have h := mul_le_mul_of_nonneg_left
    (invertSigned_advantage_le (f n) (predictor n) (coins n)
      (precision degree n) (precision_pos degree n))
    (pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) degree)
  have hprecision : (n : ℝ) ^ degree * (1 / (precision degree n : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by exact_mod_cast precision_pos degree n)]
    simp only [precision, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    gcongr
    linarith
  simp only [Game.succProbability, ENNReal.toReal] at hsmall h ⊢
  nlinarith

end Cslib.Crypto.GoldreichLevin
