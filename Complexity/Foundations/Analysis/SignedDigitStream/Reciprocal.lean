/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.SignedDigitStream.Multiplication
public import Complexity.Foundations.Analysis.SpecialFunctions.PolynomialSwitch
public import Complexity.Foundations.Analysis.SpecialFunctions.RationalRamp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Early-word reciprocal and normalized smooth estimators on signed-digit streams

This module formalizes the reciprocal algorithm of [OpenAI2026LogSpace, Section 10.4, Lemma 10.5]
together with the normalized stream decompositions of `Cslib.polynomialTransition4`,
`Cslib.polynomialSwitch4`, `Cslib.rationalRamp4Unit`, and the clipped stochastic-atom reciprocal
`1 / (2 * max (1 / 2) (min 1 q))`.

## Main definitions

* `Cslib.SignedDigitStream.recipCutoff`: early-word truncation place `t / 2 + 7` at clock `t`.
* `Cslib.SignedDigitStream.recipPrefixRat`, `recipAlpha`, `recipBeta`: rational early prefix
  `x^{[t / 2 + 7]}` and normalized first-order Taylor coefficients for `1 / (64 * x)` on
  `x ∈ [1 / 4, 1]`.
* `Cslib.SignedDigitStream.recip64Approx`, `recip64Stream`: scaled integer approximations and
  exact signed-digit stream for `1 / (64 * streamVal x)` when `streamVal x ∈ [1 / 4, 1]`.
* `Cslib.SignedDigitStream.dyadicSwitch`, `dyadicWeight`: smooth dyadic partition of unity on
  `[1, 2 ^ (m + 1)]` built from `Cslib.polynomialSwitch4`, reducing `1 / (1 + max 0 t)` in
  `Cslib.rationalRamp4Unit` to a balanced sum of reciprocals evaluated solely on `[1 / 4, 1]`.

## Main results

* `Cslib.SignedDigitStream.recipCutoff_clock_payment`: for `j ≤ recipCutoff t`,
  `recipCutoff t + 1 ≤ 22 + 2 * (t - j)` (early-word suspended-record payment).
* `Cslib.SignedDigitStream.recip64Approx_isScaledApprox`, `streamVal_recip64Stream`:
  **Lemma 10.5** for normalized reciprocals on `[1 / 4, 1]`.
* `Cslib.SignedDigitStream.shiftClipVal_clippedAtomInv`: exact recovery of
  `1 / (2 * max (1 / 2) (min 1 q))` from `1 / (64 * max (1 / 4) (max (1 / 2) (min 1 q)))`.
* `Cslib.SignedDigitStream.polynomialTransition4_eq_shiftClip`: normalized `[-1, 1]` stream
  decomposition of `Cslib.polynomialTransition4`.
* `Cslib.SignedDigitStream.rationalRamp4Unit_eq_poly_add_inv` and `inv_eq_sum_dyadicWeight`:
  smooth dyadic partition-of-unity reduction of `Cslib.rationalRamp4Unit` to `[1 / 4, 1]`
  reciprocals and `Cslib.polynomialTransition4`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 10.4, Lemma 10.5 (23 September 2026).
-/

public section

namespace Cslib.SignedDigitStream

open Finset

section EarlyWordReciprocal

/-- Early-word truncation cutoff `k(t) = t / 2 + 7` for `1 / (64 * x)` on `[1 / 4, 1]`
[OpenAI2026LogSpace, Lemma 10.5]. -/
@[expose] def recipCutoff (t : ℕ) : ℕ :=
  t / 2 + 7

/-- **Early-word clock payment** [OpenAI2026LogSpace, (10.5)]: every query `j ≤ recipCutoff t`
during formation of the `(recipCutoff t + 1)`-place integer prefix is paid for by `2 * (t - j)`
with constant additive slack. -/
theorem recipCutoff_clock_payment {t j : ℕ} (hj : j ≤ recipCutoff t) :
    ((recipCutoff t + 1 : ℕ) : ℤ) ≤ 22 + 2 * ((t : ℤ) - (j : ℤ)) := by
  unfold recipCutoff at hj ⊢
  omega

/-- Also `t + 1` itself is bounded by `15 + 2 * (t - j)` on every early-word query
`j ≤ recipCutoff t` [OpenAI2026LogSpace, (10.5)]. -/
theorem clock_succ_le_early_payment {t j : ℕ} (hj : j ≤ recipCutoff t) :
    ((t + 1 : ℕ) : ℤ) ≤ 15 + 2 * ((t : ℤ) - (j : ℤ)) := by
  unfold recipCutoff at hj
  omega

/-- Rational early prefix `x^{[recipCutoff t]}` formed from digits `0 .. recipCutoff t`. -/
@[expose] def recipPrefixRat (x : ℕ → ℤ) (t : ℕ) : ℚ :=
  (intPrefix x (recipCutoff t) : ℚ) / (2 : ℚ) ^ recipCutoff t

/-- Normalized constant Taylor coefficient `α = 1 / (64 * x^0)` for `1 / (64 * x)`. -/
@[expose] def recipAlpha (x : ℕ → ℤ) (t : ℕ) : ℚ :=
  1 / (64 * recipPrefixRat x t)

/-- Normalized linear Taylor coefficient `β = -1 / (64 * (x^0) ^ 2)` for `1 / (64 * x)`. -/
@[expose] def recipBeta (x : ℕ → ℤ) (t : ℕ) : ℚ :=
  -1 / (64 * (recipPrefixRat x t) ^ 2)

/-- Product stream representing `recipBeta x t * (streamVal x - streamPrefix x (recipCutoff t))`. -/
@[expose] def recipProdStream (x : ℕ → ℤ) (t : ℕ) : ℕ → ℤ :=
  diffDigit (mulApprox (ratStream (recipBeta x t)) (suffixStream x (recipCutoff t)))

/-- Half-sum stream representing `(recipAlpha x t + recipBeta x t * e) / 2`. -/
@[expose] def recipHalfStream (x : ℕ → ℤ) (t : ℕ) : ℕ → ℤ :=
  diffDigit (pairAvgApprox (ratStream (recipAlpha x t)) (recipProdStream x t))

/-- Scaled integer approximation to `1 / (64 * streamVal x)` at clock `t`
[OpenAI2026LogSpace, (10.4)]. -/
@[expose] def recip64Approx (x : ℕ → ℤ) (t : ℕ) : ℤ :=
  shiftClipApprox 1 (recipHalfStream x t) (t + 3) / 8

/-- Exact signed-digit stream representing `1 / (64 * streamVal x)` for
`streamVal x ∈ [1 / 4, 1]`. -/
@[expose] def recip64Stream (x : ℕ → ℤ) : ℕ → ℤ :=
  diffDigit (recip64Approx x)

theorem recipPrefixRat_cast (x : ℕ → ℤ) (t : ℕ) :
    (recipPrefixRat x t : ℝ) = streamPrefix x (recipCutoff t) := by
  unfold recipPrefixRat
  rw [streamPrefix_eq_intPrefix_div]
  push_cast
  rfl

theorem abs_tail_recipCutoff_le {x : ℕ → ℤ} (hx : IsSignedStream x) (t : ℕ) :
    |streamVal x - (recipPrefixRat x t : ℝ)| ≤ 3 / 64 := by
  rw [recipPrefixRat_cast]
  have herr := abs_streamVal_sub_streamPrefix_le hx (recipCutoff t)
  have hpow : (128 : ℝ) ≤ (2 : ℝ) ^ recipCutoff t := by
    unfold recipCutoff
    calc (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (t / 2 + 7) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv : (6 : ℝ) / (2 : ℝ) ^ recipCutoff t ≤ 6 / 128 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow
  linarith

theorem recipPrefixRat_mem_Icc {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    (recipPrefixRat x t : ℝ) ∈ Set.Icc (3 / 16 : ℝ) (17 / 16) := by
  have herr := abs_tail_recipCutoff_le hx t
  obtain ⟨hlo, hhi⟩ := hx_mem
  obtain ⟨he1, he2⟩ := abs_sub_le_iff.mp herr
  exact ⟨by linarith, by linarith⟩

theorem abs_recipAlpha_le_one {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    |recipAlpha x t| ≤ 1 := by
  have hmem := recipPrefixRat_mem_Icc hx hx_mem t
  have hreal : |(recipAlpha x t : ℝ)| ≤ 1 := by
    unfold recipAlpha
    push_cast
    have hx0_pos : (0 : ℝ) < (recipPrefixRat x t : ℝ) := by linarith [hmem.1]
    rw [abs_of_pos (by positivity)]
    have hden : (12 : ℝ) ≤ 64 * (recipPrefixRat x t : ℝ) := by linarith [hmem.1]
    calc (1 : ℝ) / (64 * (recipPrefixRat x t : ℝ))
        ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) hden
      _ ≤ 1 := by norm_num
  exact_mod_cast hreal

theorem abs_recipBeta_le_one {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    |recipBeta x t| ≤ 1 := by
  have hmem := recipPrefixRat_mem_Icc hx hx_mem t
  have hreal : |(recipBeta x t : ℝ)| ≤ 1 := by
    unfold recipBeta
    push_cast
    have hx0_pos : (0 : ℝ) < (recipPrefixRat x t : ℝ) := by linarith [hmem.1]
    have hsq : (3 / 16 : ℝ) ^ 2 ≤ (recipPrefixRat x t : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hmem.1 2
    have hden : (9 / 4 : ℝ) ≤ 64 * (recipPrefixRat x t : ℝ) ^ 2 := by linarith
    have hneg_div : (-1 : ℝ) / (64 * (recipPrefixRat x t : ℝ) ^ 2) =
        -(1 / (64 * (recipPrefixRat x t : ℝ) ^ 2)) := neg_div _ _
    rw [hneg_div, abs_neg, abs_of_pos (by positivity)]
    calc (1 : ℝ) / (64 * (recipPrefixRat x t : ℝ) ^ 2)
        ≤ 1 / (9 / 4) := one_div_le_one_div_of_le (by norm_num) hden
      _ ≤ 1 := by norm_num
  exact_mod_cast hreal

private theorem abs_recipProdVal_le {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    |(recipBeta x t : ℝ) * streamVal (suffixStream x (recipCutoff t))| ≤ 3 / 64 := by
  have hβ : |(recipBeta x t : ℝ)| ≤ 1 := by exact_mod_cast abs_recipBeta_le_one hx hx_mem t
  have he : |streamVal (suffixStream x (recipCutoff t))| ≤ 3 / 64 := by
    rw [streamVal_suffixStream hx, ← recipPrefixRat_cast]
    exact abs_tail_recipCutoff_le hx t
  rw [abs_mul]
  calc |(recipBeta x t : ℝ)| * |streamVal (suffixStream x (recipCutoff t))|
      ≤ 1 * (3 / 64) := mul_le_mul hβ he (abs_nonneg _) (by norm_num)
    _ = 3 / 64 := one_mul _

theorem recipProdStream_isSignedStream {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    IsSignedStream (recipProdStream x t) := by
  unfold recipProdStream
  have hβ := ratStream_isSignedStream (abs_recipBeta_le_one hx hx_mem t)
  have hsuff := suffixStream_isSignedStream hx (recipCutoff t)
  have hm := mulApprox_isScaledApprox hβ hsuff
  rw [streamVal_ratStream (abs_recipBeta_le_one hx hx_mem t)] at hm
  have hbound : |(recipBeta x t : ℝ) * streamVal (suffixStream x (recipCutoff t))| ≤ 1 :=
    (abs_recipProdVal_le hx hx_mem t).trans (by norm_num)
  exact diffDigit_isSignedStream hbound hm

theorem streamVal_recipProdStream {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    streamVal (recipProdStream x t) =
      (recipBeta x t : ℝ) * (streamVal x - (recipPrefixRat x t : ℝ)) := by
  unfold recipProdStream
  have hβ := ratStream_isSignedStream (abs_recipBeta_le_one hx hx_mem t)
  have hsuff := suffixStream_isSignedStream hx (recipCutoff t)
  have hm := mulApprox_isScaledApprox hβ hsuff
  rw [streamVal_ratStream (abs_recipBeta_le_one hx hx_mem t)] at hm
  have hbound : |(recipBeta x t : ℝ) * streamVal (suffixStream x (recipCutoff t))| ≤ 1 :=
    (abs_recipProdVal_le hx hx_mem t).trans (by norm_num)
  rw [streamVal_diffDigit hbound hm, streamVal_suffixStream hx, ← recipPrefixRat_cast]

theorem recipHalfStream_isSignedStream {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    IsSignedStream (recipHalfStream x t) := by
  unfold recipHalfStream
  have hα := ratStream_isSignedStream (abs_recipAlpha_le_one hx hx_mem t)
  have hp := recipProdStream_isSignedStream hx hx_mem t
  have havg := pairAvgApprox_isScaledApprox hα hp
  rw [streamVal_ratStream (abs_recipAlpha_le_one hx hx_mem t)] at havg
  have hα_le : |(recipAlpha x t : ℝ)| ≤ 1 := by exact_mod_cast abs_recipAlpha_le_one hx hx_mem t
  have hp_le : |streamVal (recipProdStream x t)| ≤ 3 / 64 := by
    rw [streamVal_recipProdStream hx hx_mem t, recipPrefixRat_cast, ← streamVal_suffixStream hx]
    exact abs_recipProdVal_le hx hx_mem t
  have hbound : |((recipAlpha x t : ℝ) + streamVal (recipProdStream x t)) / 2| ≤ 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htri := abs_add_le (recipAlpha x t : ℝ) (streamVal (recipProdStream x t))
    linarith
  exact diffDigit_isSignedStream hbound havg

theorem streamVal_recipHalfStream {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    streamVal (recipHalfStream x t) =
      ((recipAlpha x t : ℝ) +
        (recipBeta x t : ℝ) * (streamVal x - (recipPrefixRat x t : ℝ))) / 2 := by
  unfold recipHalfStream
  have hα := ratStream_isSignedStream (abs_recipAlpha_le_one hx hx_mem t)
  have hp := recipProdStream_isSignedStream hx hx_mem t
  have havg := pairAvgApprox_isScaledApprox hα hp
  rw [streamVal_ratStream (abs_recipAlpha_le_one hx hx_mem t)] at havg
  have hα_le : |(recipAlpha x t : ℝ)| ≤ 1 := by exact_mod_cast abs_recipAlpha_le_one hx hx_mem t
  have hp_le : |streamVal (recipProdStream x t)| ≤ 3 / 64 := by
    rw [streamVal_recipProdStream hx hx_mem t, recipPrefixRat_cast, ← streamVal_suffixStream hx]
    exact abs_recipProdVal_le hx hx_mem t
  have hbound : |((recipAlpha x t : ℝ) + streamVal (recipProdStream x t)) / 2| ≤ 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htri := abs_add_le (recipAlpha x t : ℝ) (streamVal (recipProdStream x t))
    linarith
  rw [streamVal_diffDigit hbound havg, streamVal_recipProdStream hx hx_mem t]

private theorem abs_recipTaylor_remainder_le {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (t : ℕ) :
    (2 : ℝ) ^ t * |((recipAlpha x t : ℝ) +
        (recipBeta x t : ℝ) * (streamVal x - (recipPrefixRat x t : ℝ))) -
        1 / (64 * streamVal x)| ≤ 1 / 128 := by
  set x₀ : ℝ := (recipPrefixRat x t : ℝ)
  set xVal : ℝ := streamVal x
  set e : ℝ := xVal - x₀
  have hx₀_mem := recipPrefixRat_mem_Icc hx hx_mem t
  have hx₀_pos : 0 < x₀ := by linarith [hx₀_mem.1]
  have hxVal_pos : 0 < xVal := by linarith [hx_mem.1]
  have hα_eq : (recipAlpha x t : ℝ) = 1 / (64 * x₀) := by
    unfold recipAlpha
    push_cast
    rfl
  have hβ_eq : (recipBeta x t : ℝ) = -1 / (64 * x₀ ^ 2) := by
    unfold recipBeta
    push_cast
    rfl
  have halg : (1 / (64 * x₀) + (-1 / (64 * x₀ ^ 2)) * e) - 1 / (64 * xVal) =
      -(e ^ 2 / (64 * x₀ ^ 2 * xVal)) := by
    dsimp [e]
    field_simp
    ring
  rw [hα_eq, hβ_eq, halg, abs_neg, abs_div, abs_of_nonneg (sq_nonneg e),
    abs_of_pos (by positivity : 0 < 64 * x₀ ^ 2 * xVal)]
  have he_abs : |e| ≤ 6 / (2 : ℝ) ^ recipCutoff t := by
    dsimp [e, xVal, x₀]
    rw [recipPrefixRat_cast]
    exact abs_streamVal_sub_streamPrefix_le hx (recipCutoff t)
  have he_sq : e ^ 2 ≤ 36 / (2 : ℝ) ^ (2 * recipCutoff t) := by
    calc e ^ 2 = |e| ^ 2 := (sq_abs e).symm
      _ ≤ (6 / (2 : ℝ) ^ recipCutoff t) ^ 2 := pow_le_pow_left₀ (abs_nonneg e) he_abs 2
      _ = 36 / ((2 : ℝ) ^ recipCutoff t) ^ 2 := by ring
      _ = 36 / (2 : ℝ) ^ (2 * recipCutoff t) := by
          rw [← pow_mul, mul_comm]
  have hexp : t + 13 ≤ 2 * recipCutoff t := by
    unfold recipCutoff
    omega
  have hpow_le : (2 : ℝ) ^ (t + 13) ≤ (2 : ℝ) ^ (2 * recipCutoff t) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hnum : (2 : ℝ) ^ t * e ^ 2 ≤ 36 / (2 : ℝ) ^ (13 : ℕ) := by
    calc (2 : ℝ) ^ t * e ^ 2
        ≤ (2 : ℝ) ^ t * (36 / (2 : ℝ) ^ (2 * recipCutoff t)) :=
          mul_le_mul_of_nonneg_left he_sq (by positivity)
      _ ≤ (2 : ℝ) ^ t * (36 / (2 : ℝ) ^ (t + 13)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow_le) (by positivity)
      _ = 36 / (2 : ℝ) ^ (13 : ℕ) := by
          rw [pow_add]
          field_simp
  have hden : (9 / 16 : ℝ) ≤ 64 * x₀ ^ 2 * xVal := by
    have hx₀_sq : (3 / 16 : ℝ) ^ 2 ≤ x₀ ^ 2 := pow_le_pow_left₀ (by norm_num) hx₀_mem.1 2
    have h64 : (9 / 4 : ℝ) ≤ 64 * x₀ ^ 2 := by linarith
    calc (9 / 16 : ℝ) = (9 / 4) * (1 / 4) := by norm_num
      _ ≤ (64 * x₀ ^ 2) * xVal :=
          mul_le_mul h64 hx_mem.1 (by norm_num) (by positivity)
  rw [mul_div_assoc']
  calc ((2 : ℝ) ^ t * e ^ 2) / (64 * x₀ ^ 2 * xVal)
      ≤ (36 / (2 : ℝ) ^ (13 : ℕ)) / (9 / 16) :=
        div_le_div₀ (by norm_num) hnum (by norm_num) hden
    _ = 1 / 128 := by norm_num

/-- **Lemma 10.5 (early-word scaled reciprocal)** [OpenAI2026LogSpace, Lemma 10.5]: for any
signed-digit stream `x` with `streamVal x ∈ [1 / 4, 1]`, `recip64Approx x` approximates
`1 / (64 * streamVal x)` within scaled error `< 2`. -/
theorem recip64Approx_isScaledApprox {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) :
    IsScaledApprox (1 / (64 * streamVal x)) (recip64Approx x) := by
  intro t
  unfold recip64Approx
  set A := shiftClipApprox 1 (recipHalfStream x t) (t + 3)
  set T : ℝ := (recipAlpha x t : ℝ) +
    (recipBeta x t : ℝ) * (streamVal x - (recipPrefixRat x t : ℝ))
  have hhalf := recipHalfStream_isSignedStream hx hx_mem t
  have hsc := shiftClipApprox_isScaledApprox 1 hhalf (t + 3)
  have hT_bound : |T| ≤ 1 := by
    have hα_le : |(recipAlpha x t : ℝ)| ≤ 1 / 12 := by
      have hmem := recipPrefixRat_mem_Icc hx hx_mem t
      unfold recipAlpha
      push_cast
      have hx0_pos : (0 : ℝ) < (recipPrefixRat x t : ℝ) := by linarith [hmem.1]
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [hmem.1])
    have hp_le : |(recipBeta x t : ℝ) * (streamVal x - (recipPrefixRat x t : ℝ))| ≤ 3 / 64 := by
      rw [recipPrefixRat_cast, ← streamVal_suffixStream hx]
      exact abs_recipProdVal_le hx hx_mem t
    have htri := abs_add_le (recipAlpha x t : ℝ)
      ((recipBeta x t : ℝ) * (streamVal x - (recipPrefixRat x t : ℝ)))
    linarith
  have hclip_eq : shiftClipVal 1 (streamVal (recipHalfStream x t)) = T := by
    rw [streamVal_recipHalfStream hx hx_mem t]
    unfold shiftClipVal
    have h2 : (2 : ℝ) ^ (1 : ℤ) * (T / 2) = T := by norm_num; ring
    rw [h2, min_eq_right (le_of_abs_le hT_bound), max_eq_right (neg_le_of_abs_le hT_bound)]
  rw [hclip_eq] at hsc
  have hfl := abs_ediv_sub_div_lt_one A (by decide : (0 : ℤ) < 8)
  push_cast at hfl
  have hA_err : |(A : ℝ) / 8 - (2 : ℝ) ^ t * T| < 1 / 4 := by
    have hpow : (2 : ℝ) ^ (t + 3) = 8 * (2 : ℝ) ^ t := by ring
    rw [hpow] at hsc
    have hsub : (A : ℝ) / 8 - (2 : ℝ) ^ t * T = ((A : ℝ) - 8 * (2 : ℝ) ^ t * T) / 8 := by ring
    rw [hsub, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    linarith
  have hrem := abs_recipTaylor_remainder_le hx hx_mem t
  have htri1 := abs_sub_le ((A / 8 : ℤ) : ℝ) ((A : ℝ) / 8) ((2 : ℝ) ^ t * T)
  have htri2 := abs_sub_le ((A / 8 : ℤ) : ℝ) ((2 : ℝ) ^ t * T)
    ((2 : ℝ) ^ t * (1 / (64 * streamVal x)))
  have hrem' : |(2 : ℝ) ^ t * T - (2 : ℝ) ^ t * (1 / (64 * streamVal x))| ≤ 1 / 128 := by
    simpa only [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ t)] using hrem
  linarith

theorem recip64Stream_isSignedStream {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) :
    IsSignedStream (recip64Stream x) := by
  have hz : |1 / (64 * streamVal x)| ≤ 1 := by
    have hx_pos : 0 < streamVal x := by linarith [hx_mem.1]
    rw [abs_of_pos (by positivity)]
    have hden : (16 : ℝ) ≤ 64 * streamVal x := by linarith [hx_mem.1]
    exact (one_div_le_one_div_of_le (by norm_num) hden).trans (by norm_num)
  exact diffDigit_isSignedStream hz (recip64Approx_isScaledApprox hx hx_mem)

theorem streamVal_recip64Stream {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) :
    streamVal (recip64Stream x) = 1 / (64 * streamVal x) := by
  have hz : |1 / (64 * streamVal x)| ≤ 1 := by
    have hx_pos : 0 < streamVal x := by linarith [hx_mem.1]
    rw [abs_of_pos (by positivity)]
    have hden : (16 : ℝ) ≤ 64 * streamVal x := by linarith [hx_mem.1]
    exact (one_div_le_one_div_of_le (by norm_num) hden).trans (by norm_num)
  exact streamVal_diffDigit hz (recip64Approx_isScaledApprox hx hx_mem)

theorem recip64Approx_emod_eq (x : ℕ → ℤ) (t q : ℕ) :
    recip64Approx x t % (2 : ℤ) ^ q =
      (shiftClipApprox 1 (recipHalfStream x t) (t + 3) % (2 : ℤ) ^ (q + 3)) / 8 := by
  unfold recip64Approx
  simpa only [show (8 : ℤ) = (2 : ℤ) ^ (3 : ℕ) by decide] using
    ediv_two_pow_emod_eq (shiftClipApprox 1 (recipHalfStream x t) (t + 3)) q 3

end EarlyWordReciprocal

section SmoothEstimatorIdentities

/-- Clamping `q` to `[1 / 2, 1]` always lands inside `[1 / 4, 1]`, and `shiftClipVal 5` recovers
the exact clipped stochastic-atom inverse `1 / (2 * max (1 / 2) (min 1 q))` from `1 / (64 * c)`. -/
theorem clippedAtomDenom_mem_Icc (q : ℝ) :
    max (1 / 2 : ℝ) (min 1 q) ∈ Set.Icc (1 / 4 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · exact (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans (le_max_left _ _)
  · exact max_le (by norm_num) (min_le_left _ _)

theorem shiftClipVal_clippedAtomInv (q : ℝ) :
    shiftClipVal 5 (1 / (64 * max (1 / 2 : ℝ) (min 1 q))) =
      1 / (2 * max (1 / 2 : ℝ) (min 1 q)) := by
  set c := max (1 / 2 : ℝ) (min 1 q)
  have hc_lo : (1 / 2 : ℝ) ≤ c := le_max_left _ _
  have hc_hi : c ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hc_pos : 0 < c := by linarith
  unfold shiftClipVal
  have hmul : (2 : ℝ) ^ (5 : ℤ) * (1 / (64 * c)) = 1 / (2 * c) := by
    norm_num
    field_simp
    ring
  have hle1 : 1 / (2 * c) ≤ 1 := by
    have h2c : 1 ≤ 2 * c := by linarith
    exact (div_le_one (by positivity)).mpr h2c
  have hge_neg1 : -1 ≤ 1 / (2 * c) := by
    have hpos : 0 ≤ 1 / (2 * c) := by positivity
    linarith
  rw [hmul, min_eq_right hle1, max_eq_right hge_neg1]

/-- Normalized `[-1, 1]` stream decomposition of `Cslib.polynomialTransition4` via `pairAvg`
and `shiftClipVal 7`. -/
theorem polynomialTransition4_eq_shiftClip (t : ℝ) :
    Cslib.polynomialTransition4 t =
      shiftClipVal 7
        ((max 0 (min 1 t)) ^ 4 *
          (((1 / 32 + (1 / 8) * (1 - max 0 (min 1 t))) / 2 +
            ((5 / 16) * (1 - max 0 (min 1 t)) ^ 2 +
              (5 / 8) * (1 - max 0 (min 1 t)) ^ 3) / 2) / 2)) := by
  set u := max (0 : ℝ) (min 1 t)
  have hpoly : u ^ 4 *
      (((1 / 32 + (1 / 8) * (1 - u)) / 2 +
        ((5 / 16) * (1 - u) ^ 2 + (5 / 8) * (1 - u) ^ 3) / 2) / 2) =
      Cslib.polynomialTransition4 t / 128 := by
    unfold Cslib.polynomialTransition4 Cslib.transitionPolynomial4
    dsimp [u]
    ring
  rw [hpoly]
  unfold shiftClipVal
  have hscale : (2 : ℝ) ^ (7 : ℤ) * (Cslib.polynomialTransition4 t / 128) =
      Cslib.polynomialTransition4 t := by
    norm_num
    ring
  have h0 : 0 ≤ Cslib.polynomialTransition4 t := Cslib.polynomialTransition4_nonneg t
  have h1 : Cslib.polynomialTransition4 t ≤ 1 := Cslib.polynomialTransition4_le_one t
  rw [hscale, min_eq_right h1, max_eq_right (by linarith)]

/-- Exact polynomial-plus-reciprocal decomposition of `Cslib.rationalRamp4Unit`. -/
theorem rationalRamp4Unit_eq_poly_add_inv (t : ℝ) :
    Cslib.rationalRamp4Unit t =
      max 0 t - 3 + 6 * (1 / (1 + max 0 t)) - 4 * (1 / (1 + max 0 t)) ^ 2 +
        (1 / (1 + max 0 t)) ^ 3 := by
  unfold Cslib.rationalRamp4Unit
  set u := max (0 : ℝ) t
  have hpos : 0 < 1 + u := by
    have hu : 0 ≤ u := le_max_left _ _
    linarith
  field_simp
  ring

/-- Smooth dyadic transition `polynomialSwitch4 (2 ^ r) (2 ^ (r + 1)) w`. -/
@[expose] noncomputable def dyadicSwitch (r : ℕ) (w : ℝ) : ℝ :=
  Cslib.polynomialSwitch4 ((2 : ℝ) ^ r) ((2 : ℝ) ^ (r + 1)) w

/-- Smooth dyadic partition-of-unity weight `ω_{m, r}(w)` across scales `0 ≤ r ≤ m`. -/
@[expose] noncomputable def dyadicWeight (m r : ℕ) (w : ℝ) : ℝ :=
  if m = 0 then
    if r = 0 then 1 else 0
  else if r = 0 then
    1 - dyadicSwitch 0 w
  else if r < m then
    dyadicSwitch (r - 1) w - dyadicSwitch r w
  else if r = m then
    dyadicSwitch (m - 1) w
  else
    0

/-- Division-free normalized evaluation of `dyadicSwitch r w` from `wNorm = w / 2 ^ (m + 1)`
whenever `0 ≤ w` and `r ≤ m`. -/
theorem dyadicSwitch_eq_of_norm {m r : ℕ} {w : ℝ} (hr : r ≤ m) (hw0 : 0 ≤ w) :
    dyadicSwitch r w =
      Cslib.polynomialTransition4
        (shiftClipVal 2
          ((shiftClipVal ((m : ℤ) - (r : ℤ)) (w / (2 : ℝ) ^ (m + 1)) + (-1 / 2)) / 2)) := by
  unfold dyadicSwitch Cslib.polynomialSwitch4
  have hscale : (2 : ℝ) ^ ((m : ℤ) - (r : ℤ)) * (w / (2 : ℝ) ^ (m + 1)) =
      w / (2 : ℝ) ^ (r + 1) := by
    have hm1 : (m + 1 : ℕ) = (m - r) + (r + 1) := by omega
    have hsub : ((m : ℤ) - (r : ℤ)) = ((m - r : ℕ) : ℤ) := by omega
    rw [hsub, zpow_natCast, hm1, pow_add]
    field_simp
  set q := w / (2 : ℝ) ^ (r + 1)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hy : shiftClipVal ((m : ℤ) - (r : ℤ)) (w / (2 : ℝ) ^ (m + 1)) = min 1 q := by
    unfold shiftClipVal
    rw [hscale, max_eq_right]
    exact le_min (by norm_num) (by linarith)
  rw [hy]
  have hmin_mem : min 1 q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_min zero_le_one hq0, min_le_left _ _⟩
  have hs2 : shiftClipVal 2 ((min 1 q + (-1 / 2)) / 2) = 2 * min 1 q - 1 := by
    unfold shiftClipVal
    have h4 : (2 : ℝ) ^ (2 : ℤ) * ((min 1 q + (-1 / 2)) / 2) = 2 * min 1 q - 1 := by
      norm_num
      ring
    rw [h4, min_eq_right (by linarith [hmin_mem.2]), max_eq_right (by linarith [hmin_mem.1])]
  rw [hs2]
  have harg_eq : (w - (2 : ℝ) ^ r) / ((2 : ℝ) ^ (r + 1) - (2 : ℝ) ^ r) = 2 * q - 1 := by
    dsimp [q]
    have hp : (2 : ℝ) ^ (r + 1) = 2 * (2 : ℝ) ^ r := by ring
    rw [hp]
    field_simp
    ring
  rw [harg_eq]
  unfold Cslib.polynomialTransition4
  congr 1
  by_cases hq1 : 1 ≤ q
  · rw [min_eq_left hq1, show (2 : ℝ) * 1 - 1 = 1 by norm_num, min_self,
      min_eq_left (by linarith : (1 : ℝ) ≤ 2 * q - 1)]
  · have hq_lt : q ≤ 1 := (not_le.mp hq1).le
    rw [min_eq_right hq_lt]

theorem sum_dyadicWeight (m : ℕ) (w : ℝ) :
    ∑ r ∈ range (m + 1), dyadicWeight m r w = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [dyadicWeight]
  · have hm_ne : m ≠ 0 := hm.ne'
    have hsplit : ∑ r ∈ range (m + 1), dyadicWeight m r w =
        (∑ r ∈ range m, dyadicWeight m r w) + dyadicWeight m m w :=
      sum_range_succ _ m
    have hlast : dyadicWeight m m w = dyadicSwitch (m - 1) w := by
      unfold dyadicWeight
      simp [hm_ne]
    have htel : ∀ k : ℕ, 1 ≤ k → k ≤ m →
        ∑ r ∈ range k, dyadicWeight m r w = 1 - dyadicSwitch (k - 1) w := by
      intro k hk1 hkm
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hk_pos
        · simp [dyadicWeight, hm_ne]
        · rw [sum_range_succ, ih hk_pos (by omega)]
          have hk_lt : k < m := by omega
          have hk_ne : k ≠ 0 := hk_pos.ne'
          have hwk : dyadicWeight m k w = dyadicSwitch (k - 1) w - dyadicSwitch k w := by
            unfold dyadicWeight
            simp [hm_ne, hk_ne, hk_lt]
          rw [hwk, Nat.add_sub_cancel]
          ring
    rw [hsplit, htel m hm le_rfl, hlast]
    ring

theorem dyadicWeight_mem_Icc (m r : ℕ) (w : ℝ) :
    dyadicWeight m r w ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsw_lo : ∀ k, 0 ≤ dyadicSwitch k w := fun k =>
    Cslib.polynomialTransition4_nonneg _
  have hsw_hi : ∀ k, dyadicSwitch k w ≤ 1 := fun k =>
    Cslib.polynomialTransition4_le_one _
  unfold dyadicWeight
  split_ifs
  · exact ⟨by norm_num, by norm_num⟩
  · exact ⟨by norm_num, by norm_num⟩
  · exact ⟨by linarith [hsw_hi 0], by linarith [hsw_lo 0]⟩
  · exact ⟨by linarith [hsw_lo (r - 1), hsw_hi r], by linarith [hsw_hi (r - 1), hsw_lo r]⟩
  · exact ⟨by linarith [hsw_lo (m - 1)], hsw_hi (m - 1)⟩
  · exact ⟨by norm_num, by norm_num⟩

private theorem dyadicSwitch_eq_zero_of_le {k : ℕ} {w : ℝ} (hw : w ≤ (2 : ℝ) ^ k) :
    dyadicSwitch k w = 0 := by
  unfold dyadicSwitch Cslib.polynomialSwitch4
  apply Cslib.polynomialTransition4_of_nonpos
  have hden : 0 < (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ k := by
    have hp : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
    have hk : 0 < (2 : ℝ) ^ k := by positivity
    linarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

private theorem dyadicSwitch_eq_one_of_ge {k : ℕ} {w : ℝ} (hw : (2 : ℝ) ^ (k + 1) ≤ w) :
    dyadicSwitch k w = 1 := by
  unfold dyadicSwitch Cslib.polynomialSwitch4
  apply Cslib.polynomialTransition4_of_one_le
  have hden : 0 < (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ k := by
    have hp : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
    have hk : 0 < (2 : ℝ) ^ k := by positivity
    linarith
  exact (one_le_div hden).mpr (by linarith)

/-- Whenever `dyadicWeight m r w ≠ 0` on `w ∈ [1, 2 ^ (m + 1)]`, the scaled argument
`w / 2 ^ (r + 1)` automatically lies in `[1 / 4, 1]`. -/
theorem scaled_mem_Icc_of_dyadicWeight_ne_zero {m r : ℕ} {w : ℝ}
    (hw : w ∈ Set.Icc (1 : ℝ) ((2 : ℝ) ^ (m + 1))) (hne : dyadicWeight m r w ≠ 0) :
    w / (2 : ℝ) ^ (r + 1) ∈ Set.Icc (1 / 4 : ℝ) 1 := by
  obtain ⟨hw_lo, hw_hi⟩ := hw
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · unfold dyadicWeight at hne
    by_cases hr0 : r = 0
    · subst hr0
      norm_num at hw_hi ⊢
      exact ⟨by linarith, by linarith⟩
    · simp [hr0] at hne
  · have hm_ne : m ≠ 0 := hm.ne'
    by_cases hr0 : r = 0
    · subst hr0
      have hlt2 : w < 2 := by
        by_contra hge
        rw [not_lt] at hge
        have h1 := dyadicSwitch_eq_one_of_ge (k := 0) (w := w) (by norm_num; linarith)
        unfold dyadicWeight at hne
        simp [hm_ne, h1] at hne
      norm_num
      exact ⟨by linarith, by linarith⟩
    · by_cases hrm : r < m
      · have hgt_lo : (2 : ℝ) ^ (r - 1) < w := by
          by_contra hle
          rw [not_lt] at hle
          have hs1 := dyadicSwitch_eq_zero_of_le hle
          have hle2 : w ≤ (2 : ℝ) ^ r := hle.trans (pow_le_pow_right₀ (by norm_num) (by omega))
          have hs2 := dyadicSwitch_eq_zero_of_le hle2
          unfold dyadicWeight at hne
          simp [hm_ne, hr0, hrm, hs1, hs2] at hne
        have hlt_hi : w < (2 : ℝ) ^ (r + 1) := by
          by_contra hge
          rw [not_lt] at hge
          have hge1 : (2 : ℝ) ^ ((r - 1) + 1) ≤ w := by
            have hr_eq : (r - 1) + 1 = r := by omega
            rw [hr_eq]
            exact (pow_le_pow_right₀ (by norm_num) (Nat.le_succ r)).trans hge
          have hs1 := dyadicSwitch_eq_one_of_ge hge1
          have hs2 := dyadicSwitch_eq_one_of_ge hge
          unfold dyadicWeight at hne
          simp [hm_ne, hr0, hrm, hs1, hs2] at hne
        have hr_pow : (2 : ℝ) ^ (r + 1) = 4 * (2 : ℝ) ^ (r - 1) := by
          have hr_eq : r + 1 = 2 + (r - 1) := by omega
          rw [hr_eq, pow_add]
          norm_num
        refine ⟨?_, ?_⟩
        · rw [le_div_iff₀ (by positivity), hr_pow]
          linarith
        · exact (div_le_one (by positivity)).mpr hlt_hi.le
      · by_cases hreq : r = m
        · subst hreq
          have hgt_lo : (2 : ℝ) ^ (r - 1) < w := by
            by_contra hle
            rw [not_lt] at hle
            have hs1 := dyadicSwitch_eq_zero_of_le hle
            unfold dyadicWeight at hne
            simp [hm_ne, hs1] at hne
          have hr_pow : (2 : ℝ) ^ (r + 1) = 4 * (2 : ℝ) ^ (r - 1) := by
            have hr_eq : r + 1 = 2 + (r - 1) := by omega
            rw [hr_eq, pow_add]
            norm_num
          refine ⟨?_, ?_⟩
          · rw [le_div_iff₀ (by positivity), hr_pow]
            linarith
          · exact (div_le_one (by positivity)).mpr hw_hi
        · unfold dyadicWeight at hne
          simp [hm_ne, hr0, hrm, hreq] at hne

/-- **Smooth dyadic partition-of-unity reciprocal formula**: for every `w ∈ [1, 2 ^ (m + 1)]`,
`1 / w` equals a weighted sum of `m + 1` reciprocals whose arguments are all clamped to the
fixed interval `[1 / 4, 1]`. -/
theorem inv_eq_sum_dyadicWeight {m : ℕ} {w : ℝ}
    (hw : w ∈ Set.Icc (1 : ℝ) ((2 : ℝ) ^ (m + 1))) :
    1 / w =
      ∑ r ∈ range (m + 1),
        dyadicWeight m r w *
          ((1 / (2 : ℝ) ^ (r + 1)) *
            (1 / max (1 / 4 : ℝ) (min 1 (w / (2 : ℝ) ^ (r + 1))))) := by
  have hw_pos : 0 < w := by linarith [hw.1]
  have hterm : ∀ r ∈ range (m + 1),
      dyadicWeight m r w *
        ((1 / (2 : ℝ) ^ (r + 1)) *
          (1 / max (1 / 4 : ℝ) (min 1 (w / (2 : ℝ) ^ (r + 1))))) =
        dyadicWeight m r w * (1 / w) := by
    intro r _
    by_cases hne : dyadicWeight m r w = 0
    · simp [hne]
    · obtain ⟨hlo, hhi⟩ := scaled_mem_Icc_of_dyadicWeight_ne_zero hw hne
      rw [min_eq_right hhi, max_eq_right hlo]
      congr 1
      field_simp
  rw [sum_congr rfl hterm, ← sum_mul, sum_dyadicWeight, one_mul]

end SmoothEstimatorIdentities

end Cslib.SignedDigitStream
