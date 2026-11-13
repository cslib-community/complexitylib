/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.WordReduction
import CslibFrontier.Languages.Probabilistic.Notation
public import CslibFrontier.Crypto.Computational.OneWay.Normalize
import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# The pseudoentropy prediction gap from one-wayness

The executable hashed parity reduction has polynomial loss. One-wayness therefore makes its
inversion term negligible, leaving an inverse-polynomial gap between feasible prediction and
the entropy threshold. Each predictor supplies one inverter with a fixed precision degree. The
argument is stated relative to a fixed advice family: a predictor reading advice gives an inverter
reading the same advice, and the advice length costs only a polynomial change of coin budget. The
uniform theorems are the empty-advice case.

## Main results

* `Cslib.Crypto.Pseudoentropy.HashPair.eventually_prediction_entropy_le_withAdvice`,
  `Cslib.Crypto.Pseudoentropy.HashPair.pair_hasGapWithAdvice`: the prediction gap relative to a
  fixed advice family.
* `Cslib.Crypto.OneWay.exists_pseudoentropyPair`,
  `Cslib.Crypto.NonuniformOneWay.exists_pseudoentropyPair`: every uniform (nonuniform) OWF gives
  an exactly samplable pair with an inverse-linear prediction gap against uniform predictors
  (predictors with polynomially bounded advice), including variable-length original images.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Definition 4 and Section 4, Lemmas 3 and 4.
  We use the public matrix and dyadic-range variant proved in `HashReduction`. This module
  discharges the inversion hypothesis using hardness of inversion with fixed advice.

Adapted from Crypto/Computational/Pseudoentropy/OneWay.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed saved seeds and nonnegative security games.
-/

public section

namespace Cslib.Crypto.Pseudoentropy.HashPair

open Probability BitString GoldreichLevin Filter Turing.MultiTapeTM
open scoped NNReal

/-- A single cubic precision suffices for all sufficiently large dimensions. -/
theorem precision_three_ge {n : ℕ} (hn : 8 ≤ n) :
    8 * hashCount n ≤ precision 3 n := by
  have hcount := hashCount_le n
  have hsquare : 9 ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by lia) 2
  have hcube := Nat.mul_le_mul_right (n + 1) hsquare
  simp only [precision, pow_succ, pow_zero, one_mul] at hcube ⊢
  omega

/-- A polynomially bounded advice family costs only a polynomial factor in the clock: a budget
polynomial in the advice-carrying encoding is dominated by one polynomial in the encoding of the
parameter and word alone. -/
private theorem exists_advice_budget_le {advice : ℕ → List Bool}
    (hadvice : PolynomiallyBounded (fun n => (advice n).length)) (c d : ℕ) :
    ∃ c' d' : ℕ, ∀ n word,
      c * ((encPair (encPair encUnary encBits) encBits ((n, advice n), word)).length + 1) ^ d ≤
        c' * ((encPair encUnary encBits (n, word)).length + 1) ^ d' := by
  obtain ⟨C, D, hC⟩ := polynomiallyBounded_iff_le.mp hadvice
  refine ⟨c * (2 * C + 4) ^ d, (D + 1) * d, fun n word => ?_⟩
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
  set L := 2 * n + 1 + word.length + 1 with hL
  have hLD : L ≤ L ^ (D + 1) := Nat.le_self_pow (Nat.succ_ne_zero D) L
  have hCL : C * (n + 1) ^ D ≤ C * L ^ (D + 1) :=
    Nat.mul_le_mul_left C
      ((Nat.pow_le_pow_left (by omega) D).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ D)))
  have hC1 : C ≤ C * L ^ (D + 1) := Nat.le_mul_of_pos_right C (by omega)
  have hbase : 2 * (2 * n + 1 + (advice n).length) + 1 + word.length + 1 ≤
      (2 * C + 4) * L ^ (D + 1) := by
    have := hC n
    rw [add_mul, mul_assoc]
    omega
  calc c * (2 * (2 * n + 1 + (advice n).length) + 1 + word.length + 1) ^ d
      ≤ c * ((2 * C + 4) * L ^ (D + 1)) ^ d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hbase d)
    _ = c * (2 * C + 4) ^ d * L ^ ((D + 1) * d) := by rw [mul_pow, ← pow_mul, mul_assoc]

/-- **The prediction gap relative to fixed advice.** If inverting `f` is hard with a polynomially
bounded advice family, then every uniform strict PPT word predictor reading the same advice
eventually stays below the finite entropy threshold. The hashed-parity reduction turns the
predictor into an inverter that passes its advice through; the advice length enters only a
polynomial change of the predictor's coin budget. -/
theorem eventually_prediction_entropy_le_withAdvice {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) {advice : ℕ → List Bool}
    (hhard : InversionHardWithAdvice f advice)
    (hadvice : PolynomiallyBounded (fun n => (advice n).length))
    {Image : ℕ → Type} [∀ n, Finite (Image n)]
    (finiteFunction : ∀ n, BitString n → Image n) (encodeImage : ∀ n, Image n ↪ List Bool)
    (hencode : ∀ n x, f (List.ofFn x) = encodeImage n (finiteFunction n x))
    (imageLength : ℕ → ℕ) (hlength : ∀ n image, (encodeImage n image).length = imageLength n)
    (adversary : (ℕ × List Bool) × List Bool → ProbComp Bool)
    (hPPT : IsPPTOn encAdvisedInput encBool adversary) :
    ∀ᶠ n in atTop, 2 * Pr[predictionGame (sample f)
        (fun n word => adversary ((n, advice n), word)) n] - 1 ≤
      1 - PMF.conditionalEntropy (joint (count := hashCount n) (finiteFunction n)) -
        1 / (hashCount n : ℝ) := by
  obtain ⟨c, d, evaluate, hefficient, _, hrealize⟩ := hPPT.exists_total_seeded_evaluator
  obtain ⟨c', d', hbudget⟩ := exists_advice_budget_le hadvice c d
  -- The inverter captures the advice word from its own input.
  let advisedEvaluate : (ℕ × List Bool) × List Bool → (ℕ × List Bool) → List Bool → Bool :=
    fun ((_, word), _) (m, observation) coins => evaluate ((m, word), observation) coins
  have hevaluate := hefficient.comp (show ComputableInPolyTime
    (fun ((((_, word), _), (m, observation)), tape) => (((m, word), observation), tape) :
      (((ℕ × List Bool) × List Bool) × (ℕ × List Bool)) × List Bool →
        ((ℕ × List Bool) × List Bool) × List Bool)
    (encPair (encPair (encPair (encPair encUnary encBits) encBits) (encPair encUnary encBits))
      encBits) (encPair (encPair (encPair encUnary encBits) encBits) encBits) by fun_prop)
  have hinverter := isPPTOn_wordInverter (evaluate := advisedEvaluate)
    (parameter := fun ((n, _), _) => n) (image := fun ((_, _), image) => image) hf hevaluate
    (by fun_prop) (by fun_prop) c' d' 3
  have hinversion := hhard.inversion_negligible _ hinverter
  have hloss : Negligible (fun n => 128 * (dyadicSize (16 * hashCount n) : ℝ≥0) ^ 2 *
      Game.succProbability (ProbComp.eval (inversionGame f
        (fun n image => wordInverter f (advisedEvaluate ((n, advice n), image)) c' d' 3 n image)
          n))) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      hinversion.polynomiallyBounded_mul
        (show PolynomiallyBounded (fun n => 128 * dyadicSize (16 * hashCount n) ^ 2) by fun_prop)
  have hsmall := hloss.eventually_le_inv_polynomial
    hashCount_polynomiallyBounded (fun n => Nat.pos_of_ne_zero (NeZero.ne (hashCount n)))
  filter_upwards [hsmall, eventually_ge_atTop 8] with n hsmall hn
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast,
    Game.coe_succProbability] at hsmall
  have h := word_prediction_entropy_le f (finiteFunction n) (encodeImage n)
    (hencode n) (hlength n) (fun n word => adversary ((n, advice n), word))
    (fun (m, word) coins => evaluate ((m, advice m), word) coins) c' d'
    (fun m word budget hle => hrealize ((m, advice m), word) budget ((hbudget m word).trans hle))
    3 (precision_three_ge hn)
  have hsame : Pr[inversionGame f (wordInverter f
      (fun (m, word) coins => evaluate ((m, advice m), word) coins) c' d' 3) n] =
      Pr[inversionGame f (fun n image =>
        wordInverter f (advisedEvaluate ((n, advice n), image)) c' d' 3 n image) n] := rfl
  rw [div_eq_mul_one_div (2 : ℝ), hsame] at h
  linarith only [h, hsmall]

/-- A function whose inversion is hard with a polynomially bounded advice family, and which has a
fixed image width at each parameter, gives a samplable pair whose gap holds against predictors with
the same advice. The gap is inverse-linear in the original input length. -/
theorem pair_hasGapWithAdvice {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) {advice : ℕ → List Bool}
    (hhard : InversionHardWithAdvice f advice)
    (hadvice : PolynomiallyBounded (fun n => (advice n).length))
    {Image : ℕ → Type} [∀ n, Finite (Image n)]
    (finiteFunction : ∀ n, BitString n → Image n) (encodeImage : ∀ n, Image n ↪ List Bool)
    (hencode : ∀ n x, f (List.ofFn x) = encodeImage n (finiteFunction n x))
    (imageLength : ℕ → ℕ) (hlength : ∀ n image, (encodeImage n image).length = imageLength n) :
    (pair f hf finiteFunction encodeImage hencode).HasGapWithAdvice
      (fun n => 1 / (hashCount n : ℝ)) advice :=
  eventually_prediction_entropy_le_withAdvice hf hhard hadvice finiteFunction encodeImage hencode
    imageLength hlength

end Cslib.Crypto.Pseudoentropy.HashPair

namespace Cslib.Crypto

open Probability BitString Pseudoentropy Turing.MultiTapeTM

/-- The samplable pair of a function with a fixed output length: its gap holds against predictors
with any polynomially bounded advice family for which inverting the function is hard. -/
private theorem exists_pseudoentropyPair_of_fixedOutputLength {g : List Bool → List Bool}
    {length : ℕ → ℕ} (hg : ComputableInPolyTime g encBits encBits)
    (hlength : ∀ input, (g input).length = length input.length) :
    ∃ pair : SamplablePair, ∀ advice : ℕ → List Bool, InversionHardWithAdvice g advice →
      PolynomiallyBounded (fun n => (advice n).length) →
        pair.HasGapWithAdvice (fun n => 1 / (2 * ((n : ℝ) + 7))) advice := by
  let finiteFunction (n : ℕ) (x : BitString n) := ofList (length n) (g (List.ofFn x))
  let encodeImage (n : ℕ) : BitString (length n) ↪ List Bool :=
    ⟨List.ofFn, fun _ _ h => List.ofFn_inj.mp h⟩
  have hencode (n : ℕ) (x : BitString n) :
      g (List.ofFn x) = encodeImage n (finiteFunction n x) :=
    (ofFn_ofList (by simp [hlength])).symm
  refine ⟨HashPair.pair g hg finiteFunction encodeImage hencode, fun advice hhard hadvice =>
    (HashPair.pair_hasGapWithAdvice hg hhard hadvice finiteFunction encodeImage hencode length
      (fun _ _ => List.length_ofFn)).mono (fun n => ?_)⟩
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (HashPair.hashCount n))
  · exact_mod_cast HashPair.hashCount_le n

/-- Every one-way word function yields an exactly samplable pseudoentropy pair with an explicit
inverse-polynomial prediction gap. Normalization handles arbitrary original output lengths. -/
theorem OneWay.exists_pseudoentropyPair {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ pair : SamplablePair, pair.HasGap (fun n => 1 / (2 * ((n : ℝ) + 7))) := by
  obtain ⟨g, length, hg, hlength, _⟩ := hf.exists_fixedOutputLength
  obtain ⟨hpoly, hhard⟩ := oneWay_iff_inversionHardWithAdvice_nil.mp hg
  obtain ⟨pair, hpair⟩ := exists_pseudoentropyPair_of_fixedOutputLength hpoly hlength
  exact ⟨pair, SamplablePair.hasGap_iff_hasGapWithAdvice_nil.mpr
    (hpair _ hhard (PolynomiallyBounded.const 0))⟩

/-- Every nonuniformly one-way word function yields an exactly samplable pair whose
inverse-polynomial prediction gap holds against predictors with every polynomially bounded advice
family. -/
theorem NonuniformOneWay.exists_pseudoentropyPair {f : List Bool → List Bool}
    (hf : NonuniformOneWay f) :
    ∃ pair : SamplablePair, ∀ advice : ℕ → List Bool,
      PolynomiallyBounded (fun n => (advice n).length) →
        pair.HasGapWithAdvice (fun n => 1 / (2 * ((n : ℝ) + 7))) advice := by
  obtain ⟨g, length, hg, hlength, _⟩ := hf.exists_fixedOutputLength
  obtain ⟨pair, hpair⟩ := exists_pseudoentropyPair_of_fixedOutputLength hg.polyTime hlength
  exact ⟨pair, fun advice hadvice => hpair advice (hg.secure advice hadvice) hadvice⟩

end Cslib.Crypto
