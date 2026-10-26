/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.WordReduction
import Complexity.Languages.Probabilistic.Notation
import Complexity.Crypto.Computational.OneWay.Normalize
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Crypto.Negligible.Basic

/-!
# The pseudoentropy prediction gap from one-wayness

The executable hashed parity reduction has polynomial loss. One-wayness therefore makes its
inversion term negligible, leaving an inverse-polynomial gap between feasible prediction and
the entropy threshold. Each predictor supplies one inverter with a fixed precision degree;
neither its code nor its choice of saved randomness depends on a nonuniform advice string.

## Main results

* `Cslib.Crypto.Pseudoentropy.HashPair.pair_hasGap`: prediction gap for normalized word functions.
* `Cslib.Crypto.OneWay.exists_pseudoentropyPair`: every uniform OWF gives an exactly samplable
  pair with an inverse-linear prediction gap, including variable-length original images.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Definition 4 and Section 4, Lemmas 3 and 4.
  We use the public matrix and dyadic-range variant proved in `HashReduction`. This module
  discharges the inversion hypothesis using uniform strict PPT one-wayness.

Adapted from Crypto/Computational/Pseudoentropy/OneWay.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed saved seeds and nonnegative security games.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.HashPair

open Probability BitString GoldreichLevin Filter Turing.MultiTapeTM
open scoped NNReal

/-- A single cubic precision suffices for all sufficiently large dimensions. -/
theorem precision_three_ge {n : ℕ} (hn : 8 ≤ n) :
    8 * hashCount n ≤ precision 3 n := by
  have hcount := hashCount_le n
  have hsquare : 9 ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by lia) 2
  have hcube := Nat.mul_le_mul_right (n + 1) hsquare
  simp only [precision, pow_succ] at *
  nlinarith

/-- The finite entropy threshold holds eventually against every uniform PPT word predictor.
The image may have any fixed width at each parameter; it need not be a permutation or regular. -/
theorem eventually_prediction_entropy_le {f : List Bool → List Bool} (hf : OneWay f)
    {Image : ℕ → Type} [∀ n, Finite (Image n)]
    (finiteFunction : ∀ n, BitString n → Image n) (encodeImage : ∀ n, Image n ↪ List Bool)
    (hencode : ∀ n x, f (List.ofFn x) = encodeImage n (finiteFunction n x))
    (imageLength : ℕ → ℕ) (hlength : ∀ n image, (encodeImage n image).length = imageLength n)
    (adversary : Distinguisher) (hPPT : IsPPT encBool adversary) :
    ∀ᶠ n in atTop, 2 * Pr[predictionGame (sample f) adversary n] - 1 ≤
      1 - PMF.conditionalEntropy (joint (count := hashCount n) (finiteFunction n)) -
        1 / (hashCount n : ℝ) := by
  obtain ⟨c, d, evaluate, hefficient, _, hrealize⟩ := hPPT.on.exists_total_seeded_evaluator
  have hinversion := hf.inversion_negligible _
    (isPPT_wordInverter hf.polyTime (.of_tidy hefficient) c d 3)
  have hloss : Negligible (fun n => 128 * (dyadicSize (16 * hashCount n) : ℝ≥0) ^ 2 *
      Game.succProbability
        (ProbComp.eval (inversionGame f (wordInverter f evaluate c d 3) n))) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      hinversion.polynomiallyBounded_mul
        (show PolynomiallyBounded (fun n => 128 * dyadicSize (16 * hashCount n) ^ 2) by fun_prop)
  have hsmall := hloss.eventually_le_inv_polynomial
    hashCount_polynomiallyBounded (fun n => Nat.pos_of_ne_zero (NeZero.ne (hashCount n)))
  filter_upwards [hsmall, eventually_ge_atTop 8] with n hsmall hn
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast,
    Game.coe_succProbability] at hsmall
  have h := word_prediction_entropy_le f (finiteFunction n) (encodeImage n)
    (hencode n) (hlength n) adversary evaluate c d (fun n input => hrealize (n, input))
    3 (precision_three_ge hn)
  have htwo : (2 : ℝ) / hashCount n = 2 * (1 / (hashCount n : ℝ)) := by ring
  rw [htwo] at h
  linarith

/-- A one-way function with a fixed image width at each parameter gives a samplable
pseudoentropy pair. The gap is inverse-linear in the original input length. -/
theorem pair_hasGap {f : List Bool → List Bool} (hf : OneWay f)
    {Image : ℕ → Type} [∀ n, Finite (Image n)]
    (finiteFunction : ∀ n, BitString n → Image n) (encodeImage : ∀ n, Image n ↪ List Bool)
    (hencode : ∀ n x, f (List.ofFn x) = encodeImage n (finiteFunction n x))
    (imageLength : ℕ → ℕ) (hlength : ∀ n image, (encodeImage n image).length = imageLength n) :
    (pair f hf.polyTime finiteFunction encodeImage hencode).HasGap
      (fun n => 1 / (hashCount n : ℝ)) :=
  eventually_prediction_entropy_le hf finiteFunction encodeImage hencode imageLength hlength

end Cslib.Crypto.Pseudoentropy.HashPair

namespace Cslib.Crypto

open Probability BitString Pseudoentropy Turing.MultiTapeTM

/-- Every one-way word function yields an exactly samplable pseudoentropy pair with an explicit
inverse-polynomial prediction gap. Normalization handles arbitrary original output lengths. -/
theorem OneWay.exists_pseudoentropyPair {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ pair : SamplablePair, pair.HasGap (fun n => 1 / (2 * ((n : ℝ) + 7))) := by
  obtain ⟨g, length, hg, hlength, _⟩ := hf.exists_fixedOutputLength
  let finiteFunction (n : ℕ) (x : BitString n) := ofList (length n) (g (List.ofFn x))
  let encodeImage (n : ℕ) : BitString (length n) ↪ List Bool :=
    ⟨List.ofFn, fun _ _ h => List.ofFn_inj.mp h⟩
  have hencode (n : ℕ) (x : BitString n) :
      g (List.ofFn x) = encodeImage n (finiteFunction n x) := by
    exact (ofFn_ofList (by simp [hlength])).symm
  refine ⟨HashPair.pair g hg.polyTime finiteFunction encodeImage hencode,
    (HashPair.pair_hasGap hg finiteFunction encodeImage hencode length
      (fun _ _ => List.length_ofFn)).mono
      (fun n => ?_)⟩
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (HashPair.hashCount n))
  · exact_mod_cast HashPair.hashCount_le n

end Cslib.Crypto
