/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GoldreichLevin.Parameters
public import Complexity.Probability.UniversalHash

import Complexity.Probability.Guessing
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.ToReal

/-!
# Inversion from a predictor with partially uniform leakage

The inverter guesses the public hash value, fixes the predictor's other public and private
randomness, and runs the shared Goldreich--Levin decoder. A short hash prefix is close to uniform
on a fiber; guessing the remaining suffix loses only its cardinality. The unknown preimage and
the split point occur only in the proof, never in the inverter.

These are finite reduction bounds. The hashed parity pair additionally needs a choice of split
points, averaging over hash lengths and images, and a uniform PPT implementation.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.guessInverter`: guess the digest and run Goldreich–Levin.

## Main results

* `Cslib.Crypto.Pseudoentropy.correlation_le_guessInverter`: prediction-to-inversion bound.
* `Cslib.Probability.IsTwoUniversal.fiber_correlation_le_guessInverter`:
  specialize to a uniform fiber without regularity assumptions.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 4, Lemma 4.
  We use decoder success as the nonnegative game score in Games 2--5, instead of maximizing
  signed prediction advantage over all preimages. This gives the same kind of polynomial loss.

Adapted from Crypto/Computational/Pseudoentropy/Reduction.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the pinned finite-PMF distance
and shared decoder.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF BitString GoldreichLevin

variable {n : ℕ} {Image Seed Digest : Type*} [DecidableEq Image]

/-- Guess the entire leakage and run the Goldreich–Levin decoder. Its behavior is independent of
the prefix/suffix split used to analyze it. `seed` may include saved predictor coins. -/
noncomputable def guessInverter [Fintype Digest] [Nonempty Digest]
    (f : BitString n → Image) (predictor : Seed → Digest → BitString n → Bool)
    (seed : PMF Seed) (precision : ℕ) (image : Image) : PMF (BitString n) :=
  seed.bind fun s => (PMF.uniformOfFintype Digest).bind fun digest =>
    invertFixed f (predictor s digest) (maskCount n precision) image

/-- Re-encoding the guessed digest by an equivalence preserves the inverter exactly. -/
theorem guessInverter_equiv [Fintype Digest] [Nonempty Digest]
    {Other : Type*} [Fintype Other] [Nonempty Other]
    (f : BitString n → Image) (predictor : Seed → Digest → BitString n → Bool)
    (seed : PMF Seed) (precision : ℕ) (image : Image) (e : Other ≃ Digest) :
    guessInverter f (fun s digest => predictor s (e digest)) seed precision image =
      guessInverter f predictor seed precision image := by
  unfold guessInverter
  congr 1 with s : 1
  rw [← uniformOfFintype_map_equiv e, PMF.bind_map]
  rfl

/-- Guessing the leakage converts parity correlation into inversion success. Only its prefix
must be statistically close to uniform; its suffix costs the number of possible guesses. -/
theorem correlation_le_guessInverter [Fintype Seed]
    {Prefix Suffix : Type*} [Fintype Prefix] [Fintype Suffix]
    [Nonempty Prefix] [Nonempty Suffix]
    (f : BitString n → Image) (image : Image) (source : PMF (BitString n))
    (hsource : ∀ x ∈ source.support, f x = image)
    (predictor : Seed → Prefix × Suffix → BitString n → Bool)
    (seed : PMF Seed) (hash : Seed → BitString n → Prefix × Suffix)
    (precision : ℕ) (hp : 0 < precision) :
    (∑ s, (seed s).toReal * ∑ x, (source x).toReal *
      (2 * agreement (predictor s (hash s x)) x - 1)) ≤
      1 / (precision : ℝ) +
      4 * dist (seededHash seed source (fun s x => (hash s x).1))
        (seed.bind (fun s => (PMF.uniformOfFintype Prefix).map (s, ·))) +
      2 * Fintype.card Suffix *
        (((guessInverter f predictor seed precision image).map
          (fun x => f x == image)) true).toReal := by
  let success (s : Seed) (digest : Prefix × Suffix) : ℝ :=
    (((invertFixed f (predictor s digest) (maskCount n precision) image).map
      (fun x => f x == image)) true).toReal
  have hsuccess (s : Seed) (digest : Prefix × Suffix) :
      0 ≤ success s digest ∧ success s digest ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, toReal_apply_le_one _ _⟩
  have hpoint (s : Seed) (x : BitString n) :
      (source x).toReal * (2 * agreement (predictor s (hash s x)) x - 1) ≤
        (source x).toReal * (1 / (precision : ℝ) + 2 * success s (hash s x)) := by
    by_cases hx : x ∈ source.support
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      simpa only [hsource x hx, success] using
        correlation_le_invertFixed f (predictor s (hash s x)) x precision hp
    · have hx0 : source x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hx
      simp only [hx0, ENNReal.toReal_zero, zero_mul, le_refl]
  have hprediction :
      (∑ s, (seed s).toReal * ∑ x, (source x).toReal *
        (2 * agreement (predictor s (hash s x)) x - 1)) ≤
      1 / (precision : ℝ) + 2 *
        ∑ s, (seed s).toReal * ∑ x, (source x).toReal * success s (hash s x) := by
    apply sum_le_affine
    intro s
    exact (Finset.sum_le_sum fun x _ => hpoint s x).trans_eq (sum_affine source _ _ _)
  have hguess := score_le_uniform_guess (seededHash seed source hash) seed success hsuccess
  simp only [seededHash, sum_bind_mul, sum_map_mul, PMF.map_bind, PMF.map_comp,
    Function.comp_def] at hguess
  have hprob : (((guessInverter f predictor seed precision image).map
      (fun x => f x == image)) true).toReal =
      ∑ s, (seed s).toReal * ∑ digest,
        (PMF.uniformOfFintype (Prefix × Suffix) digest).toReal * success s digest := by
    simp only [guessInverter, PMF.map_bind, bind_apply_toReal, success]
  rw [hprob]
  dsimp only [seededHash]
  nlinarith

/-- Universal hashing supplies the prefix error in the prediction-to-inversion bound. -/
theorem _root_.Cslib.Probability.IsTwoUniversal.correlation_le_guessInverter [Fintype Seed]
    {Prefix Suffix : Type*} [Fintype Prefix] [Fintype Suffix]
    [Nonempty Prefix] [Nonempty Suffix]
    (f : BitString n → Image) (image : Image) (source : PMF (BitString n))
    (hsource : ∀ x ∈ source.support, f x = image)
    (predictor : Seed → Prefix × Suffix → BitString n → Bool)
    {seed : PMF Seed} {hash : Seed → BitString n → Prefix × Suffix}
    (hhash : IsTwoUniversal seed (fun s x => (hash s x).1))
    (precision : ℕ) (hp : 0 < precision) :
    (∑ s, (seed s).toReal * ∑ x, (source x).toReal *
      (2 * agreement (predictor s (hash s x)) x - 1)) ≤
      1 / (precision : ℝ) +
      2 * Real.sqrt (Fintype.card Prefix * collisionProbability source) +
      2 * Fintype.card Suffix *
        (((guessInverter f predictor seed precision image).map
          (fun x => f x == image)) true).toReal := by
  have h := Pseudoentropy.correlation_le_guessInverter
    f image source hsource predictor seed hash precision hp
  have hdist := hhash.leftover_hash source
  linarith

open Classical in
/-- On a uniform fiber, the extraction error depends on its size. No regularity assumption
is made about the other fibers of the function. -/
theorem _root_.Cslib.Probability.IsTwoUniversal.fiber_correlation_le_guessInverter [Fintype Seed]
    {Prefix Suffix : Type*} [Fintype Prefix] [Fintype Suffix]
    [Nonempty Prefix] [Nonempty Suffix]
    (f : BitString n → Image) (image : Image) [Nonempty {x // f x = image}]
    (predictor : Seed → Prefix × Suffix → BitString n → Bool)
    {seed : PMF Seed} {hash : Seed → BitString n → Prefix × Suffix}
    (hhash : IsTwoUniversal seed (fun s x => (hash s x).1))
    (precision : ℕ) (hp : 0 < precision) :
    (∑ s, (seed s).toReal * ∑ x : {x // f x = image},
      (PMF.uniformOfFintype {x // f x = image} x).toReal *
        (2 * agreement (predictor s (hash s x)) x - 1)) ≤
      1 / (precision : ℝ) +
      2 * Real.sqrt (Fintype.card Prefix / (Nat.card {x // f x = image} : ℝ)) +
      2 * Fintype.card Suffix *
        (((guessInverter f predictor seed precision image).map
          (fun x => f x == image)) true).toReal := by
  let source := (PMF.uniformOfFintype {x // f x = image}).map Subtype.val
  have hsource : ∀ x ∈ source.support, f x = image := by
    intro x hx
    obtain ⟨preimage, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact preimage.property
  have h := IsTwoUniversal.correlation_le_guessInverter
    f image source hsource predictor hhash precision hp
  simpa only [source, sum_map_mul,
    collisionProbability_map_of_injective _ _ Subtype.val_injective,
    collisionProbability_uniform, Nat.card_eq_fintype_card, div_eq_mul_inv] using h

end Cslib.Crypto.Pseudoentropy
