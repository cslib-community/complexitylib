/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.Reduction
public import CslibFrontier.Crypto.Computational.Pseudoentropy.HashPair
public import CslibFrontier.Probability.BitString.LinearHash
public import CslibFrontier.Probability.UniformNat
import Mathlib.Logic.Equiv.Fin.Basic

import CslibFrontier.Probability.PMF.Expect

/-!
# The matrix-hash prediction-to-inversion bound

Split a leaked matrix hash into an almost uniform prefix and a short suffix. The inverter guesses
the entire digest uniformly and invokes Goldreich--Levin. Its definition does not use the split
point or the size of the image's fiber. Empty prefixes incur no extraction error.

The finite bounds also allow independent saved coins, reused across every decoder query.
`Pseudoentropy.WordReduction` implements the inverter as a word program.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.matrixPrediction`: prediction from a leaked matrix hash.
* `Cslib.Crypto.Pseudoentropy.matrixInverter`: one inverter for all fibers and hash lengths.

## Main results

* `Cslib.Crypto.Pseudoentropy.matrixPrediction_entropy_le_of_coins`:
  entropy threshold with independent saved predictor randomness.
* `Cslib.Crypto.Pseudoentropy.matrixInverter_success_ge`: the resulting polynomial loss.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 4, Lemma 4, Games 1--5.
  The hash family here is a public Boolean matrix; the suffix-guessing argument is the one
  developed in `Pseudoentropy.Reduction` and `Probability.Guessing`.

Adapted from Crypto/Computational/Pseudoentropy/HashReduction.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the pinned finite-PMF distance
and shared decoder.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF BitString GoldreichLevin

/-- The parity predictor receives the image, length, full public matrix, and leaked digest. -/
abbrev MatrixPredictor (n count : ℕ) (Image : Type*) :=
  Image → (i : Fin count) → (Fin count → BitString n) → BitString (i.val + 1) →
    BitString n → Bool

/-- The prediction game for the hashed parity construction, with uniform matrices. -/
noncomputable def matrixPrediction {n count : ℕ} [NeZero count] {Image : Type*}
    (f : BitString n → Image) (predictor : MatrixPredictor n count Image) : PMF Bool := do
  let x ← PMF.uniformOfFintype (BitString n)
  let i ← PMF.uniformOfFintype (Fin count)
  let rows ← PMF.uniformOfFintype (Fin count → BitString n)
  (PMF.uniformOfFintype (BitString n)).map fun query =>
    predictor (f x) i rows
      (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) x) query == x ⬝ᵥ query

/-- The inverter guesses a length, matrix, and digest, then invokes the common decoder. -/
noncomputable def matrixInverter {n count : ℕ} [NeZero count] {Image : Type*}
    [DecidableEq Image] (f : BitString n → Image) (predictor : MatrixPredictor n count Image)
    (precision : ℕ) (image : Image) : PMF (BitString n) := do
  let i ← PMF.uniformOfFintype (Fin count)
  guessInverter f (predictor image i) (PMF.uniformOfFintype (Fin count → BitString n))
    precision image

private theorem uniform_length_tail (count cutoff : ℕ) [NeZero count] (hcutoff : cutoff ≤ count) :
    (∑ i : Fin count, (PMF.uniformOfFintype (Fin count) i).toReal *
      (if cutoff < i.val + 1 then (1 : ℝ) else 0)) = 1 - cutoff / (count : ℝ) := by
  have hfilter : (Finset.range count).filter (fun i => cutoff < i + 1) =
      Finset.Ico cutoff count := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    lia
  have hcount : (count : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne count
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_fin, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => if cutoff < i + 1 then (1 : ℝ) else 0),
    ← Finset.sum_filter, hfilter]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hcutoff]
  field_simp

/-- A digest at most six bits longer than the logarithmic fiber size can be split into
an almost uniform prefix and a suffix with polynomially many guesses. This split is used only
in the proof; neither the inverter nor the predictor is given the fiber size. -/
theorem exists_short_hash_split (size width count : ℕ) (hsize : 0 < size) (hcount : 0 < count)
    (hwidth : width ≤ Nat.log 2 size + 6) :
    ∃ initial rest, width = initial + rest ∧
      (if initial = 0 then 0 else 2 * Real.sqrt ((2 : ℝ) ^ initial / size)) ≤
        1 / (8 * (count : ℝ)) ∧
      (2 : ℝ) ^ (rest + 1) ≤ 128 * (dyadicSize (16 * count) : ℝ) ^ 2 := by
  let margin := 2 * (Nat.log 2 (16 * count) + 1)
  let initial := min width (Nat.log 2 size - margin)
  let rest := width - initial
  have hinitial : initial ≤ width := min_le_left _ _
  have hrest : rest ≤ margin + 6 := by dsimp [initial, rest]; omega
  have hpower : (2 : ℝ) ^ margin = (dyadicSize (16 * count) : ℝ) ^ 2 := by
    simp only [margin, dyadicSize, Nat.cast_pow, Nat.cast_ofNat, pow_mul, mul_comm 2]
  refine ⟨initial, rest, by dsimp [rest]; omega, ?_, ?_⟩
  · split_ifs with hzero
    · positivity
    · have hinitial' : initial + margin ≤ Nat.log 2 size := by dsimp [initial] at *; omega
      have hsizePow : (2 : ℝ) ^ initial * (dyadicSize (16 * count) : ℝ) ^ 2 ≤ size := by
        rw [← hpower, ← pow_add]
        exact_mod_cast (Nat.pow_le_pow_right two_pos hinitial').trans
          (Nat.pow_log_le_self 2 hsize.ne')
      have hsizeReal : (0 : ℝ) < size := by exact_mod_cast hsize
      have hscale : (0 : ℝ) < dyadicSize (16 * count) := by
        exact_mod_cast dyadicSize_pos (16 * count)
      have hroot : Real.sqrt ((2 : ℝ) ^ initial / size) ≤
          1 / (dyadicSize (16 * count) : ℝ) := by
        apply Real.sqrt_le_iff.mpr ⟨by positivity, (div_le_iff₀ hsizeReal).mpr ?_⟩
        simpa only [div_pow, one_pow, div_mul_eq_mul_div, one_mul] using
          (le_div_iff₀ (sq_pos_of_pos hscale)).mpr hsizePow
      have hcountReal : (0 : ℝ) < count := by exact_mod_cast hcount
      have hscaleBound : 16 * (count : ℝ) ≤ dyadicSize (16 * count) := by
        exact_mod_cast (lt_dyadicSize (16 * count)).le
      have hinv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 16 * count) hscaleBound
      have hcancel : 2 * (1 / (16 * (count : ℝ))) = 1 / (8 * count) := by ring
      linarith only [hroot, hinv, hcancel]
  · calc
      _ ≤ (2 : ℝ) ^ (margin + 7) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by rw [pow_add, hpower]; norm_num; ring

open Classical in
/-- On each fiber, prediction from a matrix hash is bounded by the decoder's accuracy,
the prefix extraction error, and inversion with a uniform digest guess. The public matrix may
contain additional unused rows. -/
theorem matrix_fiber_correlation_le {n count initial rest : ℕ} {Image : Type*}
    [DecidableEq Image] (f : BitString n → Image) (image : Image)
    [Nonempty {x // f x = image}] (hlen : initial + rest ≤ count)
    (predictor : (Fin count → BitString n) → BitString (initial + rest) → BitString n → Bool)
    (precision : ℕ) (hp : 0 < precision) :
    (∑ rows, (PMF.uniformOfFintype (Fin count → BitString n) rows).toReal *
      ∑ x : {x // f x = image}, (PMF.uniformOfFintype {x // f x = image} x).toReal *
        (2 * agreement (predictor rows
          (LinearHash.hash (rows ∘ Fin.castLE hlen) x)) x - 1)) ≤
      1 / (precision : ℝ) +
      (if initial = 0 then 0 else
        2 * Real.sqrt ((2 : ℝ) ^ initial / Nat.card {x // f x = image})) +
      2 ^ (rest + 1) *
        (((guessInverter f predictor (PMF.uniformOfFintype (Fin count → BitString n))
          precision image).map (fun x => f x == image)) true).toReal := by
  let seed := PMF.uniformOfFintype (Fin count → BitString n)
  let source := (PMF.uniformOfFintype {x // f x = image}).map Subtype.val
  let append := Fin.appendEquiv (α := Bool) initial rest
  let hash (rows : Fin count → BitString n) x :=
    append.symm (LinearHash.hash (rows ∘ Fin.castLE hlen) x)
  let predict rows digest := predictor rows (append digest)
  have hsource : ∀ x ∈ source.support, f x = image := by
    intro x hx
    obtain ⟨preimage, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact preimage.property
  have hhash : IsTwoUniversal seed (fun rows x => (hash rows x).1) :=
    LinearHash.isTwoUniversal_prefix (by omega : initial ≤ count)
  have h := correlation_le_guessInverter f image source hsource predict seed hash precision hp
  have hinverter : guessInverter f predict seed precision image =
      guessInverter f predictor seed precision image :=
    guessInverter_equiv f predictor seed precision image append
  have hprefix : 4 * dist (seededHash seed source (fun rows x => (hash rows x).1))
      (seed.bind (fun rows => (PMF.uniformOfFintype (BitString initial)).map (rows, ·))) ≤
      if initial = 0 then 0 else
        2 * Real.sqrt ((2 : ℝ) ^ initial / Nat.card {x // f x = image}) := by
    split_ifs with hzero
    · subst initial
      rw [seededHash_eq_uniform_of_subsingleton, dist_self, mul_zero]
    · have hdist := hhash.leftover_hash source
      simp only [source, collisionProbability_map_of_injective _ _ Subtype.val_injective,
        collisionProbability_uniform,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
        ← div_eq_mul_inv] at hdist
      rw [Nat.card_eq_fintype_card]
      dsimp only [source]
      linarith only [hdist]
  simp only [source, sum_map_mul, predict, hash, Equiv.apply_symm_apply,
    hinverter, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] at h
  dsimp only [seed] at h hprefix
  rw [pow_succ']
  linarith only [h, hprefix]

open Classical in
/-- A hash within six bits of the logarithmic fiber size has a uniform polynomial reduction
loss. This one inverter works for every fiber; their sizes determine only its analysis. -/
theorem matrix_fiber_correlation_le_of_length {n count width : ℕ} {Image : Type*}
    [DecidableEq Image] (f : BitString n → Image) (image : Image)
    [Nonempty {x // f x = image}] (hcount : 0 < count) (hlen : width ≤ count)
    (hwidth : width ≤ Nat.log 2 (Nat.card {x // f x = image}) + 6)
    (predictor : (Fin count → BitString n) → BitString width → BitString n → Bool)
    (precision : ℕ) (hp : 8 * count ≤ precision) :
    (∑ rows, (PMF.uniformOfFintype (Fin count → BitString n) rows).toReal *
      ∑ x : {x // f x = image}, (PMF.uniformOfFintype {x // f x = image} x).toReal *
        (2 * agreement (predictor rows
          (LinearHash.hash (rows ∘ Fin.castLE hlen) x)) x - 1)) ≤
      1 / (4 * (count : ℝ)) + 128 * (dyadicSize (16 * count) : ℝ) ^ 2 *
        (((guessInverter f predictor (PMF.uniformOfFintype (Fin count → BitString n))
          precision image).map (fun x => f x == image)) true).toReal := by
  have hsize : 0 < Nat.card {x // f x = image} := Nat.card_pos
  obtain ⟨initial, rest, rfl, herror, hguess⟩ :=
    exists_short_hash_split _ width count hsize hcount hwidth
  have h := matrix_fiber_correlation_le f image hlen predictor precision
    (Nat.lt_of_lt_of_le (Nat.mul_pos (by decide) hcount) hp)
  have hcountReal : (0 : ℝ) < count := by exact_mod_cast hcount
  have hpReal : 8 * (count : ℝ) ≤ precision := by exact_mod_cast hp
  have haccuracy := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8 * count) hpReal
  have hweighted := mul_le_mul_of_nonneg_right hguess (ENNReal.toReal_nonneg
    (a := ((guessInverter f predictor
      (PMF.uniformOfFintype (Fin count → BitString n)) precision image).map
        (fun x => f x == image)) true))
  have hcancel : 1 / (8 * (count : ℝ)) + 1 / (8 * count) = 1 / (4 * count) := by ring
  linarith only [h, herror, haccuracy, hweighted, hcancel]

open Classical in
/-- Averaging all hash lengths removes the restriction on digest size. A range at least
`n + 6` makes the truncation threshold valid even for the largest possible fiber. -/
theorem matrix_fiber_mean_correlation_le {n count : ℕ} [NeZero count] {Image : Type*}
    [DecidableEq Image] (f : BitString n → Image) (image : Image)
    [Nonempty {x // f x = image}] (hcount : n + 6 ≤ count)
    (predictor : MatrixPredictor n count Image) (precision : ℕ) (hp : 8 * count ≤ precision) :
    (∑ i : Fin count, (PMF.uniformOfFintype (Fin count) i).toReal *
      ∑ rows, (PMF.uniformOfFintype (Fin count → BitString n) rows).toReal *
        ∑ x : {x // f x = image}, (PMF.uniformOfFintype {x // f x = image} x).toReal *
          (2 * agreement (predictor image i rows
            (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) x)) x - 1)) ≤
      1 - ((Nat.log 2 (Nat.card {x // f x = image}) : ℝ) + 6) / count +
        1 / (4 * (count : ℝ)) + 128 * (dyadicSize (16 * count) : ℝ) ^ 2 *
        (((matrixInverter f predictor precision image).map
          (fun x => f x == image)) true).toReal := by
  let cutoff := Nat.log 2 (Nat.card {x // f x = image}) + 6
  let success (i : Fin count) : ℝ :=
    (((guessInverter f (predictor image i) (PMF.uniformOfFintype (Fin count → BitString n))
      precision image).map (fun x => f x == image)) true).toReal
  have hcutoff : cutoff ≤ count := by
    have hcard : Nat.card {x // f x = image} ≤ 2 ^ n := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin] using Fintype.card_subtype_le (fun x => f x = image)
    have hlog := Nat.log_mono_right (b := 2) hcard
    rw [Nat.log_pow Nat.one_lt_two] at hlog
    dsimp [cutoff]
    omega
  have hpoint (i : Fin count) :
      (∑ rows, (PMF.uniformOfFintype (Fin count → BitString n) rows).toReal *
        ∑ x : {x // f x = image}, (PMF.uniformOfFintype {x // f x = image} x).toReal *
          (2 * agreement (predictor image i rows
            (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) x)) x - 1)) ≤
      (if cutoff < i.val + 1 then 1 else 0) + 1 / (4 * (count : ℝ)) +
        128 * (dyadicSize (16 * count) : ℝ) ^ 2 * success i := by
    split_ifs with hlong
    · have hmean :
          (∑ rows, (PMF.uniformOfFintype (Fin count → BitString n) rows).toReal *
            ∑ x : {x // f x = image}, (PMF.uniformOfFintype {x // f x = image} x).toReal *
              (2 * agreement (predictor image i rows
                (LinearHash.hash (rows ∘ Fin.castLE
                  (Nat.succ_le_of_lt i.isLt)) x)) x - 1)) ≤ 1 := by
        refine sum_mul_le _ _ _ fun rows => sum_mul_le _ _ _ fun x => ?_
        have hle := agreement_le_one (predictor image i rows
          (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) x)) x
        linarith only [hle]
      have hnonneg : 0 ≤ 1 / (4 * (count : ℝ)) +
          128 * (dyadicSize (16 * count) : ℝ) ^ 2 * success i := by
        dsimp only [success]
        positivity
      linarith only [hmean, hnonneg]
    · simpa only [zero_add] using matrix_fiber_correlation_le_of_length f image (by omega)
        (Nat.succ_le_of_lt i.isLt) (by dsimp [cutoff] at hlong; omega)
        (predictor image i) precision hp
  calc
    _ ≤ ∑ i : Fin count, (PMF.uniformOfFintype (Fin count) i).toReal *
        ((if cutoff < i.val + 1 then 1 else 0) + 1 / (4 * (count : ℝ)) +
          128 * (dyadicSize (16 * count) : ℝ) ^ 2 * success i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) ENNReal.toReal_nonneg)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_toReal, one_mul, mul_left_comm _ (128 * (dyadicSize (16 * count) : ℝ) ^ 2),
        ← Finset.mul_sum, uniform_length_tail count cutoff hcutoff,
        cutoff, Nat.cast_add, Nat.cast_ofNat,
        matrixInverter, monad_bind_eq_bind, PMF.map_bind, bind_apply_toReal, success]

/-- The complete finite reduction bound, averaged over images as well as hash lengths.
All fibers share one inverter and one precision; no regularity or injectivity is required. -/
theorem matrixPrediction_correlation_le {n count : ℕ} [NeZero count] {Image : Type*}
    [Finite Image] [DecidableEq Image] (f : BitString n → Image) (hcount : n + 6 ≤ count)
    (predictor : MatrixPredictor n count Image) (precision : ℕ) (hp : 8 * count ≤ precision) :
    2 * (matrixPrediction f predictor true).toReal - 1 ≤
      1 - ((∑ x, (PMF.uniformOfFintype (BitString n) x).toReal *
        Real.logb 2 (Nat.card {y // f y = f x})) + 4) / count +
      128 * (dyadicSize (16 * count) : ℝ) ^ 2 *
        (inversionExperiment f (matrixInverter f predictor precision) true).toReal := by
  classical
  let source := PMF.uniformOfFintype (BitString n)
  let joint := source.map (fun x => (f x, x))
  let correlation (image : Image) (x : BitString n) : ℝ :=
    ∑ i : Fin count, (PMF.uniformOfFintype (Fin count) i).toReal *
      ∑ rows, (PMF.uniformOfFintype (Fin count → BitString n) rows).toReal *
        (2 * agreement (predictor image i rows
          (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) x)) x - 1)
  let success (image : Image) : ℝ :=
    (((matrixInverter f predictor precision image).map (fun x => f x == image)) true).toReal
  have hpoint (x : BitString n) :
      (∑ y, (conditionalSnd joint (f x) y).toReal * correlation (f x) y) ≤
        1 - (Real.logb 2 (Nat.card {y // f y = f x}) + 4) / count +
          128 * (dyadicSize (16 * count) : ℝ) ^ 2 * success (f x) := by
    let : Nonempty {y // f y = f x} := ⟨⟨x, rfl⟩⟩
    have h := matrix_fiber_mean_correlation_le f (f x) hcount predictor precision hp
    have hgroup : (∑ y, (conditionalSnd joint (f x) y).toReal * correlation (f x) y) =
        ∑ i : Fin count, (PMF.uniformOfFintype (Fin count) i).toReal *
          ∑ rows, (PMF.uniformOfFintype (Fin count → BitString n) rows).toReal *
            ∑ y : {y // f y = f x},
              (PMF.uniformOfFintype {y // f y = f x} y).toReal *
                (2 * agreement (predictor (f x) i rows
                  (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) y)) y - 1) := by
      dsimp only [joint, source]
      rw [conditionalSnd_uniform_map, sum_map_mul]
      simp only [correlation, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun rows _ => Finset.sum_congr rfl fun y _ =>
        (mul_left_comm _ _ _).trans (congrArg (_ * ·)
          ((mul_left_comm _ _ _).trans (congrArg (_ * ·) (congrArg (· * _)
            (congrArg (fun inst => (@PMF.uniformOfFintype { y // f y = f x } inst _ y).toReal)
              (Subsingleton.elim _ _))))))
    have hlog : Real.logb 2 (Nat.card {y // f y = f x}) <
        (Nat.log 2 (Nat.card {y // f y = f x}) : ℝ) + 1 := by
      simpa only [← Nat.cast_ofNat (R := ℝ) (n := 2), Real.natFloor_logb_natCast] using
        Nat.lt_floor_add_one (Real.logb 2 (Nat.card {y // f y = f x}))
    have hmargin : (Real.logb 2 (Nat.card {y // f y = f x}) + 4) / (count : ℝ) ≤
        ((Nat.log 2 (Nat.card {y // f y = f x}) : ℝ) + 6) / count - 1 / (4 * count) := by
      calc
        _ ≤ ((Nat.log 2 (Nat.card {y // f y = f x}) : ℝ) + 23 / 4) / count :=
          div_le_div_of_nonneg_right (by linarith only [hlog]) (Nat.cast_nonneg count)
        _ = _ := by ring
    rw [hgroup]
    dsimp only [success]
    linarith only [h, hmargin]
  have havg := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (hpoint x) (ENNReal.toReal_nonneg (a := source x)))
  rw [sum_conditionalSnd_map] at havg
  have hprediction : (∑ x, (source x).toReal * correlation (f x) x) =
      2 * (matrixPrediction f predictor true).toReal - 1 := by
    have ha (value : ℝ) : 2 * value - 1 = -1 + 2 * value := by ring
    simp only [correlation, ha, sum_affine, agreement_eq_probability,
      matrixPrediction, monad_bind_eq_bind, bind_apply_toReal, source]
  rw [hprediction] at havg
  apply havg.trans_eq
  simp only [mul_add, mul_sub, mul_one, ← mul_div_assoc, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul, sum_toReal, one_mul,
    mul_left_comm _ (128 * (dyadicSize (16 * count) : ℝ) ^ 2), ← Finset.mul_sum,
    inversionExperiment, monad_bind_eq_bind, bind_apply_toReal, success, source]

/-- Prediction beyond the hashed pair's entropy threshold forces inversion with polynomial
loss. This is the finite content of Holenstein's Lemma 4, for public matrix hashing. -/
theorem matrixPrediction_entropy_le {n count : ℕ} [NeZero count] {Image : Type*}
    [Finite Image] [DecidableEq Image] (f : BitString n → Image) (hcount : n + 6 ≤ count)
    (predictor : MatrixPredictor n count Image) (precision : ℕ) (hp : 8 * count ≤ precision) :
    2 * (matrixPrediction f predictor true).toReal - 1 +
        conditionalEntropy (HashPair.joint (count := count) f) ≤
      1 - 2 / (count : ℝ) + 128 * (dyadicSize (16 * count) : ℝ) ^ 2 *
        (inversionExperiment f (matrixInverter f predictor precision) true).toReal := by
  have hprediction := matrixPrediction_correlation_le f hcount predictor precision hp
  have hentropy := HashPair.conditionalEntropy_joint_le (count := count) f
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    ENNReal.toReal_inv, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ← div_eq_inv_mul, ← Finset.sum_div] at hprediction
  apply (add_le_add hprediction hentropy).trans_eq
  ring

/-- The entropy reduction survives independent predictor randomness. The inverter samples one
coin tape and reuses the resulting deterministic predictor throughout all decoder calls. -/
theorem matrixPrediction_entropy_le_of_coins {n count : ℕ} [NeZero count] {Image Coins : Type*}
    [Finite Image] [DecidableEq Image] [Finite Coins]
    (f : BitString n → Image) (hcount : n + 6 ≤ count) (coins : PMF Coins)
    (predictor : Coins → MatrixPredictor n count Image)
    (precision : ℕ) (hp : 8 * count ≤ precision) :
    2 * ((coins.bind (fun seed => matrixPrediction f (predictor seed))) true).toReal - 1 +
        conditionalEntropy (HashPair.joint (count := count) f) ≤
      1 - 2 / (count : ℝ) + 128 * (dyadicSize (16 * count) : ℝ) ^ 2 *
        (inversionExperiment f (fun image => coins.bind
          (fun seed => matrixInverter f (predictor seed) precision image)) true).toReal := by
  let := Fintype.ofFinite Coins
  have h := Finset.sum_le_sum (s := Finset.univ) (fun seed _ =>
    mul_le_mul_of_nonneg_left (matrixPrediction_entropy_le f hcount (predictor seed) precision hp)
      (ENNReal.toReal_nonneg (a := coins seed)))
  simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_left_comm _ (2 : ℝ), mul_left_comm _ (128 * (dyadicSize (16 * count) : ℝ) ^ 2),
    ← Finset.mul_sum, ← Finset.sum_mul, sum_toReal, one_mul] at h
  simpa only [inversionExperiment_bind, bind_apply_toReal] using h

/-- Beating the entropy threshold by `1 / count` yields inverse-polynomial inversion success.
Since `dyadicSize (16 * count) ≤ 32 * count + 2`, the denominator is cubic in the hash range. -/
theorem matrixInverter_success_ge {n count : ℕ} [NeZero count] {Image : Type*}
    [Finite Image] [DecidableEq Image] (f : BitString n → Image) (hcount : n + 6 ≤ count)
    (predictor : MatrixPredictor n count Image) (precision : ℕ) (hp : 8 * count ≤ precision)
    (hprediction : 1 - conditionalEntropy (HashPair.joint (count := count) f) - 1 / (count : ℝ) ≤
      2 * (matrixPrediction f predictor true).toReal - 1) :
    1 / (128 * count * (dyadicSize (16 * count) : ℝ) ^ 2) ≤
      (inversionExperiment f (matrixInverter f predictor precision) true).toReal := by
  have h := matrixPrediction_entropy_le f hcount predictor precision hp
  have hscale : (0 : ℝ) < dyadicSize (16 * count) := by
    exact_mod_cast dyadicSize_pos (16 * count)
  rw [show (1 : ℝ) / (128 * count * (dyadicSize (16 * count) : ℝ) ^ 2) =
    (1 / (count : ℝ)) / (128 * (dyadicSize (16 * count) : ℝ) ^ 2) by ring,
    div_le_iff₀' (by positivity)]
  have htwo : (2 : ℝ) / count = 2 * (1 / count) := by ring
  linarith only [h, hprediction, htwo]

end Cslib.Crypto.Pseudoentropy
