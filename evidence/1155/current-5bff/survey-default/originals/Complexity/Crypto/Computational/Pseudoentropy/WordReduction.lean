/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.HashReduction
public import Complexity.Crypto.Computational.Pseudoentropy.Basic
public import Complexity.Crypto.Computational.GoldreichLevin.WordDecoder
public import Complexity.Crypto.Computational.OneWay
import Complexity.Languages.Probabilistic.Notation

import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Tactic.PPT

/-!
# The hashed parity inverter as a PPT word program

The reduction samples one saved predictor tape, a hash length, a matrix, a guessed digest, and
decoder masks. It then invokes the shared word decoder with the public fields and coins captured
by its callback. All sampling uses fair bits, with a fixed polynomial bound for every input.

The coin budget uses the actual framed input encoding: the unary security parameter contributes
`2 * n + 1` cells and the parity query another `n`. All public fields and delimiters are charged.
The saved evaluator returns a Boolean directly, without decoding arbitrary output words.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.HashPair.wordInverter`: the functional saved-coin reduction.
* `Cslib.Crypto.Pseudoentropy.HashPair.fixedPredictor`: one finite deterministic predictor.

## Main results

* `Cslib.Crypto.Pseudoentropy.HashPair.isPPT_wordInverter`: strict uniform PPT.
* `Cslib.Crypto.Pseudoentropy.HashPair.wordInverter_eval`: the exact finite/list law.
* `Cslib.Crypto.Pseudoentropy.HashPair.word_prediction_entropy_le`: the complete reduction bound.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 4, Lemma 4.
  `HashReduction` supplies the finite bound for our public matrix family and enlarged dyadic
  range. This module implements its inverter using the word and saved-coin interfaces.

Adapted from Crypto/Computational/Pseudoentropy/WordReduction.lean on the cslib `crypto` branch
at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed saved seeds and the tidy TM calculus.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.HashPair

open ProbComp Probability BitString GoldreichLevin Turing.MultiTapeTM

/-- One polynomial tape budget covers all digest lengths and parity queries for an image. -/
def coinBudget (c d n imageLength : ℕ) : ℕ :=
  c * (2 * imageLength + 2 * (hashCount n * n) + 4 * hashCount n + 3 * n + 8) ^ d

/-- The shared tape budget is efficient in the parameter and image length. -/
@[fun_prop]
theorem computableInPolyTime_coinBudget {α : Type} {encode : α ↪ List Bool}
    {parameter length : α → ℕ} (c d : ℕ)
    (hparameter : ComputableInPolyTime parameter encode encUnary)
    (hlength : ComputableInPolyTime length encode encUnary) :
    ComputableInPolyTime (fun a => coinBudget c d (parameter a) (length a))
      encode encUnary := by
  unfold coinBudget
  fun_prop

/-- Call the saved-coin predictor on the complete public observation. -/
def predictWithCoins (evaluate : (ℕ × List Bool) → List Bool → Bool) (n : ℕ)
    (image : List Bool) (index : ℕ) (matrix digest coins query : List Bool) : Bool :=
  evaluate (n, wordObservation image index matrix digest query) coins

/-- Captured public fields and coins use their ordinary efficiency certificates. The typed
callback has a uniformly polynomial bound on every supplied input, not only sampled words. -/
@[fun_prop]
theorem computableInPolyTime_predictWithCoins {α : Type} {encode : α ↪ List Bool}
    {evaluate : (ℕ × List Bool) → List Bool → Bool} {parameter index : α → ℕ}
    {image matrix digest coins query : α → List Bool}
    (hevaluate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (hparameter : ComputableInPolyTime parameter encode encUnary)
    (himage : ComputableInPolyTime image encode encBits)
    (hindex : ComputableInPolyTime index encode encUnary)
    (hmatrix : ComputableInPolyTime matrix encode encBits)
    (hdigest : ComputableInPolyTime digest encode encBits)
    (hcoins : ComputableInPolyTime coins encode encBits)
    (hquery : ComputableInPolyTime query encode encBits) :
    ComputableInPolyTime (fun a => predictWithCoins evaluate (parameter a) (image a)
      (index a) (matrix a) (digest a) (coins a) (query a)) encode encBool := by
  unfold predictWithCoins
  fun_prop

/-- Guess the unknown hash value and decode, using the same predictor coins for every query. -/
noncomputable def wordInverter (f : List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d degree : ℕ) : Inverter := fun n image => do
  let coins ← sampleList (coinBudget c d n image.length)
  let index ← sampleDyadicIndex (n + 6)
  let matrix ← sampleList (hashCount n * n)
  let digest ← sampleList (index + 1)
  let masks ← sampleList (maskCount n (precision degree n) * n)
  return wordDecode f (predictWithCoins evaluate n image index matrix digest coins)
    degree n image masks

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The complete inverter is one strict PPT program for every parameter and image. -/
@[program_certificate]
theorem isPPT_wordInverter {f : List Bool → List Bool}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (hevaluate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (c d degree : ℕ) : IsPPT encBits (wordInverter f evaluate c d degree) := by
  have hf := hf.tidy
  have hevaluate := hevaluate.tidy
  have hhash : ComputableTidilyInPolyTime hashCount encUnary encUnary :=
    (computableInPolyTime_hashCount (.of_tidy (by fun_prop))).tidy
  have hbudget : ComputableTidilyInPolyTime
      (fun a : ℕ × List Bool => coinBudget c d a.1 a.2.length)
      (encPair encUnary encBits) encUnary :=
    (computableInPolyTime_coinBudget c d (.of_tidy (by fun_prop))
      (.of_tidy (by fun_prop))).tidy
  have hdecode {β : Type} {encode : β ↪ List Bool}
      {predictor : β → List Bool → Bool} {dimension : β → ℕ} {image masks : β → List Bool}
      (hpredictor : ComputableTidilyInPolyTime (fun p : β × List Bool => predictor p.1 p.2)
        (encPair encode encBits) encBool)
      (hdimension : ComputableTidilyInPolyTime dimension encode encUnary)
      (himage : ComputableTidilyInPolyTime image encode encBits)
      (hmasks : ComputableTidilyInPolyTime masks encode encBits) :
      ComputableTidilyInPolyTime (fun a => wordDecode f (predictor a) degree (dimension a)
        (image a) (masks a)) encode encBits :=
    (polyTime_wordDecode degree (.of_tidy hf) (.of_tidy hpredictor)
      (.of_tidy hdimension) (.of_tidy himage) (.of_tidy hmasks)).tidy
  unfold wordInverter predictWithCoins
  fun_prop

/-- The tape budget covers every well-formed public observation at this dimension. -/
theorem observation_coinBudget_le (c d n : ℕ) (image : List Bool)
    (index : Fin (hashCount n)) (matrix : BitString (hashCount n * n))
    (digest : BitString (index.val + 1)) (query : BitString n) :
    c * ((encPair encUnary encBits (n, wordObservation image index.val (List.ofFn matrix)
      (List.ofFn digest) (List.ofFn query))).length + 1) ^ d ≤
        coinBudget c d n image.length := by
  unfold coinBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [wordObservation, length_encPair, encBits_apply, encUnary_apply, List.length_replicate,
    List.length_ofFn]
  have := index.isLt
  lia

/-- A common finite tape turns the word evaluator into a deterministic matrix predictor.
The finite image type is represented injectively when relating its inversion experiment. -/
def fixedPredictor {Image : Type*} (encodeImage : Image → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d n imageLength : ℕ)
    (coins : BitString (coinBudget c d n imageLength)) :
    MatrixPredictor n (hashCount n) Image := fun image index rows digest query =>
  predictWithCoins evaluate n (encodeImage image) index.val
    (List.ofFn ((blocksEquiv (m := hashCount n) (k := n)).symm rows))
    (List.ofFn digest) (List.ofFn coins) (List.ofFn query)

/-- Padding the saved tape to the common budget preserves every individual prediction law. -/
theorem fixedPredictor_distribution {Image : Type*} (encodeImage : Image → List Bool)
    (adversary : Distinguisher) (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d : ℕ)
    (hrealize : ∀ n input budget,
      c * ((encPair encUnary encBits (n, input)).length + 1) ^ d ≤ budget →
      ProbComp.eval (adversary n input) = (uniformList budget).map
        (evaluate (n, input)))
    (n imageLength : ℕ) (image : Image) (hlength : (encodeImage image).length = imageLength)
    (index : Fin (hashCount n)) (rows : Fin (hashCount n) → BitString n)
    (digest : BitString (index.val + 1)) (query : BitString n) :
    (PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))).map
        (fun coins => fixedPredictor encodeImage evaluate c d n imageLength coins
          image index rows digest query) =
      ProbComp.eval (adversary n (wordObservation (encodeImage image) index.val
        (List.ofFn ((blocksEquiv (m := hashCount n) (k := n)).symm rows))
        (List.ofFn digest) (List.ofFn query))) := by
  have hbudget := observation_coinBudget_le c d n (encodeImage image) index
    ((blocksEquiv (m := hashCount n) (k := n)).symm rows) digest query
  rw [hlength] at hbudget
  rw [hrealize _ _ _ hbudget]
  simp only [uniformList, PMF.map_comp, Function.comp_def, fixedPredictor, predictWithCoins]

/-- The word inverter agrees exactly with the finite inverter after encoding its output.
Only the image representation and its fixed width enter this statement. -/
theorem wordInverter_eval {n imageLength : ℕ} {Image : Type*} [DecidableEq Image]
    (f : List Bool → List Bool) (finiteFunction : BitString n → Image)
    (encodeImage : Image ↪ List Bool)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d degree : ℕ) (image : Image)
    (hlength : (encodeImage image).length = imageLength) :
    ProbComp.eval (wordInverter f evaluate c d degree n (encodeImage image)) =
      (do
        let coins ← PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))
        matrixInverter finiteFunction (fixedPredictor encodeImage evaluate c d n imageLength coins)
          (precision degree n) image).map List.ofFn := by
  have hindex : ProbComp.eval (sampleDyadicIndex (n + 6)) =
      (PMF.uniformOfFintype (Fin (hashCount n))).map Fin.val := eval_sampleDyadicIndex (n + 6)
  have hmatrix : uniformList (hashCount n * n) =
      (PMF.uniformOfFintype (Fin (hashCount n) → BitString n)).map
        (fun rows => List.ofFn ((blocksEquiv (m := hashCount n) (k := n)).symm rows)) := by
    rw [uniformList,
      ← PMF.uniformOfFintype_map_equiv (blocksEquiv (m := hashCount n) (k := n)).symm, PMF.map_comp]
    rfl
  have hfunction : (fun bits => f (List.ofFn bits)) = encodeImage ∘ finiteFunction :=
    funext hf
  have hdecode (predictor : List Bool → Bool) :
      (uniformList (maskCount n (precision degree n) * n)).bind
        (fun masks => PMF.pure (wordDecode f predictor degree n (encodeImage image) masks)) =
      (invertFixed finiteFunction (fun query => predictor (List.ofFn query))
        (maskCount n (precision degree n)) image).map List.ofFn := by
    change (uniformList _).map (wordDecode f predictor degree n (encodeImage image)) = _
    rw [uniform_wordDecode, hfunction,
      invertFixed_comp_injective finiteFunction encodeImage encodeImage.injective]
  simp only [wordInverter, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleList, hindex, hlength]
  simp_rw [hdecode, hmatrix]
  simp only [uniformList, PMF.bind_map, PMF.map_bind,
    Function.comp_def, matrixInverter, guessInverter, PMF.monad_bind_eq_bind]
  rfl

/-- The complete prediction game agrees with the finite experiment with one independent saved
tape. Moving that tape outside the experiment does not change the predictor's distribution. -/
theorem eval_predictionGame {n imageLength : ℕ} {Image : Type*}
    (f : List Bool → List Bool) (finiteFunction : BitString n → Image)
    (encodeImage : Image → List Bool)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (hlength : ∀ image, (encodeImage image).length = imageLength)
    (adversary : Distinguisher) (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d : ℕ)
    (hrealize : ∀ n input budget,
      c * ((encPair encUnary encBits (n, input)).length + 1) ^ d ≤ budget →
      ProbComp.eval (adversary n input) = (uniformList budget).map
        (evaluate (n, input))) :
    ProbComp.eval (predictionGame (sample f) adversary n) =
      (do
        let coins ← PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))
        matrixPrediction finiteFunction (fixedPredictor encodeImage evaluate c d n imageLength
          coins)) := by
  simp only [predictionGame, ProbComp.eval_bind, eval_sample f finiteFunction encodeImage hf,
    ProbComp.eval_pure, joint, Seed, ← PMF.uniformOfFintype_prod, PMF.map_bind, PMF.bind_map,
    PMF.bind_bind, Function.comp_def]
  rw [← PMF.uniformOfFintype_map_equiv (blocksEquiv (m := hashCount n) (k := n)).symm]
  simp only [PMF.bind_map, Function.comp_def, encodeObservation, prefixHash,
    Equiv.apply_symm_apply]
  simp_rw [← fixedPredictor_distribution encodeImage adversary evaluate c d hrealize n
    imageLength _ (hlength _), PMF.bind_map]
  simp only [Function.comp_def, matrixPrediction, PMF.map, PMF.monad_bind_eq_bind]
  simp_rw [← PMF.bind_comm (PMF.uniformOfFintype (BitString (coinBudget c d n imageLength)))]
  congr 1
  funext coins
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext index
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext rows
  rw [PMF.bind_comm]

/-- The word one-wayness game is the finite inversion experiment under the same
image encoding. Success still means finding any preimage. -/
theorem eval_wordInversionGame {n imageLength : ℕ} {Image : Type*} [DecidableEq Image]
    (f : List Bool → List Bool) (finiteFunction : BitString n → Image)
    (encodeImage : Image ↪ List Bool)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (hlength : ∀ image, (encodeImage image).length = imageLength)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d degree : ℕ) :
    ProbComp.eval (inversionGame f (wordInverter f evaluate c d degree) n) =
      inversionExperiment finiteFunction (fun image => do
        let coins ← PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))
        matrixInverter finiteFunction
          (fixedPredictor encodeImage evaluate c d n imageLength coins)
          (precision degree n) image) := by
  simp only [inversionGame, ProbComp.eval_bind, eval_sampleList, ProbComp.eval_pure,
    uniformList, PMF.bind_map, Function.comp_def, hf]
  simp_rw [wordInverter_eval f finiteFunction encodeImage hf evaluate c d degree _ (hlength _)]
  simp only [inversionExperiment, PMF.monad_bind_eq_bind, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def, hf, beq_eq_decide, encodeImage.injective.eq_iff]

/-- Holenstein's entropy-versus-prediction bound for the executable word games. Every sampled
bit and decoder query is included in the inverter certified by `isPPT_wordInverter`. -/
theorem word_prediction_entropy_le {n imageLength : ℕ} {Image : Type*}
    [Finite Image]
    (f : List Bool → List Bool) (finiteFunction : BitString n → Image)
    (encodeImage : Image ↪ List Bool)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (hlength : ∀ image, (encodeImage image).length = imageLength)
    (adversary : Distinguisher) (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d : ℕ)
    (hrealize : ∀ n input budget,
      c * ((encPair encUnary encBits (n, input)).length + 1) ^ d ≤ budget →
      ProbComp.eval (adversary n input) = (uniformList budget).map
        (evaluate (n, input)))
    (degree : ℕ) (hp : 8 * hashCount n ≤ precision degree n) :
    2 * Pr[predictionGame (sample f) adversary n] - 1 +
        PMF.conditionalEntropy (joint (count := hashCount n) finiteFunction) ≤
      1 - 2 / (hashCount n : ℝ) + 128 * (dyadicSize (16 * hashCount n) : ℝ) ^ 2 *
        Pr[inversionGame f (wordInverter f evaluate c d degree) n] := by
  classical
  simp only [
    eval_predictionGame f finiteFunction encodeImage hf hlength adversary evaluate c d hrealize,
    eval_wordInversionGame f finiteFunction encodeImage hf hlength evaluate c d degree]
  exact matrixPrediction_entropy_le_of_coins finiteFunction (hashCount_ge n) _ _ _ hp

end Cslib.Crypto.Pseudoentropy.HashPair
