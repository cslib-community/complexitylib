/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.HashReduction
public import CslibFrontier.Crypto.Computational.Pseudoentropy.Basic
public import CslibFrontier.Crypto.Computational.GoldreichLevin.WordDecoder
public import CslibFrontier.Crypto.Computational.OneWay
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Notation

import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT

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

* `Cslib.Crypto.Pseudoentropy.HashPair.isPPTOn_wordInverter`: strict uniform PPT, with the
  evaluator, parameter and image computed from an arbitrary input.
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

/-- Captured public fields and coins use their ordinary efficiency certificates. The evaluator may
itself depend on the captured input, for example on an advice word. The typed callback has a
uniformly polynomial bound on every supplied input, not only sampled words. -/
@[fun_prop]
theorem computableInPolyTime_predictWithCoins {α : Type} {encode : α ↪ List Bool}
    {evaluate : α → (ℕ × List Bool) → List Bool → Bool} {parameter index : α → ℕ}
    {image matrix digest coins query : α → List Bool}
    (hevaluate : ComputableInPolyTime (fun ((a, observation), tape) => evaluate a observation tape)
      (encPair (encPair encode (encPair encUnary encBits)) encBits) encBool)
    (hparameter : ComputableInPolyTime parameter encode encUnary)
    (himage : ComputableInPolyTime image encode encBits)
    (hindex : ComputableInPolyTime index encode encUnary)
    (hmatrix : ComputableInPolyTime matrix encode encBits)
    (hdigest : ComputableInPolyTime digest encode encBits)
    (hcoins : ComputableInPolyTime coins encode encBits)
    (hquery : ComputableInPolyTime query encode encBits) :
    ComputableInPolyTime (fun a => predictWithCoins (evaluate a) (parameter a) (image a)
      (index a) (matrix a) (digest a) (coins a) (query a)) encode encBool := by
  unfold predictWithCoins
  have harg : ComputableInPolyTime (fun a => ((a, (parameter a, wordObservation (image a)
      (index a) (matrix a) (digest a) (query a))), coins a)) encode
      (encPair (encPair encode (encPair encUnary encBits)) encBits) :=
    ((ComputableInPolyTime.of_eq fun _ => rfl).prod
      (hparameter.prod (by fun_prop))).prod hcoins
  exact hevaluate.comp harg

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

/-- **The inverter with a captured evaluator** is one strict PPT program on any input type: the
evaluator, parameter and image may all be computed from the input, which may carry an advice
word. -/
@[program_certificate]
theorem isPPTOn_wordInverter {α : Type} {input : α ↪ List Bool} {f : List Bool → List Bool}
    {evaluate : α → (ℕ × List Bool) → List Bool → Bool} {parameter : α → ℕ}
    {image : α → List Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (hevaluate : ComputableInPolyTime (fun ((a, observation), tape) => evaluate a observation tape)
      (encPair (encPair input (encPair encUnary encBits)) encBits) encBool)
    (hparameter : ComputableInPolyTime parameter input encUnary)
    (himage : ComputableInPolyTime image input encBits) (c d degree : ℕ) :
    IsPPTOn input encBits
      (fun a => wordInverter f (evaluate a) c d degree (parameter a) (image a)) := by
  -- The five sampled values (coins, index, matrix, digest, masks) are kept alongside the input.
  let e₅ := encPair (encPair (encPair (encPair (encPair input encBits) encUnary) encBits) encBits)
    encBits
  have hhash : ComputableInPolyTime hashCount encUnary encUnary :=
    computableInPolyTime_hashCount (by fun_prop)
  have hinput : ComputableInPolyTime
      (fun q : ((((α × List Bool) × ℕ) × List Bool) × List Bool) × List Bool => q.1.1.1.1.1)
      e₅ input := by fun_prop
  have hpredictor : ComputableInPolyTime
      (fun p : (((((α × List Bool) × ℕ) × List Bool) × List Bool) × List Bool) × List Bool =>
        predictWithCoins (evaluate p.1.1.1.1.1.1) (parameter p.1.1.1.1.1.1)
          (image p.1.1.1.1.1.1) p.1.1.1.1.2 p.1.1.1.2 p.1.1.2 p.1.1.1.1.1.2 p.2)
      (encPair e₅ encBits) encBool := by
    have hevaluate' : ComputableInPolyTime
        (fun ((p, observation), tape) => evaluate p.1.1.1.1.1.1 observation tape :
          ((((((((α × List Bool) × ℕ) × List Bool) × List Bool) × List Bool) × List Bool) ×
            (ℕ × List Bool)) × List Bool) → Bool)
        (encPair (encPair (encPair e₅ encBits) (encPair encUnary encBits)) encBits) encBool :=
      hevaluate.comp (show ComputableInPolyTime
        (fun ((p, observation), tape) => ((p.1.1.1.1.1.1, observation), tape) :
          ((((((((α × List Bool) × ℕ) × List Bool) × List Bool) × List Bool) × List Bool) ×
            (ℕ × List Bool)) × List Bool) → (α × (ℕ × List Bool)) × List Bool)
        (encPair (encPair (encPair e₅ encBits) (encPair encUnary encBits)) encBits)
        (encPair (encPair input (encPair encUnary encBits)) encBits) by fun_prop)
    exact computableInPolyTime_predictWithCoins hevaluate' (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hdecode : ComputableInPolyTime
      (fun q : ((((α × List Bool) × ℕ) × List Bool) × List Bool) × List Bool =>
        wordDecode f (predictWithCoins (evaluate q.1.1.1.1.1) (parameter q.1.1.1.1.1)
          (image q.1.1.1.1.1) q.1.1.1.2 q.1.1.2 q.1.2 q.1.1.1.1.2) degree
          (parameter q.1.1.1.1.1) (image q.1.1.1.1.1) q.2) e₅ encBits :=
    polyTime_wordDecode degree hf hpredictor (hparameter.comp hinput) (himage.comp hinput)
      (ComputableInPolyTime.snd _ _)
  unfold wordInverter
  refine IsPPTOn.bind_with (left := encBits)
    (isPPTOn_sampleList.preprocess (computableInPolyTime_coinBudget c d hparameter
      (by fun_prop))) ?_
  refine IsPPTOn.bind_with (left := encUnary) (isPPTOn_sampleDyadicIndex (by fun_prop)) ?_
  refine IsPPTOn.bind_with (left := encBits) (isPPTOn_sampleList.preprocess (by fun_prop)) ?_
  refine IsPPTOn.bind_with (left := encBits) (isPPTOn_sampleList.preprocess (by fun_prop)) ?_
  refine IsPPTOn.bind_with (left := encBits) (isPPTOn_sampleList.preprocess (by fun_prop)) ?_
  exact hdecode.isPPTOn

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
  simp only [pmf_norm, uniformList, matrixInverter, guessInverter]
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
  simp only [pmf_norm, predictionGame, predictionExperiment,
    eval_sample f finiteFunction encodeImage hf, joint, Seed, ← PMF.uniformOfFintype_prod]
  rw [← PMF.uniformOfFintype_map_equiv (blocksEquiv (m := hashCount n) (k := n)).symm]
  simp only [PMF.bind_map, Function.comp_def, encodeObservation, prefixHash,
    Equiv.apply_symm_apply]
  simp_rw [← fixedPredictor_distribution encodeImage adversary evaluate c d hrealize n
    imageLength _ (hlength _), PMF.bind_map]
  simp only [Function.comp_def, matrixPrediction, PMF.map, PMF.monad_bind_eq_bind]
  pmf_swap

/-- The word one-wayness game is the finite inversion experiment under the same
image encoding. Success still means finding any preimage. -/
theorem eval_wordInversionGame {n imageLength : ℕ} {Image : Type*} [DecidableEq Image]
    (f : List Bool → List Bool) (finiteFunction : BitString n → Image)
    (encodeImage : Image ↪ List Bool)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (hlength : ∀ image, (encodeImage image).length = imageLength)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d degree : ℕ) :
    ProbComp.eval (inversionGame f (wordInverter f evaluate c d degree) n) =
      inversionExperiment (PMF.uniformOfFintype _) finiteFunction (fun image => do
        let coins ← PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))
        matrixInverter finiteFunction
          (fixedPredictor encodeImage evaluate c d n imageLength coins)
          (precision degree n) image) := by
  simp only [pmf_norm, inversionGame, inversionExperiment, eval_sampleList, uniformList, hf]
  simp_rw [wordInverter_eval f finiteFunction encodeImage hf evaluate c d degree _ (hlength _)]
  simp only [pmf_norm, PMF.map, hf, beq_eq_decide, encodeImage.injective.eq_iff]

/-- Holenstein's entropy-versus-prediction bound for the executable word games. Every sampled
bit and decoder query is included in the inverter certified by `isPPTOn_wordInverter`. -/
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
