/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GoldreichLevin.WordDecoder
public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Computational.OneWay
import Complexity.Languages.Probabilistic.Notation
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Tactic.PPT

/-!
# The uniform Goldreich–Levin inverter

One functional program samples a sign, a saved predictor seed and independent mask bits, then
runs the certified word decoder. Its saved evaluator is typed: it receives the parameter and
auxiliary word directly and returns a Boolean. No raw output decoding is exposed to the caller.

The same seed is reused for every query at a given image. Its length accounts for the actual
pair encoding: an `n`-bit query appended to the image has encoded input length
`3 * n + image.length + 1`. Images may have arbitrary lengths. Every fixed precision degree
selects one uniform PPT inverter across all security parameters.

## Main definitions

* `coinBudget`: the predictor tape length for an arbitrary image and an `n`-bit query.
* `parityPredictionGame`: predict a uniform inner product given an image and a mask.
* `wordInverter`: the functional randomized inversion program.

## Main results

* `isPPT_wordInverter`: the complete inverter is uniformly PPT.
* `wordInverter_eval`, `eval_parityPredictionGame`: exact finite-game correspondences.
* `word_prediction_advantage_le`: the concrete reduction loss.
* `negligible_parityPrediction`: one-wayness implies negligible prediction bias.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [L. Trevisan, *CS276 Lecture 12: Goldreich–Levin*][Trevisan2009GL]

Adapted from Crypto/Computational/GoldreichLevin/WordReduction.lean on the cslib `crypto` branch
at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed saved seeds and the tidy TM calculus.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability BitString Turing.MultiTapeTM

/-- The saved tape covers the unary parameter, the whole image and an `n`-bit query. -/
def coinBudget (c d n imageLength : ℕ) : ℕ := c * (3 * n + imageLength + 2) ^ d

/-- Evaluate a parity query with the same saved private seed throughout the reduction. -/
def fixedPredictor (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d n : ℕ)
    (image : List Bool) (coins : BitString (coinBudget c d n image.length))
    (query : BitString n) : Bool :=
  evaluate (n, image ++ List.ofFn query) (List.ofFn coins)

/-- Predict a uniform inner product from an image and an independent uniform query. -/
noncomputable def parityPredictionGame (f : List Bool → List Bool) (adversary : Distinguisher)
    (n : ℕ) : ProbComp Bool := do
  let x ← BitString.sampleList n
  let query ← BitString.sampleList n
  let guess ← adversary n (f x ++ query)
  return guess == (x.zipWith Bool.and query).foldl Bool.xor false

/-- The prediction experiment composes sampling, the adversary and Boolean word operations. -/
@[program_certificate]
theorem isPPTOn_parityPredictionGame {f : List Bool → List Bool} {adversary : Distinguisher}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (parityPredictionGame f adversary) := by
  unfold parityPredictionGame
  ppt

/-- Sample one sign, one predictor seed and independent masks, then decode and check candidates. -/
noncomputable def wordInverter (f : List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d degree : ℕ) : Inverter := fun n image => do
  let flip ← ProbComp.uniform Bool
  let coins ← BitString.sampleList (coinBudget c d n image.length)
  let masks ← BitString.sampleList (maskCount n (precision degree n) * n)
  return wordDecode f (fun query => evaluate (n, image ++ query) coins ^^ flip)
    degree n image masks

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Every fixed degree gives one strict PPT inverter for all parameters and images. -/
@[program_certificate]
theorem isPPT_wordInverter {f : List Bool → List Bool}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (hevaluate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (c d degree : ℕ) : IsPPT encBits (wordInverter f evaluate c d degree) := by
  have hdecode : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × Bool) × List Bool) × List Bool =>
        wordDecode f
          (fun query => evaluate (p.1.1.1.1, p.1.1.1.2 ++ query) p.1.2 ^^ p.1.1.2)
          degree p.1.1.1.1 p.1.1.1.2 p.2)
      (encPair (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBits)
      encBits := by
    apply polyTime_wordDecode degree hf <;> fun_prop
  unfold wordInverter coinBudget
  ppt

/-- At every image length, the program realizes exactly the finite seeded inverter. -/
theorem wordInverter_eval (f : List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (c d degree n : ℕ) (image : List Bool) :
    ProbComp.eval (wordInverter f evaluate c d degree n image) =
      (invertSigned (fun bits => f (List.ofFn bits)) (fixedPredictor evaluate c d n)
        (fun image => PMF.uniformOfFintype (BitString (coinBudget c d n image.length)))
        (maskCount n (precision degree n)) image).map List.ofFn := by
  simp only [wordInverter, ProbComp.eval_bind, ProbComp.eval_uniform, BitString.eval_sampleList,
    ProbComp.eval_pure, invertSigned, invert, PMF.monad_bind_eq_bind, PMF.map_bind]
  congr 1
  funext flip
  rw [uniformList, PMF.bind_map]
  congr 1
  funext seed
  simpa only [PMF.map, fixedPredictor, Function.comp_def] using
    uniform_wordDecode f (fun query => evaluate (n, image ++ query) (List.ofFn seed) ^^ flip)
      degree n image

/-- Saved-seed evaluation has the right prediction law for images of any length. -/
theorem fixedPredictor_distribution (adversary : Distinguisher)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformList (c * ((encPair encUnary encBits (n, input)).length + 1) ^ d)).map
        (evaluate (n, input)))
    (n : ℕ) (image : List Bool) (query : BitString n) :
    (PMF.uniformOfFintype (BitString (coinBudget c d n image.length))).map
        (fun coins => fixedPredictor evaluate c d n image coins query) =
      ProbComp.eval (adversary n (image ++ List.ofFn query)) := by
  rw [hrealize]
  have hlen : (encPair encUnary encBits (n, image ++ List.ofFn query)).length + 1 =
      3 * n + image.length + 2 := by
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      List.length_append, List.length_ofFn]
    lia
  rw [hlen]
  simp only [uniformList, PMF.map_comp, Function.comp_def, coinBudget, fixedPredictor]
  rfl

/-- The prediction game is exactly the finite experiment with an image-dependent saved seed. -/
theorem eval_parityPredictionGame (f : List Bool → List Bool) (adversary : Distinguisher)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformList (c * ((encPair encUnary encBits (n, input)).length + 1) ^ d)).map
        (evaluate (n, input)))
    (n : ℕ) :
    ProbComp.eval (parityPredictionGame f adversary n) =
      predictionExperiment (fun bits => f (List.ofFn bits)) (fixedPredictor evaluate c d n)
        (fun image => PMF.uniformOfFintype (BitString (coinBudget c d n image.length))) := by
  simp only [parityPredictionGame, ProbComp.eval_bind, BitString.eval_sampleList,
    ProbComp.eval_pure, uniformList, PMF.bind_map, Function.comp_def,
    ← dotProduct_eq_foldl, predictionExperiment]
  congr 1
  funext x
  simp_rw [← fixedPredictor_distribution adversary evaluate c d hrealize,
    PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  rfl

/-- The standard any-preimage game agrees with the finite inversion experiment. -/
theorem eval_wordInversionGame (f : List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d degree n : ℕ) :
    ProbComp.eval (inversionGame f (wordInverter f evaluate c d degree) n) =
      inversionExperiment (fun bits => f (List.ofFn bits))
        (invertSigned (fun bits => f (List.ofFn bits)) (fixedPredictor evaluate c d n)
          (fun image => PMF.uniformOfFintype (BitString (coinBudget c d n image.length)))
          (maskCount n (precision degree n))) := by
  simp only [inversionGame, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
    uniformList, PMF.bind_map, Function.comp_def, inversionExperiment, wordInverter_eval,
    beq_eq_decide]
  rfl

/-- Prediction bias is at most the precision error plus eight times inversion success. -/
theorem word_prediction_advantage_le (f : List Bool → List Bool) (adversary : Distinguisher)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformList (c * ((encPair encUnary encBits (n, input)).length + 1) ^ d)).map
        (evaluate (n, input)))
    (degree n : ℕ) :
    |Pr[parityPredictionGame f adversary n] - 1 / 2| ≤
      1 / (precision degree n : ℝ) +
        8 * Pr[inversionGame f (wordInverter f evaluate c d degree) n] := by
  simp only [eval_parityPredictionGame f adversary evaluate c d hrealize,
    eval_wordInversionGame f]
  exact invertSigned_advantage_le _ _ _ _ (precision_pos degree n)

/-- No uniform PPT adversary predicts a masked inner product of a one-way input with
nonnegligible bias. Each precision degree selects one inverter for all lengths. -/
theorem negligible_parityPrediction {f : List Bool → List Bool} (hf : OneWay f)
    (adversary : Distinguisher) (hPPT : IsPPT encBool adversary) :
    Negligible (fun n => Game.guessingAdvantage
      (ProbComp.eval (parityPredictionGame f adversary n))) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := hPPT.on.exists_seeded_evaluator
  simp only [eval_parityPredictionGame f adversary evaluate c d
    (fun n input => hrealize (n, input))]
  apply negligible_prediction_of_negligible_inversion
  intro degree
  simpa only [eval_wordInversionGame f] using
    hf.inversion_negligible _ (isPPT_wordInverter hf.polyTime (.of_tidy hefficient) c d degree)

/-- One efficient typed evaluator witnesses the concrete reduction at every precision degree.
When `f` is efficient, `isPPT_wordInverter` certifies each resulting inverter. -/
theorem exists_word_reduction (f : List Bool → List Bool) (adversary : Distinguisher)
    (hPPT : IsPPT encBool adversary) :
    ∃ (c d : ℕ) (evaluate : (ℕ × List Bool) → List Bool → Bool),
      ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
        (encPair (encPair encUnary encBits) encBits) encBool ∧
      ∀ degree n, |Pr[parityPredictionGame f adversary n] - 1 / 2| ≤
        1 / (precision degree n : ℝ) +
          8 * Pr[inversionGame f (wordInverter f evaluate c d degree) n] := by
  have this : ∃ (c d : ℕ) (evaluate : (ℕ × List Bool) → List Bool → Bool),
    ComputableTidilyInPolyTime (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2) (encPair
    (encPair encUnary encBits) encBits) encBool ∧ ∀ degree n, |Pr[parityPredictionGame f
    adversary n] - 1 / 2| ≤ 1 / (precision degree n : ℝ) + 8 * Pr[inversionGame f (wordInverter f
    evaluate c d degree) n] := by
    obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := hPPT.on.exists_seeded_evaluator
    exact ⟨c, d, evaluate, hefficient, fun degree n =>
      word_prediction_advantage_le f adversary evaluate c d
        (fun n input => hrealize (n, input)) degree n⟩
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

end Cslib.Crypto.GoldreichLevin
