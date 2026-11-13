/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Computational.Nonuniform.Advice
public import CslibFrontier.Crypto.Game.Inversion
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Samplable pseudoentropy pairs

A pair consists of a public observation and a hidden bit. The observation has a finite type
at each parameter and an injective word encoding, so its conditional entropy is unambiguous.
A strict PPT sampler realizes the joint law exactly.

`SamplablePair.HasGap` says that every uniform PPT predictor, playing
`Cslib.Crypto.predictionExperiment` on a draw `(x, b)` of the pair, eventually has signed
correlation at most `1 - H(b | x) - gap`. This is the entropy threshold used in the OWF-to-PRG
construction; merely being hard to predict is not sufficient.

Predictors are typed: a `SamplablePair.Predictor` reads the security parameter and an observation
of `pair.Observation n`. Encodings appear only in `SamplablePair.Predictor.IsPPT`, whose machine
reads `(1ⁿ, encode n x)`.

`SamplablePair.HasGapWithAdvice` gives every predictor an advice word from a fixed family. The
extraction and generator theorems built on this module are stated relative to such a family; their
uniform cases follow at empty advice from `hasGap_iff_hasGapWithAdvice_nil` and
`computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil`.
`SamplablePair.hasGapWithAdvice_iff_word` restates the advised gap for word predictors on
`encAdvisedInput` in the word game `predictionGame`, the form used by the word-level extraction
pipeline. Its machines read the same words as the typed ones (`encAdvisedPredictorInput`).

This interface records the joint law and its sampler. The shared saved-coin interface exposes a
strict PPT sampler's fair-bit tape as a uniform seed, including unused randomness.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.SamplablePair`: a finite joint law with a uniform strict PPT sampler.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.Predictor`,
  `Cslib.Crypto.Pseudoentropy.SamplablePair.AdvisedPredictor`: typed predictors and their
  `IsPPT` predicates.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap`: the conditional-entropy prediction threshold.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGapWithAdvice`: the same threshold against
  predictors given one fixed advice family.
* `Cslib.Crypto.Pseudoentropy.predictionGame`: the word prediction game of a word sampler.
* `Cslib.Crypto.Pseudoentropy.encLabeledSamples`: the encoding of a list of labeled samples.

## Main results

* `Cslib.Crypto.Pseudoentropy.isPPTOn_predictionGame`: the word prediction game is strict PPT.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.eval_latentSample`: recover the exact latent joint law.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.hasGapWithAdvice_iff_word`: the advised gap is the
  same assumption against word predictors in the word game.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.hasGap_iff_hasGapWithAdvice_nil`: the uniform gap is
  the empty-advice case.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGapWithAdvice.eventually_error_ge`,
  `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_error_ge`: prediction error bounds.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGapWithAdvice.eventually_entropy_add_gap_le_one`,
  `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_entropy_add_gap_le_one`:
  the threshold forced by an independent fair-bit predictor.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Definitions 3 and 4. We use a sampler presentation and uniform
  strict PPT predictors. Signed correlation is twice success probability minus one.

Adapted from Crypto/Computational/Pseudoentropy/Basic.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared nonnegative game API and tidy machine
certificates. Existence of a pair with a positive gap is a separate security theorem.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter Turing.MultiTapeTM

/-- The word prediction game: `Cslib.Crypto.predictionExperiment` on a word sampler of
observation words and hidden bits. -/
def predictionGame (sample : ℕ → ProbComp (List Bool × Bool))
    (adversary : Distinguisher) (n : ℕ) : ProbComp Bool :=
  predictionExperiment (sample n) Prod.fst Prod.snd (adversary n)

/-- The complete prediction experiment is strict PPT whenever the sampler and predictor are. -/
@[program_certificate]
theorem isPPTOn_predictionGame {sample : ℕ → ProbComp (List Bool × Bool)}
    (hsample : IsPPTOn encUnary (encPair encBits encBool) sample) {adversary : Distinguisher}
    (hadversary : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (predictionGame sample adversary) :=
  let e0 := encPair encBits encBool; let e1 := encPair encUnary e0
  let p0 := ComputableInPolyTime.fst encUnary e0; let p1 := ComputableInPolyTime.snd encUnary e0
  let hpred := hadversary.on.preprocess (p0.prod (p1.trans (.fst encBits encBool)))
  hsample.bind_with (hpred.bind_with ((ComputableInPolyTime.snd e1 encBool).beq
    (((ComputableInPolyTime.fst e1 encBool).trans p1).trans (.snd encBits encBool))).isPPTOn)

/-- The input fields every advised predictor reads before its observation: the security parameter
and the advice word. -/
structure AdvisedParameter where
  /-- The security parameter, given to machines in unary. -/
  parameter : ℕ
  /-- The advice word for this parameter. -/
  advice : List Bool

/-- The encoding of an advised parameter: `(1ⁿ, advice)`, as in `encAdvisedInput`. -/
enc_structure encAdvisedParameter : AdvisedParameter where
  parameter : encUnary, advice : encBits

/-- A finite joint law together with its exact strict PPT word sampler. -/
structure SamplablePair where
  /-- The public information available at each parameter. -/
  Observation : ℕ → Type
  /-- Its alphabet is finite, without requiring a computable enumeration. -/
  [finite : ∀ n, Finite (Observation n)]
  /-- Encoding preserves all the public information. -/
  encode : ∀ n, Observation n ↪ List Bool
  /-- The public observation and hidden bit. -/
  joint : ∀ n, PMF (Observation n × Bool)
  /-- A word-level sampler with the strict fair-coin realization certified below. -/
  sample : ℕ → ProbComp (List Bool × Bool)
  /-- Its complete running time is bounded by one polynomial. -/
  efficient : IsPPTOn encUnary (encPair encBits encBool) sample
  /-- The sampler realizes the finite joint law exactly. -/
  eval_sample : ∀ n, ProbComp.eval (sample n) =
    (joint n).map (fun pair => (encode n pair.1, pair.2))

attribute [instance] SamplablePair.finite

namespace SamplablePair

/-- Recover the latent draw by relabelling the existing sampler. This is a mathematical
program, with no efficiency claim for decoding arbitrary observation encodings. -/
noncomputable def latentSample (pair : SamplablePair) (n : ℕ) :
    ProbComp (pair.Observation n × Bool) :=
  letI : Nonempty (pair.Observation n × Bool) := ⟨(pair.joint n).support_nonempty.choose⟩
  Function.invFun (fun value : pair.Observation n × Bool => (pair.encode n value.1, value.2)) <$>
    pair.sample n

/-- The recovered sample has exactly the joint law, including its hidden label. -/
theorem eval_latentSample (pair : SamplablePair) (n : ℕ) :
    ProbComp.eval (pair.latentSample n) = pair.joint n := by
  let : Nonempty (pair.Observation n × Bool) := ⟨(pair.joint n).support_nonempty.choose⟩
  have hinj : Function.Injective (fun v : pair.Observation n × Bool => (pair.encode n v.1, v.2)) :=
    (pair.encode n).injective.prodMap Function.injective_id
  simp only [latentSample, ProbComp.eval_map, pair.eval_sample, PMF.map_comp,
    Function.invFun_comp hinj, PMF.map_id]

/-! ### Typed predictors -/

variable (pair : SamplablePair)

/-- The input of a uniform predictor: the security parameter and an observation. -/
structure PredictorInput where
  /-- The security parameter, given to machines in unary. -/
  parameter : ℕ
  /-- The observation at this parameter. -/
  observation : pair.Observation parameter

/-- The encoding of a predictor input: `(1ⁿ, encode n x)`. -/
enc_structure encPredictorInput (pair : SamplablePair) : PredictorInput pair where
  parameter : encUnary,
  observation : (pair.encode parameter) using (pair.encode parameter).injective

/-- The input of an advised predictor: the security parameter, the advice word and an
observation. -/
structure AdvisedPredictorInput extends AdvisedParameter where
  /-- The observation at this parameter. -/
  observation : pair.Observation parameter

/-- The encoding of an advised predictor input: `((1ⁿ, advice), encode n x)`, the layout of
`encAdvisedInput`. -/
enc_structure encAdvisedPredictorInput (pair : SamplablePair) : AdvisedPredictorInput pair where
  toAdvisedParameter : encAdvisedParameter,
  observation : (pair.encode toAdvisedParameter.parameter) using
    (pair.encode toAdvisedParameter.parameter).injective

/-- A uniform predictor: given the security parameter and an observation, guess the hidden bit.
`Predictor.IsPPT` states its efficiency on encodings. -/
abbrev Predictor : Type :=
  (n : ℕ) → pair.Observation n → ProbComp Bool

/-- An advised predictor: a predictor that also reads an advice word. `AdvisedPredictor.IsPPT`
states its efficiency on encodings. -/
abbrev AdvisedPredictor : Type :=
  (n : ℕ) → List Bool → pair.Observation n → ProbComp Bool

variable {pair}

/-- A predictor is PPT when one uniform strict PPT machine reads `encPredictorInput`. -/
def Predictor.IsPPT (predictor : pair.Predictor) : Prop :=
  IsPPTOn pair.encPredictorInput encBool fun x => predictor x.parameter x.observation

/-- An advised predictor is PPT when one uniform strict PPT machine reads
`encAdvisedPredictorInput`. -/
def AdvisedPredictor.IsPPT (predictor : pair.AdvisedPredictor) : Prop :=
  IsPPTOn pair.encAdvisedPredictorInput encBool fun x =>
    predictor x.parameter x.advice x.observation

/-- A uniform PPT predictor is a PPT advised predictor that ignores its advice. -/
theorem Predictor.IsPPT.dropAdvice {predictor : pair.Predictor} (h : predictor.IsPPT) :
    AdvisedPredictor.IsPPT (pair := pair) fun n _ x => predictor n x :=
  IsPPTOn.preprocess h (prepare := fun x : pair.AdvisedPredictorInput =>
    (⟨x.parameter, x.observation⟩ : pair.PredictorInput)) (by fun_prop)

/-- A PPT advised predictor run on empty advice is a uniform PPT predictor. -/
theorem AdvisedPredictor.IsPPT.nilAdvice {predictor : pair.AdvisedPredictor}
    (h : predictor.IsPPT) : Predictor.IsPPT (pair := pair) fun n x => predictor n [] x :=
  IsPPTOn.preprocess h (prepare := fun x : pair.PredictorInput =>
    (⟨⟨x.parameter, []⟩, x.observation⟩ : pair.AdvisedPredictorInput)) (by fun_prop)

/-! ### The prediction gap -/

/-- Every uniform PPT predictor stays below the conditional-entropy threshold by this gap: drawing
`(x, b)` from the pair and giving the predictor `x`, its signed correlation with `b` is eventually
at most `1 - H(b | x) - gap`. The threshold beyond which the inequality holds may depend on the
predictor. -/
def HasGap (pair : SamplablePair) (gap : ℕ → ℝ) : Prop :=
  ∀ predictor : pair.Predictor, predictor.IsPPT →
    ∀ᶠ n in atTop,
      2 * Pr[predictionExperiment (pair.latentSample n) Prod.fst Prod.snd (predictor n)] - 1 ≤
        1 - PMF.conditionalEntropy (pair.joint n) - gap n

/-- **The prediction gap relative to fixed advice**: every uniform strict PPT predictor that also
reads the advice word `advice n` stays below the conditional-entropy threshold by `gap`. The advice
family is not bounded here; its length is charged to the predictor's clock. With empty advice this
is `HasGap` (`hasGap_iff_hasGapWithAdvice_nil`). -/
def HasGapWithAdvice (pair : SamplablePair) (gap : ℕ → ℝ) (advice : ℕ → List Bool) : Prop :=
  ∀ predictor : pair.AdvisedPredictor, predictor.IsPPT →
    ∀ᶠ n in atTop,
      2 * Pr[predictionExperiment (pair.latentSample n) Prod.fst Prod.snd
          (predictor n (advice n))] - 1 ≤
        1 - PMF.conditionalEntropy (pair.joint n) - gap n

/-- The word prediction game on the pair's sampler is the prediction experiment on its latent
draw, with the predictor reading the observation's encoding. -/
theorem eval_predictionGame_sample (pair : SamplablePair) (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (predictionGame pair.sample adversary n) =
      ProbComp.eval (predictionExperiment (pair.latentSample n) Prod.fst Prod.snd
        fun x => adversary n (pair.encode n x)) := by
  simp only [pmf_norm, predictionGame, predictionExperiment, pair.eval_sample,
    pair.eval_latentSample]

/-- **`HasGapWithAdvice` is the word-level advised gap.** Quantifying over word predictors that
read `((1ⁿ, advice), encode n x)` with one uniform strict PPT machine on `encAdvisedInput`, in the
word game `predictionGame`, gives the same assumption as quantifying over typed advised predictors.
A typed predictor's machine reads exactly that layout; conversely, a word predictor is typed by
encoding its observation, and a typed one is a word predictor on that layout run on the encoded
observation (`IsPPTOn.exists_bool_factor`), since its output is a single bit. -/
theorem hasGapWithAdvice_iff_word {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} :
    pair.HasGapWithAdvice gap advice ↔
      ∀ adversary : (ℕ × List Bool) × List Bool → ProbComp Bool,
        IsPPTOn encAdvisedInput encBool adversary →
        ∀ᶠ n in atTop,
          2 * Pr[predictionGame pair.sample (fun n word => adversary ((n, advice n), word)) n] -
              1 ≤
            1 - PMF.conditionalEntropy (pair.joint n) - gap n := by
  constructor
  · intro h adversary hadversary
    have := h (fun n a x => adversary ((n, a), pair.encode n x))
      (hadversary.preprocess (input := pair.encAdvisedPredictorInput) (by fun_prop))
    simpa only [eval_predictionGame_sample] using this
  · intro h predictor hpredictor
    obtain ⟨W, hW, hWpredictor⟩ := hpredictor.exists_bool_factor (words := encAdvisedInput)
      (toWords := fun x : pair.AdvisedPredictorInput =>
        ((x.parameter, x.advice), pair.encode x.parameter x.observation)) fun _ => rfl
    obtain rfl : predictor = fun n a x => W ((n, a), pair.encode n x) :=
      funext₃ fun n a x => hWpredictor ⟨⟨n, a⟩, x⟩
    simpa only [eval_predictionGame_sample] using h W hW

/-- **The uniform gap is the empty-advice case.** A uniform predictor is an advice predictor that
ignores its advice, and an advice predictor run on empty advice is a uniform predictor. -/
theorem hasGap_iff_hasGapWithAdvice_nil {pair : SamplablePair} {gap : ℕ → ℝ} :
    pair.HasGap gap ↔ pair.HasGapWithAdvice gap (fun _ => []) :=
  ⟨fun h predictor hpredictor => h (fun n x => predictor n [] x) hpredictor.nilAdvice,
   fun h predictor hpredictor => h (fun n _ x => predictor n x) hpredictor.dropAdvice⟩

/-- A smaller requested gap follows from any larger proved gap, with the same advice. -/
theorem HasGapWithAdvice.mono {pair : SamplablePair} {gap smaller : ℕ → ℝ}
    {advice : ℕ → List Bool} (h : pair.HasGapWithAdvice gap advice)
    (hle : ∀ n, smaller n ≤ gap n) : pair.HasGapWithAdvice smaller advice :=
  fun predictor hPPT =>
    (h predictor hPPT).mono fun n hn => hn.trans (sub_le_sub_left (hle n) _)

/-- The pseudoentropy threshold relative to fixed advice equivalently lower-bounds each efficient
advised predictor's error. -/
theorem HasGapWithAdvice.eventually_error_ge {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hgap : pair.HasGapWithAdvice gap advice)
    (predictor : pair.AdvisedPredictor) (hefficient : predictor.IsPPT) :
    ∀ᶠ n in atTop, (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤
      (ProbComp.eval (predictionExperiment (pair.latentSample n) Prod.fst Prod.snd
        (predictor n (advice n))) false).toReal := by
  filter_upwards [hgap predictor hefficient] with n hn
  have hsum := PMF.toReal_true_add_toReal_false (ProbComp.eval
    (predictionExperiment (pair.latentSample n) Prod.fst Prod.snd (predictor n (advice n))))
  linarith only [hn, hsum]

/-- The pseudoentropy threshold equivalently lower-bounds each efficient predictor's error. -/
theorem HasGap.eventually_error_ge {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) (predictor : pair.Predictor) (hefficient : predictor.IsPPT) :
    ∀ᶠ n in atTop, (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤
      (ProbComp.eval (predictionExperiment (pair.latentSample n) Prod.fst Prod.snd
        (predictor n)) false).toReal :=
  (hasGap_iff_hasGapWithAdvice_nil.mp hgap).eventually_error_ge (fun n _ x => predictor n x)
    hefficient.dropAdvice

/-- A fair-bit predictor has zero correlation, so entropy plus the prediction gap relative to fixed
advice cannot eventually exceed one. -/
theorem HasGapWithAdvice.eventually_entropy_add_gap_le_one {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hgap : pair.HasGapWithAdvice gap advice) :
    ∀ᶠ n in atTop, PMF.conditionalEntropy (pair.joint n) + gap n ≤ 1 := by
  filter_upwards [hgap (fun _ _ _ => ProbComp.uniform Bool) (isPPTOn_uniform_bool _)] with n hn
  have hfair : Pr[predictionExperiment (pair.latentSample n) Prod.fst Prod.snd
      fun _ => ProbComp.uniform Bool] = 1 / 2 := by
    simp [predictionExperiment, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_apply,
      PMF.map_apply, PMF.uniformOfFintype_apply, ENNReal.tsum_mul_right, PMF.tsum_coe]
  linarith only [hn, hfair]

/-- A fair-bit predictor has zero correlation, so entropy plus the prediction gap cannot
eventually exceed one. -/
theorem HasGap.eventually_entropy_add_gap_le_one {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) :
    ∀ᶠ n in atTop, PMF.conditionalEntropy (pair.joint n) + gap n ≤ 1 :=
  (hasGap_iff_hasGapWithAdvice_nil.mp hgap).eventually_entropy_add_gap_le_one

/-- A smaller requested gap follows from any larger proved gap. -/
theorem HasGap.mono {pair : SamplablePair} {gap smaller : ℕ → ℝ} (h : pair.HasGap gap)
    (hle : ∀ n, smaller n ≤ gap n) : pair.HasGap smaller :=
  fun predictor hPPT =>
    (h predictor hPPT).mono fun n hn => hn.trans (sub_le_sub_left (hle n) _)

end SamplablePair

/-- A list of labeled samples `(x, b)`, such as repeated draws of `SamplablePair.sample`: each
sample is an observation word `x` paired with its label bit `b`, with `x` framed. The samples are
framed and concatenated in order. -/
abbrev encLabeledSamples : List (List Bool × Bool) ↪ List Bool :=
  encList (encPair encBits encBool)

end Cslib.Crypto.Pseudoentropy
