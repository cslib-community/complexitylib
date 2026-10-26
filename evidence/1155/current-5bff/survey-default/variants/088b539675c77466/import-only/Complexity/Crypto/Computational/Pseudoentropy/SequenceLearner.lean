/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Hybrid.SavedPrediction
public import Complexity.Crypto.Computational.Pseudoentropy.Learning
public import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Training
import Complexity.Languages.Probabilistic.Notation
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# A sequence learner for the boosting loop

Each boosting state defines a fresh soft mask. The learner samples saved coordinate predictors
using that mask, then validates them on fresh labeled examples. Stored descriptions contain the
sampled data and test coins; they do not recursively contain the state that generated them.
Their uniform size bound therefore justifies the loop's truncation on every execution.

The evaluator is obtained from the sequence test's strict PPT certificate. Its signed version
interprets the learner's orientation bit, and is also the evaluator used by subsequent rounds.

## Main definitions

* `parameters`: configure the loop from the density and distinguishing gap.
* `candidates`, `learn`, `predict`: save coordinate predictors, learn, and predict.
* `failureBound`: the common negligible sampling-error budget.

## Main results

* `isPPTOn_predict`: certify the complete adaptive reduction.
* `exists_evaluator`: discharge the replay law from one sequence-test certificate.
* `learn_goodPredictor_error`: a noticeable sequence gap satisfies the boosting loop contract.
* `failureBound_negligible`: the total failure bound is negligible for polynomial parameters.
* `predict_extracted_error`: turn a gap against every dense masked source into prediction bias.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the prediction reduction.
  [Holenstein2006].
* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2.
  [Holenstein2005].
  We use fresh soft masks and the clocked boosting implementation.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SequenceLearner

open Probability Probability.PMF BitString Boosting Turing.MultiTapeTM

open scoped NNReal

/-- Configure the loop at the learner's required correlation. The density denominator and
inverse distinguishing gap determine the rate; the supplied bound covers signed descriptions. -/
def parameters (confidence numerator densityBound inverseGap codeBound : ℕ) : Parameters :=
  ⟨confidence, numerator, densityBound, 2 * inverseGap * dyadicSize densityBound, codeBound⟩

/-- Polynomial-time numerical inputs construct the complete encoded loop parameters. -/
@[program_certificate]
theorem isPolyTime_parameters {α : Type} {input : α ↪ List Bool}
    {confidence numerator densityBound inverseGap codeBound : α → ℕ}
    (hconfidence : ComputableInPolyTime confidence input encUnary)
    (hnumerator : ComputableInPolyTime numerator input encUnary)
    (hdensity : ComputableInPolyTime densityBound input encUnary)
    (hgap : ComputableInPolyTime inverseGap input encUnary)
    (hbound : ComputableInPolyTime codeBound input encUnary) :
    ComputableInPolyTime (fun a =>
      parameters (confidence a) (numerator a) (densityBound a) (inverseGap a) (codeBound a))
      input Parameters.encoding := by
  unfold parameters
  fun_prop

/-- A positive density numerator and the configured rate meet the learner's correlation budget. -/
theorem parameters_gamma_le (confidence numerator densityBound inverseGap codeBound : ℕ)
    (hvalid : (parameters confidence numerator densityBound inverseGap codeBound).Valid)
    (hgap : 0 < inverseGap) :
    (parameters confidence numerator densityBound inverseGap codeBound).gamma ≤
      1 / (2 * inverseGap) := by
  let params := parameters confidence numerator densityBound inverseGap codeBound
  have hden : (0 : ℝ) < params.denominator := by exact_mod_cast params.denominator_pos
  have hrate : (0 : ℝ) < params.inverseRate := by exact_mod_cast params.inverseRate_pos
  have hnum : (1 : ℝ) ≤ numerator := by exact_mod_cast hvalid.1
  have hgap' : (0 : ℝ) < inverseGap := by exact_mod_cast hgap
  have hbudget : 2 * (inverseGap : ℝ) * params.denominator ≤ params.inverseRate := by
    exact_mod_cast (lt_dyadicSize (2 * inverseGap * dyadicSize densityBound)).le
  change params.gamma ≤ _
  apply (div_le_iff₀ hvalid.delta_pos).mpr
  change 1 / (params.inverseRate : ℝ) ≤ 1 / (2 * inverseGap) *
    (numerator / (params.denominator : ℝ))
  rw [one_div_mul_eq_div, div_div]
  apply (div_le_div_iff₀ hrate (mul_pos hden (mul_pos (by norm_num) hgap'))).mpr
  nlinarith

/-- Sample the current soft weight on a fresh labeled observation. -/
noncomputable def mask (evaluate : List Bool → List Bool → Bool)
    (params : Parameters) (state : State)
    (sample : List Bool × Bool) : ProbComp Bool :=
  sampleWeight params.rateBound 1 state.threshold (state.votes evaluate sample.1) sample.2

/-- Draw saved coordinate descriptions before receiving any challenge observation. -/
noncomputable def candidates (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (base : List Bool) (count c d width : ℕ) (params : Parameters) (state : State) :
    ProbComp (List Bool) :=
  SavedPrediction.sample encBits base
    (maskedSample source Prod.fst Prod.snd (mask evaluate params state)) source count c d width

/-- Learn a signed coordinate predictor against the state's soft mask. The evaluator supplied
here interprets unsigned descriptions; the loop uses `signedPredict evaluate`. -/
noncomputable def learn (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (base : List Bool) (count c d width inverseGap : ℕ) (params : Parameters) (state : State) :
    ProbComp (List Bool) :=
  Boosting.learn (candidates (signedPredict evaluate) source base count c d width params state)
    (fun code => weightedTrial source (mask (signedPredict evaluate) params state)
      (fun sample => pure (evaluate code sample.1 == sample.2))) params.confidence inverseGap

/-- Train with the sequence learner, then predict from the challenge's public observation. -/
noncomputable def predict (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (base : List Bool) (count c d width inverseGap : ℕ) (params : Parameters)
    (observation : List Bool) :
    ProbComp Bool := do
  let model ← Boosting.train (signedPredict evaluate) source
    (learn evaluate source base count c d width inverseGap params) params
  Boosting.predict (signedPredict evaluate) params.predictionGridBound model observation

section Efficiency

variable {α : Type} {input : α ↪ List Bool} {evaluate : List Bool → List Bool → Bool}
  {params : α → Parameters} {state : α → State}

/-- Masks compose the efficient evaluator with the stored state and a labeled sample. -/
theorem isPPTOn_mask {sample : α → List Bool × Bool}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hparams : ComputableInPolyTime params input Parameters.encoding)
    (hstate : ComputableInPolyTime state input State.encoding)
    (hsample : ComputableInPolyTime sample input (encPair encBits encBool)) :
    IsPPTOn input encBool (fun a => mask evaluate (params a) (state a) (sample a)) := by
  unfold mask
  fun_prop

attribute [program_certificate] isPPTOn_mask

/-- Drawing descriptions is strict PPT even on executions with inaccurate guards or learners. -/
theorem isPPTOn_candidates {source : α → ProbComp (List Bool × Bool)} {base : α → List Bool}
    {count width : α → ℕ} (c d : ℕ)
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hbase : ComputableInPolyTime base input encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hparams : ComputableInPolyTime params input Parameters.encoding)
    (hstate : ComputableInPolyTime state input State.encoding) :
    IsPPTOn input encBits (fun a =>
      candidates evaluate (source a) (base a) (count a) c d (width a) (params a) (state a)) := by
  unfold candidates
  fun_prop

attribute [program_certificate] isPPTOn_candidates

/-- The adaptive sequence learner is strict PPT in the complete stored state and source input. -/
theorem isPPTOn_learn {source : α → ProbComp (List Bool × Bool)} {base : α → List Bool}
    {count width inverseGap : α → ℕ} (c d : ℕ)
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hbase : ComputableInPolyTime base input encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hgap : ComputableInPolyTime inverseGap input encUnary)
    (hparams : ComputableInPolyTime params input Parameters.encoding)
    (hstate : ComputableInPolyTime state input State.encoding) :
    IsPPTOn input encBits (fun a =>
      learn evaluate (source a) (base a) (count a) c d (width a) (inverseGap a)
        (params a) (state a)) := by
  have hevaluate := hevaluate.tidy
  have hbase := hbase.tidy
  have hcount := hcount.tidy
  have hwidth := hwidth.tidy
  have hgap := hgap.tidy
  have hparams := hparams.tidy
  have hstate := hstate.tidy
  unfold learn
  fun_prop

attribute [program_certificate] isPPTOn_learn

/-- The complete reduction has one uniform strict PPT implementation. The client supplies
source and evaluator certificates and polynomial-time numerical parameters, not machine data. -/
theorem isPPTOn_predict {source : α → ProbComp (List Bool × Bool)}
    {base observation : α → List Bool}
    {count width inverseGap : α → ℕ} (c d : ℕ)
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hbase : ComputableInPolyTime base input encBits)
    (hobservation : ComputableInPolyTime observation input encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hgap : ComputableInPolyTime inverseGap input encUnary)
    (hparams : ComputableInPolyTime params input Parameters.encoding) :
    IsPPTOn input encBool (fun a =>
      predict evaluate (source a) (base a) (count a) c d (width a) (inverseGap a)
        (params a) (observation a)) := by
  unfold predict
  fun_prop

attribute [program_certificate] isPPTOn_predict

end Efficiency

/-- The mask used by the executable learner is exactly the analytic soft weight. -/
theorem mask_probability (evaluate : List Bool → List Bool → Bool)
    (params : Parameters) (state : State)
    (sample : List Bool × Bool) :
    Pr[mask evaluate params state sample] = weight params.rate
      (listVoteMargin (state.votes evaluate sample.1) sample.2 - state.threshold) := by
  simpa only [mask, Parameters.rate, Parameters.inverseRate,
    Nat.cast_one] using eval_sampleWeight_true params.rateBound 1 state.threshold
      (state.votes evaluate sample.1) sample.2

/-- The code bound depends on the source's output width, not the current state's size. -/
theorem candidates_length_le (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (base : List Bool) (count c d width : ℕ) (params : Parameters) (state : State)
    (hwidth : ∀ sample ∈ (ProbComp.eval source).support, sample.1.length ≤ width)
    {code : List Bool} (hcode : code ∈ (ProbComp.eval
      (candidates evaluate source base count c d width params state)).support) :
    code.length ≤ SavedPrediction.codeBound base.length count c d width := by
  apply SavedPrediction.length_sample_le encBits base _ source count c d width _ hwidth hcode
  intro sample hsample
  simp only [eval_maskedSample, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hsample
  obtain ⟨original, horiginal, bit, _, rfl⟩ := hsample
  exact hwidth original horiginal

/-- Orientation and empirical selection add at most one bit to a sampled description. -/
theorem learn_length_le (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (base : List Bool) (count c d width inverseGap : ℕ) (params : Parameters) (state : State)
    (hwidth : ∀ sample ∈ (ProbComp.eval source).support, sample.1.length ≤ width)
    {code : List Bool} (hcode : code ∈ (ProbComp.eval
      (learn evaluate source base count c d width inverseGap params state)).support) :
    code.length ≤ SavedPrediction.codeBound base.length count c d width + 1 :=
  Boosting.learn_length_le _ _ params.confidence inverseGap _
    (fun _ => candidates_length_le _ _ _ _ _ _ _ _ _ hwidth) hcode

/-- One certified sequence test gives a fixed evaluator for every parameter, source, and
boosting state. The challenge observation is supplied only after the description is sampled. -/
theorem exists_evaluator {Param : Type} {input : Param ↪ List Bool}
    {test : Param → List (List Bool × Bool) → ProbComp Bool}
    (htest : IsPPTOn (encPair input (encList (encPair encBits encBool)))
      encBool (fun pair => test pair.1 pair.2)) :
    ∃ (c d : ℕ) (evaluate : List Bool → List Bool → Bool),
      ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool ∧
      ∀ a {α : Type} (source : ProbComp α) (observe : α → List Bool) (truth : α → Bool)
          count width params state observation, observation.length ≤ width →
        ProbComp.eval ((fun code => evaluate code observation) <$>
          candidates (signedPredict evaluate) ((fun x => (observe x, truth x)) <$> source)
            (input a) count c d width params state) =
          ProbComp.eval (maskedSequencePredictor source observe truth
            (fun x => mask (signedPredict evaluate) params state (observe x, truth x))
            count (test a) observation) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := SavedPrediction.exists_evaluator htest
  refine ⟨c, d, evaluate, hefficient.tidy, ?_⟩
  intro a α source observe truth count width params state observation hwidth
  simpa only [candidates, maskedSequencePredictor, maskedSample, bind_map_left, Functor.map_map,
    Function.comp_def, encBits, Function.Embedding.refl_apply] using
      hrealize a (maskedSample ((fun x => (observe x, truth x)) <$> source) Prod.fst Prod.snd
        (mask (signedPredict evaluate) params state)) ((fun x => (observe x, truth x)) <$> source)
          count width observation hwidth

/-- A common bound for all sampled guards, candidate discovery, validation, and slope selection. -/
noncomputable def failureBound (params : Parameters) (inverseGap : ℕ) : ℝ≥0 :=
  ((params.clock * ((params.confidence + 1) * (4 * inverseGap) ^ 2 + 3) +
    dyadicSize params.predictionGridBound + 1 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ params.confidence

/-- Polynomial parameters and at least `n` confidence bits make the complete failure bound
negligible. The polynomial degree may depend on the fixed sequence distinguisher. -/
theorem failureBound_negligible {params : ℕ → Parameters} {inverseGap : ℕ → ℕ}
    (hconfidence : PolynomiallyBounded (fun n => (params n).confidence))
    (hdensity : PolynomiallyBounded (fun n => (params n).densityBound))
    (hrate : PolynomiallyBounded (fun n => (params n).rateBound))
    (hgap : PolynomiallyBounded inverseGap) (hbudget : ∀ n, n ≤ (params n).confidence) :
    Negligible (fun n => failureBound (params n) (inverseGap n)) := by
  have hdecay : Negligible (fun n => (1 / 2 : ℝ≥0) ^ (params n).confidence) := by
    apply negligible_of_le (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num))
    intro n
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hbudget n)
  apply hdecay.polynomiallyBounded_mul
  unfold Parameters.predictionGridBound Parameters.predictionInverseTolerance Parameters.clock
    Parameters.inverseRate Parameters.denominator
  fun_prop

open Filter in
/-- Eventually all sampling failures consume at most half the inverse-polynomial prediction
advantage. The threshold may depend on the fixed distinguisher and its polynomial parameters. -/
theorem failureBound_eventually_le {params : ℕ → Parameters} {inverseGap : ℕ → ℕ}
    (hconfidence : PolynomiallyBounded (fun n => (params n).confidence))
    (hdensity : PolynomiallyBounded (fun n => (params n).densityBound))
    (hrate : PolynomiallyBounded (fun n => (params n).rateBound))
    (hgap : PolynomiallyBounded inverseGap) (hbudget : ∀ n, n ≤ (params n).confidence) :
    ∀ᶠ n in atTop, (failureBound (params n) (inverseGap n) : ℝ) ≤
      1 / (2 * (params n).predictionInverseTolerance) := by
  have hfailure := failureBound_negligible hconfidence hdensity hrate hgap hbudget
  have htolerance : PolynomiallyBounded (fun n => 2 * (params n).predictionInverseTolerance) := by
    unfold Parameters.predictionInverseTolerance Parameters.inverseRate Parameters.denominator
    fun_prop
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    hfailure.eventually_le_inv_polynomial htolerance
      (fun n => Nat.mul_pos (by decide) (params n).predictionInverseTolerance_pos)

section Correctness

variable {α : Type} [Fintype α]

/-- A noticeable sequence gap supplies the actual loop contract. Both the sampled descriptions
and their orientations fit the declared code bound, so truncation preserves their predictions. -/
theorem learn_goodPredictor_error (source : ProbComp α) (observe : α → List Bool) (truth : α → Bool)
    (evaluate : List Bool → List Bool → Bool) (base : List Bool) (count c d width inverseGap : ℕ)
    (params : Parameters) (state : State) (test : List (List Bool × Bool) → ProbComp Bool)
    (hparams : params.Valid) (hgap : 0 < inverseGap)
    (hgamma : params.gamma ≤ 1 / (2 * inverseGap))
    (hwidth : ∀ value ∈ (ProbComp.eval source).support, (observe value).length ≤ width)
    (hbound : SavedPrediction.codeBound base.length count c d width + 1 ≤ params.codeBound)
    (hrealize : ∀ value ∈ (ProbComp.eval source).support,
      ProbComp.eval ((fun code => evaluate code (observe value)) <$>
        candidates (signedPredict evaluate) ((fun x => (observe x, truth x)) <$> source)
          base count c d width params state) =
        ProbComp.eval (maskedSequencePredictor source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))
          count test (observe value)))
    (hdistinguish : (dyadicSize count : ℝ) / inverseGap ≤
      |Pr[OracleComp.replicate count ((fun x => (observe x, truth x)) <$> source)
          >>= test] -
        Pr[OracleComp.replicate count (maskedSample source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))) >>= test]|) :
    ((ProbComp.eval (learn evaluate ((fun x => (observe x, truth x)) <$> source)
      base count c d width inverseGap params state)).toOuterMeasure
      {code | ¬ state.GoodPredictor (ProbComp.eval source)
        (fun code x => signedPredict evaluate code (observe x)) truth params code}).toReal ≤
      (((params.confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) *
        (1 / 2 : ℝ) ^ params.confidence := by
  let descriptions := candidates (signedPredict evaluate)
    ((fun x => (observe x, truth x)) <$> source) base count c d width params state
  let weights := fun x => mask (signedPredict evaluate) params state (observe x, truth x)
  have hsize : ∀ code ∈ (ProbComp.eval descriptions).support,
      code.length ≤ SavedPrediction.codeBound base.length count c d width := by
    apply candidates_length_le
    intro sample hsample
    simp only [ProbComp.eval_map, PMF.mem_support_map_iff] at hsample
    obtain ⟨value, hvalue, rfl⟩ := hsample
    exact hwidth value hvalue
  have hbias : (1 : ℝ) / inverseGap ≤ |Pr[descriptions >>= fun code =>
      weightedTrial source weights (fun x => pure (evaluate code (observe x) == truth x))] -
        1 / 2| := by
    have hcount : (0 : ℝ) < dyadicSize count := by exact_mod_cast dyadicSize_pos count
    rw [maskedSequence_validation_gap source observe truth weights count test descriptions
      evaluate hrealize, abs_mul, abs_of_pos hcount] at hdistinguish
    apply (mul_le_mul_iff_right₀ hcount).mp
    simpa only [mul_one_div] using hdistinguish
  have h := Boosting.learn_goodPredictor_error_pow descriptions source weights
    (fun code x => evaluate code (observe x)) truth state params hparams inverseGap _ hgap hgamma
    hsize hbound (fun x => mask_probability _ _ _ _) hbias
  have hsigned : signedPredict (fun code x => evaluate code (observe x)) =
      fun code x => signedPredict evaluate code (observe x) := rfl
  rw [hsigned] at h
  simpa only [learn, descriptions, weights, weightedTrial, bind_map_left] using h

/-- Distinguishing every dense masked sequence yields a predictor beating `delta / 2`, up to
the single explicit failure bound. The learner here is the executable saved-description program. -/
theorem predict_error (source : ProbComp α) (observe : α → List Bool) (truth : α → Bool)
    (evaluate : List Bool → List Bool → Bool) (base : List Bool) (count c d width inverseGap : ℕ)
    (params : Parameters) (test : List (List Bool × Bool) → ProbComp Bool)
    (hparams : params.Valid) (hgap : 0 < inverseGap)
    (hgamma : params.gamma ≤ 1 / (2 * inverseGap))
    (hwidth : ∀ value ∈ (ProbComp.eval source).support, (observe value).length ≤ width)
    (hbound : SavedPrediction.codeBound base.length count c d width + 1 ≤ params.codeBound)
    (hrealize : ∀ state value, value ∈ (ProbComp.eval source).support →
      ProbComp.eval ((fun code => evaluate code (observe value)) <$>
        candidates (signedPredict evaluate) ((fun x => (observe x, truth x)) <$> source)
          base count c d width params state) =
        ProbComp.eval (maskedSequencePredictor source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))
          count test (observe value)))
    (hdistinguish : ∀ state : State,
      params.delta ≤ density (ProbComp.eval source) params.rate
        (fun x => state.margin (fun code x => signedPredict evaluate code (observe x)) truth x -
          state.threshold) →
      (dyadicSize count : ℝ) / inverseGap ≤
        |Pr[OracleComp.replicate count ((fun x => (observe x, truth x)) <$> source)
            >>= test] -
          Pr[OracleComp.replicate count (maskedSample source observe truth
            (fun x => mask (signedPredict evaluate) params state (observe x, truth x))) >>=
              test]|) :
    (ProbComp.eval (do
      let x ← source
      (fun answer => answer == truth x) <$> predict evaluate
        ((fun x => (observe x, truth x)) <$> source) base count c d width inverseGap params
        (observe x)) false).toReal ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance +
        failureBound params inverseGap := by
  have h := Boosting.train_predict_error source observe truth (signedPredict evaluate)
    (learn evaluate ((fun x => (observe x, truth x)) <$> source)
      base count c d width inverseGap params) params hparams (by positivity)
    (fun state hdense => learn_goodPredictor_error source observe truth evaluate base
      count c d width inverseGap params state test hparams hgap hgamma hwidth hbound
        (hrealize state) (hdistinguish state hdense))
  have hbudget : params.delta / 2 - 1 / params.predictionInverseTolerance +
      params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence +
        (((params.confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) *
          (1 / 2 : ℝ) ^ params.confidence) +
      (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence =
        params.delta / 2 - 1 / params.predictionInverseTolerance +
          failureBound params inverseGap := by
    unfold failureBound
    push_cast
    ring
  rw [hbudget] at h
  simpa only [predict, ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind] using h

/-- Extraction error is the only additional loss when the complete reduction starts from a
test of hashed labels. The statistical premise is needed only at dense boosting states. -/
theorem predict_extracted_error {Seed Output : Type}
    (source : ProbComp α) (observe : α → List Bool) (truth : α → Bool)
    (evaluate : List Bool → List Bool → Bool) (base : List Bool) (count c d width inverseGap : ℕ)
    (params : Parameters) (seed : ProbComp Seed) (hash : Seed → List Bool → Output)
    (test : List (List Bool) × Seed × Output → ProbComp Bool)
    (ideal : PMF (List (List Bool) × Seed × Output)) {ε : ℝ}
    (hparams : params.Valid) (hgap : 0 < inverseGap)
    (hgamma : params.gamma ≤ 1 / (2 * inverseGap))
    (hwidth : ∀ value ∈ (ProbComp.eval source).support, (observe value).length ≤ width)
    (hbound : SavedPrediction.codeBound base.length count c d width + 1 ≤ params.codeBound)
    (hrealize : ∀ state value, value ∈ (ProbComp.eval source).support →
      ProbComp.eval ((fun code => evaluate code (observe value)) <$>
        candidates (signedPredict evaluate) ((fun x => (observe x, truth x)) <$> source)
          base count c d width params state) =
        ProbComp.eval (maskedSequencePredictor source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))
          count (fun samples => extractLabels seed hash samples >>= test) (observe value)))
    (hclose : ∀ state : State,
      params.delta ≤ density (ProbComp.eval source) params.rate
        (fun x => state.margin (fun code x => signedPredict evaluate code (observe x)) truth x -
          state.threshold) →
      (Game.advantage
        ((ProbComp.eval (OracleComp.replicate count (maskedSample source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))) >>=
            extractLabels seed hash)).bind (fun output => ProbComp.eval (test output)))
        (ideal.bind (fun output => ProbComp.eval (test output))) : ℝ) ≤ ε)
    (hdistinguish : (dyadicSize count : ℝ) / inverseGap + ε ≤
      (Game.advantage (ProbComp.eval (do
        let samples ← OracleComp.replicate count ((fun x => (observe x, truth x)) <$> source)
        let result ← extractLabels seed hash samples
        test result))
        (ideal.bind (fun output => ProbComp.eval (test output))) : ℝ)) :
    (ProbComp.eval (do
      let x ← source
      (fun answer => answer == truth x) <$> predict evaluate
        ((fun x => (observe x, truth x)) <$> source) base count c d width inverseGap params
        (observe x)) false).toReal ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance +
        failureBound params inverseGap := by
  apply predict_error source observe truth evaluate base count c d width inverseGap params
    (fun samples => extractLabels seed hash samples >>= test)
    hparams hgap hgamma hwidth hbound hrealize
  intro state hdense
  have h := extractLabels_sequence_gap ((fun x => (observe x, truth x)) <$> source)
    (maskedSample source observe truth
      (fun x => mask (signedPredict evaluate) params state (observe x, truth x)))
    count seed hash test ideal (hclose state hdense)
  have hgap' := (le_sub_iff_add_le.mpr hdistinguish).trans h
  simpa only [Game.coe_advantage, Game.coe_succProbability] using hgap'

end Correctness

end Cslib.Crypto.Pseudoentropy.SequenceLearner
