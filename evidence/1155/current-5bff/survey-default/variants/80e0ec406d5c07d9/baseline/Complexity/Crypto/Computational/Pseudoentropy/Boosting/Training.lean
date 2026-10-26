/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Selection
import Complexity.Probability.PMF.Event
import Complexity.Tactic.PPT

/-!
# Training and evaluating a boosted predictor

`train` runs the clocked loop and selects the final slope. Its result is the stored state paired
with a natural numerator. `predict` uses only this description and the public observation;
training labels are never supplied at prediction time.

The correctness bound adds the loop's guard and learner failures to the final selection failure.
The learner's correlation contract remains an explicit hypothesis. The efficiency certificates
compose the programming rules, independently of these probabilistic guarantees.

## Main definitions

* `finish`, `train`: select a final model after the clocked boosting loop.
* `predict`, `predictionError`: evaluate that model on public observations and measure its error.

## Main results

* `isPPTOn_train`, `isPPTOn_predict`: compositional training and prediction certificates.
* `train_sound`, `train_predict_error`: combine guard, learner and slope-selection failures.

## References

[Holenstein2005], Section 2.2, Lemma 2.4 and Claims 2.15–2.16. As in `Selection`, the final
predictor uses empirical selection over a finite slope grid.
Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Probability BitString Turing.MultiTapeTM

/-- Keep a stopped majority predictor, or select a slope from fresh labeled samples. -/
noncomputable def finish (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (params : Parameters) (state : State) : ProbComp (State × ℕ) :=
  if state.stopped then pure (state, 0)
  else (fun slope => (state, slope)) <$> selectSlope params.confidence
    params.predictionInverseTolerance params.predictionGridBound (withVotes evaluate source state)

/-- Train one predictor description using the clocked loop and uniform final selection. -/
noncomputable def train (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (learn : State → ProbComp (List Bool)) (params : Parameters) : ProbComp (State × ℕ) := do
  let state ← run evaluate source learn params
  finish evaluate source params state

/-- Evaluate a learned description on public information alone. The numerator is unused when
the majority stopping test succeeded. -/
noncomputable def predict (evaluate : List Bool → List Bool → Bool) (precision : ℕ)
    (model : State × ℕ) (observation : List Bool) : ProbComp Bool :=
  if model.1.stopped then pure (listStrictMajority (model.1.votes evaluate observation))
  else clippedPredict precision model.2 (model.1.votes evaluate observation)

section Efficiency

variable {α : Type} {input : α ↪ List Bool} {evaluate : List Bool → List Bool → Bool}

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Final selection composes the evaluator, source, stored state, and encoded parameters. -/
@[program_certificate]
theorem isPPTOn_finish {source : α → ProbComp (List Bool × Bool)} {params : α → Parameters}
    {state : α → State}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hstate : ComputableInPolyTime state input State.encoding)
    (hparams : ComputableInPolyTime params input Parameters.encoding) :
    IsPPTOn input (encPair State.encoding encUnary)
      (fun a => finish evaluate (source a) (params a) (state a)) := by
  have hevaluate := hevaluate.tidy
  have hstate := hstate.tidy
  have hparams := hparams.tidy
  unfold finish
  fun_prop

/-- Training is strict PPT on every execution, including guard and learner failures. -/
@[program_certificate]
theorem isPPTOn_train {source : α → ProbComp (List Bool × Bool)}
    {learn : α → State → ProbComp (List Bool)} {params : α → Parameters}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hlearn : IsPPTOn (encPair input State.encoding) encBits (fun pair => learn pair.1 pair.2))
    (hparams : ComputableInPolyTime params input Parameters.encoding) :
    IsPPTOn input (encPair State.encoding encUnary)
      (fun a => train evaluate (source a) (learn a) (params a)) := by
  unfold train
  ppt

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Applying a trained predictor requires only efficient observations and the stored description. -/
@[program_certificate]
theorem isPPTOn_predict {precision : α → ℕ} {model : α → State × ℕ}
    {observation : α → List Bool}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hprecision : ComputableInPolyTime precision input encUnary)
    (hmodel : ComputableInPolyTime model input (encPair State.encoding encUnary))
    (hobservation : ComputableInPolyTime observation input encBits) :
    IsPPTOn input encBool
      (fun a => predict evaluate (precision a) (model a) (observation a)) := by
  have hevaluate := hevaluate.tidy
  have hprecision := hprecision.tidy
  have hmodel := hmodel.tidy
  have hobservation := hobservation.tidy
  unfold predict
  ppt

end Efficiency

/-- Prediction error on a source. This semantic definition also permits infinite source types. -/
noncomputable def predictionError {α : Type*} (source : PMF α) (observe : α → List Bool)
    (truth : α → Bool) (evaluate : List Bool → List Bool → Bool)
    (precision : ℕ) (model : State × ℕ) : ℝ :=
  (source.bind (fun x => (ProbComp.eval (predict evaluate precision model (observe x))).map
    (fun answer => answer == truth x)) false).toReal

/-- A stopped model has exactly its deterministic majority error. -/
theorem predictionError_stopped {α : Type*} (source : PMF α) (observe : α → List Bool)
    (truth : α → Bool) (evaluate : List Bool → List Bool → Bool) (precision : ℕ) (model : State × ℕ)
    (hstopped : model.1.stopped = true) :
    predictionError source observe truth evaluate precision model =
      (source.toOuterMeasure
        {x | listStrictMajority (model.1.votes evaluate (observe x)) ≠ truth x}).toReal := by
  simp only [predictionError, predict, hstopped, ite_true, ProbComp.eval_pure, PMF.pure_map]
  change ((source.map (fun x => listStrictMajority (model.1.votes evaluate (observe x)) == truth x))
    false).toReal = _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 2
  ext x
  simp

section Correctness

variable {α : Type} [Fintype α]

/-- An active model has exactly the clipped error used by the slope-selection theorem. -/
theorem predictionError_active (source : PMF α) (observe : α → List Bool) (truth : α → Bool)
    (evaluate : List Bool → List Bool → Bool) (precision : ℕ) (model : State × ℕ)
    (hactive : model.1.stopped = false) :
    predictionError source observe truth evaluate precision model =
      clippedError source (model.1.margin (fun code x => evaluate code (observe x)) truth)
        (model.2 / dyadicSize precision) := by
  have hwrong (p : PMF Bool) (truth : Bool) :
      p.map (fun answer => answer == truth) false = p (!truth) := by
    cases truth <;> simp [PMF.map_apply]
  simp only [predictionError, predict, hactive, Bool.false_eq_true, ite_false,
    Cslib.Probability.PMF.bind_apply_toReal, hwrong, eval_clippedPredict_wrong,
    clippedError, State.margin, State.votes]

variable (source : ProbComp α) (observe : α → List Bool) (truth : α → Bool)
  (evaluate : List Bool → List Bool → Bool) (learn : State → ProbComp (List Bool))
  (params : Parameters)

/-- Either stopping branch gives the same prediction advantage, except for final slope selection. -/
theorem finish_sound (hparams : params.Valid) {state : State}
    (hstate : State.Successful (ProbComp.eval source)
      (fun code x => evaluate code (observe x)) truth params state)
    (hbounded : state.Bounded params.clock params.codeBound) :
    ((ProbComp.eval (finish evaluate ((fun x => (observe x, truth x)) <$> source)
      params state)).toOuterMeasure {model | ¬ predictionError (ProbComp.eval source) observe
        truth evaluate params.predictionGridBound model ≤
          params.delta / 2 - 1 / params.predictionInverseTolerance}).toReal ≤
      (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence := by
  cases hstopped : state.stopped
  · have h := hstate.selectSlope_advantage hparams hbounded hstopped params.confidence
    have herr (slope : ℕ) := predictionError_active (ProbComp.eval source) observe truth
      evaluate params.predictionGridBound (state, slope) hstopped
    simpa only [finish, hstopped, Bool.false_eq_true, ite_false, ProbComp.eval_map,
      PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq, herr] using h
  · have hgood : predictionError (ProbComp.eval source) observe truth evaluate
        params.predictionGridBound (state, 0) ≤
          params.delta / 2 - 1 / params.predictionInverseTolerance := by
      rw [predictionError_stopped _ _ _ _ _ _ hstopped]
      apply le_trans _ hparams.majority_error_le
      simpa only [State.Successful, hstopped, ite_true, State.votes] using hstate
    simp only [finish, hstopped, ite_true, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
      Set.mem_ofPred_eq, hgood, not_true_eq_false, ite_false, ENNReal.toReal_zero]
    positivity

variable (hparams : params.Valid) {error : ℝ} (herror : 0 ≤ error)
  (hlearn : ∀ state : State,
    params.delta ≤ density (ProbComp.eval source) params.rate
      (fun x => state.margin (fun code x => evaluate code (observe x)) truth x - state.threshold) →
    ((ProbComp.eval (learn state)).toOuterMeasure
      {code | ¬ State.GoodPredictor (ProbComp.eval source)
        (fun code x => evaluate code (observe x)) truth params state code}).toReal ≤ error)

include hparams herror hlearn

/-- The complete training algorithm has one failure bound for guards, learners, and selection.
All obligations refer to the supplied source and the descriptions actually stored by the loop. -/
theorem train_sound :
    ((ProbComp.eval (train evaluate ((fun x => (observe x, truth x)) <$> source)
      learn params)).toOuterMeasure {model | ¬ predictionError (ProbComp.eval source) observe
        truth evaluate params.predictionGridBound model ≤
          params.delta / 2 - 1 / params.predictionInverseTolerance}).toReal ≤
      params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + error) +
        (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence := by
  rw [train, ProbComp.eval_bind]
  refine (PMF.toOuterMeasure_bind_failure_toReal_le _ _
    {state | State.Successful (ProbComp.eval source)
      (fun code x => evaluate code (observe x)) truth params state} _ (by positivity)
    (fun state hsupport hstate => finish_sound source observe truth evaluate params hparams hstate
      (run_bounded evaluate _ learn params state hsupport))).trans ?_
  exact add_le_add
    (run_sound source observe truth evaluate learn params hparams herror hlearn) le_rfl

/-- Averaging over training gives an overall prediction-error bound. Training is
independent of the challenge, and only its public observation reaches the trained predictor. -/
theorem train_predict_error :
    (ProbComp.eval (do
      let x ← source
      let model ← train evaluate ((fun x => (observe x, truth x)) <$> source) learn params
      (fun answer => answer == truth x) <$>
        predict evaluate params.predictionGridBound model (observe x)) false).toReal ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance +
        params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + error) +
        (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence := by
  let training := train evaluate ((fun x => (observe x, truth x)) <$> source) learn params
  let test := fun model => (ProbComp.eval source).bind (fun x =>
    (ProbComp.eval (predict evaluate params.predictionGridBound model (observe x))).map
      (fun answer => answer == truth x))
  have hdelta := hparams.delta_pos
  have hthreshold : 0 ≤ params.delta / 2 - 1 / params.predictionInverseTolerance :=
    (by positivity : 0 ≤ 7 * params.delta / 16).trans hparams.majority_error_le
  have h := PMF.toOuterMeasure_bind_failure_toReal_le (ProbComp.eval training) test
    {model | predictionError (ProbComp.eval source) observe truth evaluate
      params.predictionGridBound model ≤ params.delta / 2 - 1 / params.predictionInverseTolerance}
    {false} hthreshold (fun model _ hgood => by
      simpa only [PMF.toOuterMeasure_apply_singleton, Set.mem_ofPred_eq, predictionError, test]
        using hgood)
  have hbad := train_sound source observe truth evaluate learn params hparams herror hlearn
  have hbound := h.trans (add_le_add hbad le_rfl)
  simp only [ProbComp.eval_bind, ProbComp.eval_map]
  rw [PMF.bind_comm (ProbComp.eval source)]
  have hfinal := by simpa only [PMF.toOuterMeasure_apply_singleton] using hbound
  dsimp only [training, test] at hfinal
  linarith

end Correctness

end Cslib.Crypto.Pseudoentropy.Boosting
