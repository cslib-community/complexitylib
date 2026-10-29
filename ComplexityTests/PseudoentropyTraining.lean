/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Training
import Complexity.Probability.Quantile
import Complexity.Tactic.PPT

/-!
# Empirical selection and trained prediction

Selection handles empty pools and score ties. Clipping handles both signs and zero margins.
The complete training contract has a concrete learner and a nontrivial prediction-error bound.
Composed programs use captured inputs and alternative encodings without exposing machines.
-/

namespace ComplexityTests.PseudoentropyTraining

open Cslib Cslib.Probability Cslib.Crypto.Pseudoentropy.Boosting Cslib.BitString
  Turing.MultiTapeTM

-- Zero candidates return the fallback without using either generator or test.
example (source : ProbComp Bool) (test : Bool → ProbComp Bool) :
    OracleComp.sampleBest 0 7 source test true = pure true := by
  simp [OracleComp.sampleBest, OracleComp.selectFrom, OracleComp.selectBest]

-- All zero-trial scores tie; the last index wins, independently of the tests.
example (test : ℕ → ProbComp Bool) : OracleComp.selectBest 3 0 test = pure 2 := by
  simp [OracleComp.selectBest, OracleComp.iterate, OracleComp.selectStep,
    OracleComp.countTrue, OracleComp.selectUpdate]

example : ProbComp.eval (OracleComp.selectBest 2 1 (fun i => pure (i == 0))) = PMF.pure 0 := by
  simp [OracleComp.selectBest, OracleComp.iterate, OracleComp.selectStep,
    OracleComp.countTrue, OracleComp.replicate, OracleComp.selectUpdate, ProbComp.eval_pure]

-- A point mass still has a lower tail of mass 1/3: its boundary weight must be fractional.
example : ∃ softSet : Unit → ℝ, softSet () = 1 / 3 ∧
    (∑ x, (PMF.pure () x).toReal * softSet x) = 1 / 3 := by
  obtain ⟨_, _, softSet, _, _, _, hmass⟩ := PMF.exists_lowerTail (PMF.pure ())
    (fun _ => (7 : ℝ)) (δ := 1 / 3) (by norm_num) (by norm_num)
  exact ⟨softSet, by simpa using hmass, hmass⟩

example (bound numerator : ℕ) :
    (ProbComp.eval (clippedPredict bound numerator []) true).toReal = 1 / 2 := by
  rw [eval_clippedPredict_true]
  norm_num [listVoteMargin, clippedProbability]

example : (ProbComp.eval (clippedPredict 0 2 [true]) true).toReal = 1 ∧
    (ProbComp.eval (clippedPredict 0 2 [false]) true).toReal = 0 ∧
    (ProbComp.eval (clippedPredict 0 0 [true, true]) true).toReal = 1 / 2 := by
  simp only [eval_clippedPredict_true]
  norm_num [listVoteMargin, clippedProbability, dyadicSize]

private def parameters : Parameters := ⟨22, 1, 0, 0, 1⟩

private theorem valid : parameters.Valid := by
  norm_num [Parameters.Valid, parameters, Parameters.denominator, dyadicSize]

private theorem goodPredictor (state : State) :
    State.GoodPredictor (PMF.pure ()) (fun code _ => listStrictMajority code) (fun _ => true)
      parameters state [true, false, false] := by
  simp [State.GoodPredictor, parameters, Parameters.gamma, Parameters.rate, Parameters.delta,
    Parameters.inverseRate, Parameters.denominator, dyadicSize, density, signedVote,
    listStrictMajority]

-- Keeping the generic theorem opaque avoids expanding the concrete training computation.
private theorem perfectLearner_predict (params : Parameters) (hvalid : params.Valid)
    (hgood : ∀ state, State.GoodPredictor (PMF.pure ())
      (fun code _ => listStrictMajority code) (fun _ => true) params state [true, false, false]) :
    (ProbComp.eval (do
      let _ ← (pure () : ProbComp Unit)
      let model ← train (fun code _ => listStrictMajority code)
        ((fun _ : Unit => ([], true)) <$> pure ()) (fun _ => pure [true, false, false]) params
      (fun answer => answer == true) <$>
        predict (fun code _ => listStrictMajority code) params.predictionGridBound model [])
      false).toReal ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance +
        params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + 0) +
        (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence :=
  train_predict_error (pure ()) (fun _ => []) (fun _ => true)
    (fun code _ => listStrictMajority code) (fun _ => pure [true, false, false]) params
    hvalid (error := 0) (by rfl) (by
      intro state _
      simp [ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply, hgood])

example : (ProbComp.eval (do
      let _ ← (pure () : ProbComp Unit)
      let model ← train (fun code _ => listStrictMajority code)
        ((fun _ : Unit => ([], true)) <$> pure ()) (fun _ => pure [true, false, false]) parameters
      (fun answer => answer == true) <$>
        predict (fun code _ => listStrictMajority code) parameters.predictionGridBound model [])
      false).toReal ≤ 1 / 3 := by
  apply (perfectLearner_predict parameters valid goodPredictor).trans
  have hlog : Nat.log 2 131072 = 17 := by decide
  norm_num [parameters, Parameters.delta, Parameters.predictionGridBound,
    Parameters.predictionInverseTolerance, Parameters.clock, Parameters.inverseRate,
    Parameters.denominator, dyadicSize, hlog]

-- Search includes all list storage, lookups and the original input captured by each trial.
example : IsPPTOn encBits encUnary (fun word =>
    OracleComp.selectFrom (List.range (word.length + 1)) (word.length + 1)
      (fun candidate => pure (candidate < word.length)) 0) := by ppt

example : IsPPTOn (encList encBool) encBool (fun word =>
    OracleComp.sampleBest (word.length + 1) (word.length + 1) (pure true)
      (fun candidate => pure (candidate == listStrictMajority word)) false) := by ppt

attribute [local fun_prop] ComputableInPolyTime.tidy in
-- Training and prediction compose directly, including computation of the final precision.
example : IsPPTOn encBits encBool (fun word => do
    let params : Parameters := ⟨word.length + 1, 0, 0, 0, word.length⟩
    let model ← train (fun code observation => listStrictMajority (code ++ observation))
      (pure (word, true)) (fun state => pure (word.take (state.threshold + 1))) params
    predict (fun code observation => listStrictMajority (code ++ observation))
      params.predictionGridBound model word) := by ppt

attribute [local fun_prop] ComputableInPolyTime.tidy in
example : IsPPTOn (encList encBool) (encPair State.encoding encUnary) (fun word =>
    train (fun code observation => listStrictMajority (code ++ observation)) (pure (word, true))
      (fun state => pure (word.take (state.threshold + 1)))
      { confidence := word.length + 1, densityNumerator := 0, densityBound := 0,
        rateBound := 0, codeBound := word.length }) := by ppt

-- An unknown evaluator still requires its efficiency certificate.
example (evaluate : List Bool → List Bool → Bool)
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool) :
    IsPPTOn encBits encBool (fun word =>
      predict evaluate word.length (⟨true, 0, [word]⟩, word.length) word) := by
  fail_if_success (clear hevaluate; ppt)
  ppt

end ComplexityTests.PseudoentropyTraining


namespace ComplexityTests.PseudoentropyTraining
open Cslib Cslib.Probability Turing.MultiTapeTM

-- Selection retains arbitrary caller/output encodings and every supplied callback contract.
example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {values : α → List β} {trials : α → ℕ} {test : α → β → ProbComp Bool}
    (fallback : β)
    (hv : ComputableInPolyTime values input (encList output))
    (hn : ComputableInPolyTime trials input encUnary)
    (ht : IsPPTOn (encPair input output) encBool (fun p => test p.1 p.2)) :
    IsPPTOn input output (fun a => OracleComp.selectFrom (values a) (trials a) (test a)
      fallback) := by
  fail_if_success (clear hv; ppt)
  fail_if_success (clear hn; ppt)
  fail_if_success (clear ht; ppt)
  ppt

end ComplexityTests.PseudoentropyTraining
