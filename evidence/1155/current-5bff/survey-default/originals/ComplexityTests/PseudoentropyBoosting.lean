/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Loop
import Complexity.Tactic.PPT

/-!
# Sampled boosting clients

The stored description can predict differently from the learner's full output. A concrete
learner satisfies the truncated correlation contract and gives a nontrivial final error bound.
Resource certificates also cover invalid density parameters and different input encodings.
-/

namespace ComplexityTests.PseudoentropyBoosting

open Cslib Cslib.Probability Cslib.Crypto.Pseudoentropy.Boosting Cslib.BitString
  Turing.MultiTapeTM

private def parameters : Parameters := ⟨11, 1, 0, 0, 1⟩

private theorem valid : parameters.Valid := by
  norm_num [Parameters.Valid, parameters, Parameters.denominator, dyadicSize]

-- Truncation is semantically significant, including the zero-length case.
example : (State.initial.add 1 [true, false, false]).predictors = [[true]] ∧
    listStrictMajority [true, false, false] = false ∧ listStrictMajority [true] = true ∧
    (State.initial.add 0 [true]).predictors = [[]] := by decide

example : (State.encoding ((State.initial.shift true).add 2 [true, false, true])).length =
    1 * (2 * 2 + 3) + 4 := by decide

private theorem goodPredictor (state : State) :
    State.GoodPredictor (PMF.pure ()) (fun code _ => listStrictMajority code) (fun _ => true)
      parameters state [true, false, false] := by
  simp [State.GoodPredictor, parameters, Parameters.gamma, Parameters.rate, Parameters.delta,
    Parameters.inverseRate, Parameters.denominator, dyadicSize, density, signedVote,
    listStrictMajority]

-- Check the generic law before specializing the clock, keeping its proof opaque to the kernel.
private theorem perfectLearner_sound (params : Parameters) (hvalid : params.Valid)
    (hgood : ∀ state, State.GoodPredictor (PMF.pure ())
      (fun code _ => listStrictMajority code) (fun _ => true) params state [true, false, false]) :
    ((ProbComp.eval (run (fun code _ => listStrictMajority code)
      ((fun _ : Unit => ([], true)) <$> pure ())
      (fun _ => pure [true, false, false]) params)).toOuterMeasure
      {state | ¬ State.Successful (ProbComp.eval (pure () : ProbComp Unit))
        (fun code _ => listStrictMajority code) (fun _ => true) params state}).toReal ≤
        params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + 0) :=
  run_sound (pure ()) (fun _ => []) (fun _ => true)
    (fun code _ => listStrictMajority code) (fun _ => pure [true, false, false]) params
    hvalid (error := 0) (by rfl) (by
      intro state _
      simp [ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply, hgood])

-- A real learner discharges the analytic contract; the resulting error bound is below one.
example : ((ProbComp.eval (run (fun code _ => listStrictMajority code)
      ((fun _ : Unit => ([], true)) <$> pure ())
      (fun _ => pure [true, false, false]) parameters)).toOuterMeasure
      {state | ¬ State.Successful (ProbComp.eval (pure () : ProbComp Unit))
        (fun code _ => listStrictMajority code) (fun _ => true) parameters state}).toReal ≤
        1 / 8 := by
  exact (perfectLearner_sound parameters valid goodPredictor).trans (by
    norm_num [parameters, Parameters.clock, Parameters.inverseRate,
      Parameters.denominator, dyadicSize])

-- The storage invariant needs neither valid tests nor a correct learner.
example (params : Parameters) :
    ∀ state ∈ (ProbComp.eval (run (fun _ _ => false) (pure ([], true))
      (fun _ => pure (List.replicate (params.codeBound + 10) true)) params)).support,
      State.Bounded params.clock params.codeBound state :=
  run_bounded _ _ _ _

example : ComputableInPolyTime
    (fun word : List Bool => (⟨false, word.length, [word]⟩ : State)) encBits State.encoding := by
  polytime

example : ComputableInPolyTime
    (fun word : List Bool => ({ State.initial with predictors := [word] }).threshold)
    (encList encBool) encUnary := by fun_prop

example : ComputableInPolyTime
    (fun word : List Bool => (⟨word.length, 1, word.length, 0, word.length + 1⟩ : Parameters))
    encBits Parameters.encoding := by polytime

example : ComputableInPolyTime
    (fun p : Parameters × State => p.1.confidence + p.2.threshold)
    (encPair Parameters.encoding State.encoding) encUnary := by fun_prop

-- These are the same functional loop with different input encodings and parameter spellings.
example : IsPPTOn encBits State.encoding (fun word =>
    run (fun code observation => listStrictMajority (code ++ observation)) (pure (word, true))
      (fun state => pure (word.take (state.threshold + 1)))
      { confidence := word.length + 1, densityNumerator := 0, densityBound := 0,
        rateBound := 0, codeBound := word.length }) := by ppt

example : IsPPTOn (encList encBool) State.encoding (fun word => do
    let params : Parameters := ⟨word.length + 1, 0, 0, 0, word.length⟩
    run (fun code observation => listStrictMajority (code ++ observation)) (pure (word, true))
      (fun state => do return word.take (state.threshold + 1)) params) := by ppt

-- Unknown parameter computation must remain an explicit obligation.
example (params : List Bool → Parameters)
    (hparams : ComputableInPolyTime params encBits Parameters.encoding) :
    ComputableInPolyTime (fun word => (params word).codeBound) encBits encUnary := by
  fail_if_success (clear hparams; fun_prop)
  fun_prop

end ComplexityTests.PseudoentropyBoosting
