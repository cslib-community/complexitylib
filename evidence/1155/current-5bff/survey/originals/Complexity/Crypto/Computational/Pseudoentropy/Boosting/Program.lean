/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Decision
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Computability.Probabilistic.Adaptive
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PPT

/-!
# A clocked hard-core boosting program

The state stores a threshold, a list of predictor descriptions, and a stopping flag.
A fixed certified evaluator interprets each description on an observation. Each active round
tests the majority guard, optionally raises the threshold, and requests one new predictor.

The supplied learner is an explicit program with its own efficiency and correctness obligations.
We truncate its output to the declared description bound on every execution, including failures.
The analysis must therefore certify the truncated predictor. This gives a polynomial bound on
the complete state throughout the clocked loop without a probabilistic runtime exception.

## Main definitions

* `State`, `Parameters`: stored predictor descriptions and explicit resource parameters.
* `round`, `run`: the sampled body and its clocked iteration.

## Main results

* `round_bounded`, `run_bounded`: every execution preserves the storage invariant.
* `isPPTOn_round`, `isPPTOn_run`: compositional certificates for the complete programs.

## References

[Holenstein2005], Section 2.2, Figure 2 and Lemma 2.14. The proved polynomial clock replaces the
worst-dense-set stopping test. The majority test remains explicit and uses finite fair-bit
sampling. Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Probability BitString Turing.MultiTapeTM

/-- The executable state of the boosting loop. Predictor descriptions are ordinary binary words. -/
structure State where
  /-- Once true, all remaining clock ticks preserve this state. -/
  stopped : Bool
  /-- The number of shifts subtracted from the raw vote margin. -/
  threshold : ℕ
  /-- Predictor descriptions, newest first. -/
  predictors : List (List Bool)
  deriving DecidableEq

namespace State

/-- Reuse the standard Boolean, unary, and list encodings. -/
def encoding : State ↪ List Bool :=
  ⟨fun state => encPair encBool (encPair encUnary (encList encBits))
    (state.stopped, state.threshold, state.predictors), by
    intro left right h
    have hfields := (encPair encBool
      (encPair encUnary (encList encBits))).injective h
    cases left
    cases right
    simpa using hfields⟩

/-- Start before any learned predictors or threshold shifts. -/
def initial : State := ⟨false, 0, []⟩

/-- Evaluate the current collection on an observation. The truth label is not an input. -/
def votes (evaluate : List Bool → List Bool → Bool) (state : State)
    (observation : List Bool) : List Bool :=
  state.predictors.map (fun code => evaluate code observation)

/-- Move the threshold according to the sampled shift decision. -/
def shift (state : State) (yes : Bool) : State :=
  { state with threshold := state.threshold + if yes then 1 else 0 }

/-- Add a bounded predictor description. -/
def add (state : State) (bound : ℕ) (code : List Bool) : State :=
  { state with predictors := code.take bound :: state.predictors }

@[simp] theorem votes_initial (evaluate : List Bool → List Bool → Bool) (observation : List Bool) :
    initial.votes evaluate observation = [] := rfl

@[simp] theorem votes_shift (evaluate : List Bool → List Bool → Bool) (state : State)
    (yes : Bool) (observation : List Bool) :
    (state.shift yes).votes evaluate observation = state.votes evaluate observation := rfl

@[simp] theorem votes_add (evaluate : List Bool → List Bool → Bool) (state : State)
    (bound : ℕ) (code observation : List Bool) :
    (state.add bound code).votes evaluate observation =
      evaluate (code.take bound) observation :: state.votes evaluate observation := rfl

@[simp] theorem length_encoding (state : State) :
    (encoding state).length = 2 * state.threshold +
      (encList encBits state.predictors).length + 4 := by
  simp only [encoding, Function.Embedding.coeFn_mk, length_encPair, encBool_apply,
    List.length_singleton, encUnary_apply, List.length_replicate]
  lia

/-- After `rounds` rounds there are at most that many shifts and bounded descriptions. -/
def Bounded (rounds codeBound : ℕ) (state : State) : Prop :=
  state.threshold ≤ rounds ∧ state.predictors.length ≤ rounds ∧
    ∀ code ∈ state.predictors, code.length ≤ codeBound

@[simp] theorem bounded_initial (codeBound : ℕ) : Bounded 0 codeBound initial := by
  simp [Bounded, initial]

/-- A bound remains valid when more rounds are allowed. -/
theorem Bounded.mono {rounds more codeBound : ℕ} {state : State}
    (h : Bounded rounds codeBound state) (hmore : rounds ≤ more) :
    Bounded more codeBound state :=
  ⟨h.1.trans hmore, h.2.1.trans hmore, h.2.2⟩

/-- An optional shift and a truncated description preserve the resource invariant. -/
theorem Bounded.shift_add {rounds codeBound : ℕ} {state : State}
    (h : Bounded rounds codeBound state) (yes : Bool) (code : List Bool) :
    Bounded (rounds + 1) codeBound ((state.shift yes).add codeBound code) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [add, shift]
    split <;> lia [h.1]
  · simpa only [add, shift, List.length_cons] using Nat.add_le_add_right h.2.1 1
  · intro candidate hcandidate
    rcases List.mem_cons.mp hcandidate with rfl | hcandidate
    · simp only [List.length_take]; exact min_le_left _ _
    · exact h.2.2 candidate hcandidate

/-- The semantic resource invariant bounds the complete encoded state. -/
theorem Bounded.length_encoding_le {rounds codeBound : ℕ} {state : State}
    (h : Bounded rounds codeBound state) :
    (encoding state).length ≤ rounds * (2 * codeBound + 3) + 4 := by
  have hsum := List.sum_le_length_nsmul
    (state.predictors.map (fun code => 2 * code.length + 1)) (2 * codeBound + 1) (by
      intro value hvalue
      obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hvalue
      have := h.2.2 code hcode
      lia)
  simp only [List.length_map, smul_eq_mul] at hsum
  simp only [length_encoding, length_encList, encBits, Function.Embedding.refl_apply]
  have := Nat.mul_le_mul_right (2 * codeBound + 1) h.2.1
  nlinarith [h.1]

section Efficiency

variable {α : Type} {input : α ↪ List Bool} {state : α → State}

private theorem isPolyTime_fields
    (hstate : ComputableTidilyInPolyTime state input encoding) :
    ComputableTidilyInPolyTime
      (fun a => ((state a).stopped, (state a).threshold, (state a).predictors))
      input (encPair encBool (encPair encUnary (encList encBits))) :=
  hstate.of_enc_eq (fun _ => rfl)

/-- Efficient field values construct an efficient state. -/
@[program_certificate]
theorem isPolyTime_mk {stopped : α → Bool} {threshold : α → ℕ}
    {predictors : α → List (List Bool)}
    (hstopped : ComputableInPolyTime stopped input encBool)
    (hthreshold : ComputableInPolyTime threshold input encUnary)
    (hpredictors : ComputableInPolyTime predictors input (encList encBits)) :
    ComputableInPolyTime (fun a => ⟨stopped a, threshold a, predictors a⟩) input encoding := by
  have hstopped := hstopped.tidy
  have hthreshold := hthreshold.tidy
  have hpredictors := hpredictors.tidy
  exact .of_tidy ((hstopped.prod (hthreshold.prod hpredictors)).of_enc_eq (fun _ => rfl))

/-- Project the stopping flag through the shared pair implementation. -/
@[fun_prop]
theorem isPolyTime_stopped (hstate : ComputableInPolyTime state input encoding) :
    ComputableInPolyTime (fun a => (state a).stopped) input encBool := by
  have hstate := hstate.tidy
  exact .of_tidy ((isPolyTime_fields hstate).fst')

/-- Project the threshold through the shared pair implementation. -/
@[fun_prop]
theorem isPolyTime_threshold (hstate : ComputableInPolyTime state input encoding) :
    ComputableInPolyTime (fun a => (state a).threshold) input encUnary := by
  have hstate := hstate.tidy
  exact .of_tidy ((isPolyTime_fields hstate).snd'.fst')

/-- Project the predictor collection through the shared pair implementation. -/
@[fun_prop]
theorem isPolyTime_predictors (hstate : ComputableInPolyTime state input encoding) :
    ComputableInPolyTime (fun a => (state a).predictors) input (encList encBits) := by
  have hstate := hstate.tidy
  exact .of_tidy ((isPolyTime_fields hstate).snd'.snd')

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Evaluating a list of descriptions is an ordinary captured map. -/
@[program_certificate]
theorem isPolyTime_votes {evaluate : List Bool → List Bool → Bool}
    {observation : α → List Bool}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hstate : ComputableInPolyTime state input encoding)
    (hobservation : ComputableInPolyTime observation input encBits) :
    ComputableInPolyTime (fun a => (state a).votes evaluate (observation a))
      input encBits := by
  have hevaluate := hevaluate.tidy
  have hstate := hstate.tidy
  have hobservation := hobservation.tidy
  refine .of_tidy ?_
  unfold votes
  fun_prop

/-- Updating the threshold uses its field certificate and the efficient Boolean decision. -/
@[program_certificate]
theorem isPolyTime_shift {yes : α → Bool}
    (hstate : ComputableInPolyTime state input encoding)
    (hyes : ComputableInPolyTime yes input encBool) :
    ComputableInPolyTime (fun a => (state a).shift (yes a)) input encoding := by
  unfold shift
  polytime

/-- Truncation and list insertion charge for the complete stored predictor description. -/
@[program_certificate]
theorem isPolyTime_add {bound : α → ℕ} {code : α → List Bool}
    (hstate : ComputableInPolyTime state input encoding)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hcode : ComputableInPolyTime code input encBits) :
    ComputableInPolyTime (fun a => (state a).add (bound a) (code a)) input encoding := by
  unfold add
  fun_prop

end Efficiency

end State

/-- Natural parameters for exact dyadic weights and polynomial sampling budgets. -/
structure Parameters where
  /-- Each sampled guard has failure probability at most `2⁻confidence`. -/
  confidence : ℕ
  /-- The numerator of the target density. -/
  densityNumerator : ℕ
  /-- The parameter whose `dyadicSize` is the density denominator. -/
  densityBound : ℕ
  /-- The parameter whose `dyadicSize` is the reciprocal weight rate. -/
  rateBound : ℕ
  /-- Maximum length of each stored predictor description. -/
  codeBound : ℕ

namespace Parameters

/-- Store all five resource parameters in unary using the shared product encoding. -/
def encoding : Parameters ↪ List Bool :=
  ⟨fun params => encPair encUnary (encPair encUnary
      (encPair encUnary (encPair encUnary encUnary)))
    (params.confidence, params.densityNumerator, params.densityBound,
      params.rateBound, params.codeBound), by
    intro left right h
    have hfields := (encPair encUnary (encPair encUnary
      (encPair encUnary (encPair encUnary encUnary)))).injective h
    cases left
    cases right
    simpa using hfields⟩

section Efficiency

variable {α : Type} {input : α ↪ List Bool} {params : α → Parameters}

private theorem isPolyTime_fields
    (hparams : ComputableTidilyInPolyTime params input encoding) :
    ComputableTidilyInPolyTime (fun a =>
      ((params a).confidence, (params a).densityNumerator, (params a).densityBound,
        (params a).rateBound, (params a).codeBound))
      input (encPair encUnary
        (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))) :=
  hparams.of_enc_eq (fun _ => rfl)

/-- Computing the five fields suffices to construct the encoded parameter record. -/
@[program_certificate]
theorem isPolyTime_mk {confidence densityNumerator densityBound rateBound codeBound : α → ℕ}
    (hconfidence : ComputableInPolyTime confidence input encUnary)
    (hdensityNumerator : ComputableInPolyTime densityNumerator input encUnary)
    (hdensityBound : ComputableInPolyTime densityBound input encUnary)
    (hrateBound : ComputableInPolyTime rateBound input encUnary)
    (hcodeBound : ComputableInPolyTime codeBound input encUnary) :
    ComputableInPolyTime (fun a =>
      ⟨confidence a, densityNumerator a, densityBound a, rateBound a, codeBound a⟩)
      input encoding := by
  have hconfidence := hconfidence.tidy
  have hdensityNumerator := hdensityNumerator.tidy
  have hdensityBound := hdensityBound.tidy
  have hrateBound := hrateBound.tidy
  have hcodeBound := hcodeBound.tidy
  exact .of_tidy ((hconfidence.prod (hdensityNumerator.prod
    (hdensityBound.prod (hrateBound.prod hcodeBound)))).of_enc_eq (fun _ => rfl))

/-- Project the confidence through the shared product implementation. -/
@[fun_prop]
theorem isPolyTime_confidence (hparams : ComputableInPolyTime params input encoding) :
    ComputableInPolyTime (fun a => (params a).confidence) input encUnary := by
  have hparams := hparams.tidy
  exact .of_tidy ((isPolyTime_fields hparams).fst')

/-- Project the density numerator through the shared product implementation. -/
@[fun_prop]
theorem isPolyTime_densityNumerator (hparams : ComputableInPolyTime params input encoding) :
    ComputableInPolyTime (fun a => (params a).densityNumerator) input encUnary := by
  have hparams := hparams.tidy
  exact .of_tidy ((isPolyTime_fields hparams).snd'.fst')

/-- Project the density parameter through the shared product implementation. -/
@[fun_prop]
theorem isPolyTime_densityBound (hparams : ComputableInPolyTime params input encoding) :
    ComputableInPolyTime (fun a => (params a).densityBound) input encUnary := by
  have hparams := hparams.tidy
  exact .of_tidy ((isPolyTime_fields hparams).snd'.snd'.fst')

/-- Project the rate parameter through the shared product implementation. -/
@[fun_prop]
theorem isPolyTime_rateBound (hparams : ComputableInPolyTime params input encoding) :
    ComputableInPolyTime (fun a => (params a).rateBound) input encUnary := by
  have hparams := hparams.tidy
  exact .of_tidy ((isPolyTime_fields hparams).snd'.snd'.snd'.fst')

/-- Project the description bound through the shared product implementation. -/
@[fun_prop]
theorem isPolyTime_codeBound (hparams : ComputableInPolyTime params input encoding) :
    ComputableInPolyTime (fun a => (params a).codeBound) input encUnary := by
  have hparams := hparams.tidy
  exact .of_tidy ((isPolyTime_fields hparams).snd'.snd'.snd'.snd')

end Efficiency

/-- The density denominator is a positive power of two. -/
def denominator (params : Parameters) : ℕ := dyadicSize params.densityBound

/-- The reciprocal weight rate is a positive power of two. -/
def inverseRate (params : Parameters) : ℕ := dyadicSize params.rateBound

/-- A sufficient majority-test precision for every positive density numerator. -/
def majorityPrecision (params : Parameters) : ℕ := 32 * params.denominator

/-- A sufficient density-test precision at weight rate `1 / inverseRate`. -/
def shiftPrecision (params : Parameters) : ℕ := 32 * params.denominator * params.inverseRate

/-- A polynomial clock whenever `0 < densityNumerator ≤ denominator`. -/
def clock (params : Parameters) : ℕ := 4 * params.inverseRate ^ 2 * params.denominator ^ 3

end Parameters

/-- Draw a fresh labeled observation and evaluate the current predictor collection on it. -/
def withVotes (evaluate : List Bool → List Bool → Bool) (source : ProbComp (List Bool × Bool))
    (state : State) : ProbComp (List Bool × Bool) :=
  (fun sample => (state.votes evaluate sample.1, sample.2)) <$> source

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Training samples compose with the certified evaluator without exposing a machine. -/
theorem isPPTOn_withVotes {α : Type} {input : α ↪ List Bool}
    {evaluate : List Bool → List Bool → Bool}
    {source : α → ProbComp (List Bool × Bool)} {state : α → State}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hstate : ComputableInPolyTime state input State.encoding) :
    IsPPTOn input (encPair encBits encBool)
      (fun a => withVotes evaluate (source a) (state a)) := by
  have hevaluate := hevaluate.tidy
  have hstate := hstate.tidy
  unfold withVotes
  ppt

attribute [program_certificate] isPPTOn_withVotes

/-- One round of boosting. A previously stopped state is returned unchanged. -/
noncomputable def round (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool)) (learn : State → ProbComp (List Bool))
    (params : Parameters) (state : State) : ProbComp State := do
  if state.stopped then return state
  let training := withVotes evaluate source state
  let stop ← testMajority params.confidence params.majorityPrecision
    params.densityNumerator params.denominator
    ((fun sample => listNonpositiveMargin sample.1 sample.2) <$> training)
  if stop then return { state with stopped := true }
  let shift ← testShift params.confidence params.shiftPrecision params.densityNumerator
    params.denominator 1 params.inverseRate do
      let (votes, truth) ← training
      sampleWeight params.rateBound 1 state.threshold votes truth
  let shifted := state.shift shift
  let code ← learn shifted
  return shifted.add params.codeBound code

/-- Run the sampled boosting body for the proved polynomial clock. -/
noncomputable def run (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (learn : State → ProbComp (List Bool)) (params : Parameters) : ProbComp State :=
  OracleComp.iterate params.clock (round evaluate source learn params) State.initial

/-- Resource bounds hold on every outcome, including erroneous tests and learner failures. -/
theorem round_bounded (evaluate : List Bool → List Bool → Bool)
    (source : ProbComp (List Bool × Bool))
    (learn : State → ProbComp (List Bool)) (params : Parameters) {rounds : ℕ} {state : State}
    (hstate : State.Bounded rounds params.codeBound state) :
    ∀ next ∈ (ProbComp.eval (round evaluate source learn params state)).support,
      State.Bounded (rounds + 1) params.codeBound next := by
  intro next hnext
  unfold round at hnext
  split at hnext
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
    subst next
    exact hstate.mono (by lia)
  · simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hnext
    obtain ⟨stop, _, hnext⟩ := hnext
    split at hnext
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
      subst next
      exact hstate.mono (by lia)
    · simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff,
        ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
      obtain ⟨shift, _, code, _, rfl⟩ := hnext
      exact hstate.shift_add shift code

/-- The clocked loop stores at most one bounded predictor per round. -/
theorem run_bounded (evaluate : List Bool → List Bool → Bool) (source : ProbComp (List Bool × Bool))
    (learn : State → ProbComp (List Bool)) (params : Parameters) :
    ∀ state ∈ (ProbComp.eval (run evaluate source learn params)).support,
      State.Bounded params.clock params.codeBound state :=
  ProbComp.iterate_invariant params.clock (round evaluate source learn params) State.initial
    (fun rounds => State.Bounded rounds params.codeBound) (State.bounded_initial _)
    (fun _ _ _ hstate => round_bounded evaluate source learn params hstate)

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The complete sampled round composes the evaluator, source, learner, and unary parameters.
No machine implementation is part of the client's proof. -/
@[program_certificate]
theorem isPPTOn_round {α : Type} {input : α ↪ List Bool} {evaluate : List Bool → List Bool → Bool}
    {source : α → ProbComp (List Bool × Bool)} {learn : α → State → ProbComp (List Bool)}
    {params : α → Parameters}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hlearn : IsPPTOn (encPair input State.encoding) encBits
      (fun pair => learn pair.1 pair.2))
    (hparams : ComputableInPolyTime params input Parameters.encoding) :
    IsPPTOn (encPair input State.encoding) State.encoding
      (fun pair => round evaluate (source pair.1) (learn pair.1) (params pair.1) pair.2) := by
  have hevaluate := hevaluate.tidy
  have hparams := hparams.tidy
  unfold round Parameters.majorityPrecision Parameters.shiftPrecision
    Parameters.denominator Parameters.inverseRate
  dsimp only
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Polynomially bounded parameters and a certified learner give a strict PPT boosting loop.
The single resource invariant also proves `run_bounded`, independently of correctness. -/
@[program_certificate]
theorem isPPTOn_run {α : Type} {input : α ↪ List Bool} {evaluate : List Bool → List Bool → Bool}
    {source : α → ProbComp (List Bool × Bool)} {learn : α → State → ProbComp (List Bool)}
    {params : α → Parameters}
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hlearn : IsPPTOn (encPair input State.encoding) encBits
      (fun pair => learn pair.1 pair.2))
    (hparams : ComputableInPolyTime params input Parameters.encoding) :
    IsPPTOn input State.encoding (fun a => run evaluate (source a) (learn a) (params a)) := by
  have hevaluate := hevaluate.tidy
  have hparams := hparams.tidy
  have hclock : ComputableTidilyInPolyTime (fun a => (params a).clock) input encUnary := by
    unfold Parameters.clock Parameters.inverseRate Parameters.denominator
    polytime
  have hcode := (Parameters.isPolyTime_codeBound (.of_tidy hparams)).tidy
  refine (IsPPTOn.iterateWith_spec (stateEncoding := State.encoding)
    (initial := fun _ => State.initial)
    (step := fun a => round evaluate (source a) (learn a) (params a))
    hclock (by fun_prop) (isPPTOn_round (.of_tidy hevaluate) hsource hlearn (.of_tidy hparams))
    (fun a rounds => State.Bounded rounds (params a).codeBound)
    (fun _ => State.bounded_initial _)
    (fun a _ _ _ hstate => round_bounded evaluate (source a) (learn a) (params a) hstate)
    (size := fun a => (params a).clock * (2 * (params a).codeBound + 3) + 4)
    (ComputableTidilyInPolyTime.polyBounded (by fun_prop)) ?_).1
  intro a rounds state hrounds hstate
  exact hstate.length_encoding_le.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ hrounds) 4)

end Cslib.Crypto.Pseudoentropy.Boosting
