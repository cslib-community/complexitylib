/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import ComplexityTests.StochasticOracleResidualCover
import Complexity.Probability.StochasticOracle.NativeResidualOneTurn
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sampling
import Mathlib.Tactic

/-!
# Actual native randomization, private packet conditioning and clock padding

The first machine draws two fair bits. Its observed action is their conjunction;
the continuation reads the retained packet and emits its first bit. On the
false-action fiber the conditional probability of true output is 1/3, not 1/2.
This detects forgetting private-state/action correlations. Both actual machines
halt, and padding either local clock preserves the entire joint law.
-/

noncomputable section
open Cslib Cslib.Probability Cslib.Optimization.OneConstraint
open Turing Turing.MultiTapePTM
namespace ComplexityTests.NativeOneTurn

/-- Read the retained packet's first bit, emit it, and actually halt. -/
def echoHead : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ _ := .step
    { inputTape := 0, workTapes := Fin.elim0, output := symbol, state := none }
    Empty.elim Empty.elim

/-- Two genuine native phases, not supplied probability tables or evaluators. -/
def selector : NativeOneTurn Bool Bool Bool where
  firstTapes := 0
  FirstState := Unit
  firstFinite := inferInstance
  first := uniformListMachine
  firstClock := 3
  action word := decide (word = [true, true])
  finishTapes := 0
  FinishState := Unit
  finishFinite := inferInstance
  finish := echoHead
  finishClock := 1
  prepare packet _ := packet
  output word := word.headD false

/-- The response exposes the chosen action and no private coins. -/
def respond (a : Bool) : Distribution Bool ℝ := Distribution.pure a

private theorem echo_word_law (word : List Bool) (hw : word.length = 2) :
    ProbComp.eval (echoHead.runClosed 1 word) = PMF.pure [word.headD false] := by
  cases word with
  | nil => simp at hw
  | cons b bs =>
    cases bs with
    | nil => simp at hw
    | cons c cs =>
      have he : cs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hw; omega)
      subst cs
      have hn : (1 : Fin 4) ≠ 0 := by decide
      simp [echoHead, runClosed, Turing.MultiTapePTM.run,
        runFrom, runConfigFrom, MultiTapeMachine.runConfigFrom, MultiTapeMachine.initialConfig,
        Cfg.inputSymbol, MultiTapeMachine.Config.step, Action.apply,
        Function.comp_def, PMF.map, PMF.bind_const, hn]

private theorem output_law (word : List Bool) (hw : word.length = 2) (r : Bool) :
    selector.finishLaw word r = PMF.pure (word.headD false) := by
  change (ProbComp.eval (echoHead.runClosed 1 word)).map _ = _
  rw [echo_word_law word hw, PMF.pure_map]
  rfl

private theorem joint_law : selector.run [false, false] respond =
    (PMF.uniformOfFintype Bool).bind (fun b => (PMF.uniformOfFintype Bool).map
      (fun c => (b && c, b && c, b))) := by
  unfold NativeOneTurn.run
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind]
  change (ProbComp.eval (uniformListMachine.runClosed 3 [false, false])).bind _ = _
  have hs : ProbComp.eval (uniformListMachine.runClosed 3 [false, false]) =
      BitString.uniformList 2 := eval_uniformListMachine _
  rw [hs]
  rw [BitString.uniformList_succ, BitString.uniformList_succ, BitString.uniformList_zero]
  simp only [PMF.bind_bind, PMF.map_bind, PMF.pure_map, PMF.pure_bind]
  congr 1
  funext b
  rw [PMF.map]
  congr 1
  funext c
  simp only [respond, Distribution.toPMF_pure, PMF.pure_bind]
  rw [output_law _ (by simp)]
  cases b <;> cases c <;> simp [selector]

private theorem mass (a r o : Bool) :
    (selector.run [false, false] respond (a, r, o)).toReal =
      (if (true, true, true) = (a, r, o) then 1 / 4 else 0) +
      (if (false, false, true) = (a, r, o) then 1 / 4 else 0) +
      (if (false, false, false) = (a, r, o) then 1 / 2 else 0) := by
  rw [joint_law]
  cases a <;> cases r <;> cases o <;>
    norm_num [PMF.bind_apply, PMF.map_apply, tsum_fintype, Fintype.sum_bool,
      PMF.uniformOfFintype_apply, ENNReal.toReal_add]

example : (selector.run [false, false] respond (true, true, false)).toReal = 0 := by
  norm_num [mass]

private theorem action_false : (selector.actionTable [false, false]).weight false = 3 / 4 := by
  have h0 := selector.behavioralRun_weight [false, false] respond false false false
  have h1 := selector.behavioralRun_weight [false, false] respond false false true
  have ht := (selector.outputTable [false, false] false false).total
  rw [← Distribution.toPMF_real, selector.behavioralRun_toPMF] at h0 h1
  norm_num [mass, respond, Distribution.pure] at h0 h1
  simp only [Fintype.sum_bool] at ht
  nlinarith

/-- Conditioning on the actual emitted batch changes the private-coin law. -/
example : (selector.outputTable [false, false] false false).weight true = 1 / 3 := by
  have h := selector.behavioralRun_weight [false, false] respond false false true
  have hm : (selector.behavioralRun [false, false] respond).weight (false, false, true) =
      1 / 4 := by
    rw [← Distribution.toPMF_real, selector.behavioralRun_toPMF]
    norm_num [mass]
  rw [hm, action_false] at h
  norm_num [respond, Distribution.pure] at h
  linarith

private theorem echo_halted (word : List Bool) :
    ∀ cfg ∈ (ProbComp.eval (echoHead.runClosedConfigFrom 1
      (echoHead.initialConfig word))).support, cfg.tapes.state = none := by
  simp [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom,
    MultiTapeMachine.initialConfig, echoHead, MultiTapeMachine.Config.step]

/-- The protocol's actual halting contract is satisfiable for native machines. -/
theorem selector_halts : selector.Halts [false, false] respond := by
  constructor
  · exact uniformListMachine_halted _
  · intro word _ r _
    exact echo_halted word

example : ({ selector with firstClock := 8 } : NativeOneTurn Bool Bool Bool).run
    [false, false] respond = selector.run [false, false] respond :=
  selector.run_pad_first _ _ selector_halts 8 (by norm_num [selector])

example : ({ selector with finishClock := 9 } : NativeOneTurn Bool Bool Bool).run
    [false, false] respond = selector.run [false, false] respond :=
  selector.run_pad_finish _ _ selector_halts 9 (by norm_num [selector])

/-- The native continuation really emits an encoded bit, rather than relying on
an arbitrary classification of invalid output words. -/
def bitEncoding : Bool ↪ List Bool :=
  ⟨fun b => [b], by intro a b h; simpa using congrArg (fun word => word.headD false) h⟩

theorem selector_encoded : selector.OutputsEncoded bitEncoding [false, false] respond := by
  intro packet hp r _ word hw
  have hs : ProbComp.eval (uniformListMachine.runClosed 3 [false, false]) =
      BitString.uniformList 2 := eval_uniformListMachine _
  change packet ∈ (ProbComp.eval (uniformListMachine.runClosed 3 [false, false])).support at hp
  rw [hs] at hp
  have hl := BitString.length_of_mem_support_uniformList hp
  change word ∈ (ProbComp.eval (echoHead.runClosed 1 packet)).support at hw
  rw [echo_word_law packet hl] at hw
  have he := (PMF.mem_support_pure_iff _ _).mp hw
  subst word
  rfl

example : ((selector.behavioralRun [false, false] respond).toPMF.map
    (fun (a, r, o) => (a, r, bitEncoding o))) = selector.rawRun [false, false] respond := by
  exact selector.behavioralRun_encoded _ _ bitEncoding selector_encoded

open Cslib.Probability.StochasticOracle.ResidualCover
open ComplexityTests.StochasticOracleResidualCover

/-- A native packet protocol with an explicit family observation adapter.
All specialists are queried, so the decoded full family has actual provenance.
This client does not realize the source's original candidate encoding. -/
def residualSelector : NativeOneTurn (Batch 5) (Option (Fin 5)) (Finset (Candidate blocks)) where
  firstTapes := 0
  FirstState := Unit
  firstFinite := inferInstance
  first := uniformListMachine
  firstClock := 3
  action _ := specialistBatch
  finishTapes := 0
  FinishState := Unit
  finishFinite := inferInstance
  finish := echoHead
  finishClock := 1
  prepare packet _ := packet
  output _ := payload blocks Finset.univ

private theorem residual_finish (packet : List Bool) (r : Option (Fin 5)) :
    residualSelector.finishLaw packet r = PMF.pure (payload blocks Finset.univ) :=
  PMF.map_const _ _

private theorem residual_law : residualSelector.run [false, false] (reply parameters) =
    PMF.pure (specialistBatch, none, payload blocks Finset.univ) := by
  unfold NativeOneTurn.run
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind,
    show residualSelector.action = fun _ => specialistBatch from rfl,
    reply, specialistBatch, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
    ite_false, Distribution.toPMF_pure, PMF.pure_bind, residual_finish, PMF.pure_map,
    PMF.bind_const]

/-- Actual supported halting and source successful-output provenance are proved. -/
theorem residual_admitted : NativeAdmitted residualSelector [false, false] parameters
    (by norm_num) := by
  constructor
  · constructor
    · exact uniformListMachine_halted _
    · intro word _ r _
      exact echo_halted word
  · intro A r C hp _
    rw [residual_law] at hp
    by_cases he : (A, r, C) = (specialistBatch, none, payload blocks Finset.univ)
    · cases he
      have hr : received (specialistBatch : Batch 5) none = Finset.univ := by
        ext j
        simp [received, specialistBatch]
      rw [hr]
    · simp [PMF.pure_apply, he] at hp

private theorem residual_success :
    (∑ t : Batch 5 × Option (Fin 5) × Finset (Candidate blocks),
      let (A, r, C) := t;
      (residualSelector.run [false, false] (reply parameters) (A, r, C)).toReal *
        optimalOutput (by norm_num) C) = 1 := by
  have ho : optimalOutput (T := blocks) (by norm_num) (payload blocks Finset.univ) = 1 := by
    simp [optimalOutput, (primal_optimum blocks (by norm_num)).1,
      (primal_optimum blocks (by norm_num)).2.1]
  change (Distribution.ofPMF (residualSelector.run [false, false] (reply parameters))).mean
    (fun (_, _, C) => optimalOutput (by norm_num) C) = 1
  rw [residual_law, Distribution.ofPMF_pure, Distribution.mean_pure]
  exact ho

/-- The generic native lower-bound theorem applies to actual native machines. -/
example : (5 : ℝ) ≤
    ∑ t : Batch 5 × Option (Fin 5) × Finset (Candidate blocks),
      (residualSelector.run [false, false] (reply parameters) t).toReal *
        batchCost parameters t.1 := by
  have h := native_one_turn_lower residualSelector [false, false] parameters (by norm_num)
    residual_admitted residual_success
  norm_num [parameters] at h ⊢
  exact h

/-- The actual native protocol attains that cost, excluding local transitions. -/
example : (∑ t : Batch 5 × Option (Fin 5) × Finset (Candidate blocks),
    (residualSelector.run [false, false] (reply parameters) t).toReal * batchCost parameters t.1) =
      5 := by
  change (Distribution.ofPMF (residualSelector.run [false, false] (reply parameters))).mean
    (fun t => batchCost parameters t.1) = 5
  rw [residual_law, Distribution.ofPMF_pure, Distribution.mean_pure]
  norm_num [batchCost, specialistBatch, parameters]

/-- A fallback candidate never returned by these specialist opportunities. -/
def fabricated : Finset (Candidate blocks) := {⟨0, none⟩}

private theorem fabricated_not_optimal :
    optimalOutput (T := blocks) (by norm_num) fabricated = 0 := by
  norm_num [optimalOutput, fabricated,
    Cslib.Probability.StochasticOracle.PartialCover.Instance.cost, coverInstance, weight]

private theorem fabricated_not_proposed :
    ¬ fabricated ⊆ payload blocks (received (specialistBatch : Batch 5) none) := by
  intro h
  have hc := h (show (⟨0, none⟩ : Candidate blocks) ∈ fabricated by simp [fabricated])
  obtain ⟨j, _, hc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨A, _, he⟩ := Finset.mem_map.mp hc
  have ho := congrArg (fun c : Candidate blocks => c.2.isNone) he
  change false = true at ho
  cases ho

/-- Native failed outputs may be unproposed. This is source-admissible because
only successful covers count toward selection-only success. -/
def failureSelector := { residualSelector with output := fun _ => fabricated }

private theorem failure_law : failureSelector.run [false, false] (reply parameters) =
    PMF.pure (specialistBatch, none, fabricated) := by
  have hf (packet : List Bool) (r : Option (Fin 5)) :
      failureSelector.finishLaw packet r = PMF.pure fabricated := PMF.map_const _ _
  unfold NativeOneTurn.run
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind,
    show failureSelector.action = fun _ => specialistBatch from rfl,
    reply, specialistBatch, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
    ite_false, Distribution.toPMF_pure, PMF.pure_bind, hf, PMF.pure_map, PMF.bind_const]

example : NativeAdmitted failureSelector [false, false] parameters (by norm_num) := by
  constructor
  · exact residual_admitted.1
  · intro A r C hp hs
    rw [failure_law] at hp
    by_cases he : (A, r, C) = (specialistBatch, none, fabricated)
    · cases he
      rw [fabricated_not_optimal] at hs
      norm_num at hs
    · simp [PMF.pure_apply, he] at hp

/-- The fabricated failure family is actually removed; its optimal-success
indicator was already zero, rather than an assumed provenance condition. -/
example : proposedOnly (T := blocks) specialistBatch none fabricated = ∅ ∧
    optimalOutput (T := blocks) (by norm_num) fabricated = 0 := by
  exact ⟨by simp [proposedOnly, fabricated_not_proposed], fabricated_not_optimal⟩

end ComplexityTests.NativeOneTurn
