/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Probabilistic.NativeOpenSelection
import Complexity.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Actual correlated multi-query native execution

One private work-tape bit survives both calls. The first oracle reply is a fresh
fair bit; the second repeats that bit from private oracle state. Native control
uses the work bit and first answer to choose an early halt or a second query.
Bills and external durations depend on that actual history and query. The full
joint law, successful-output provenance and stopping/resource edges are checked.
-/

noncomputable section
open Cslib Cslib.Probability Turing
open Turing.MultiTapeMachine (Config Channel)
open Cslib.Probability.NativeOpenExecution
open scoped NNReal ENNReal
namespace ComplexityTests.NativeOpenExecution

inductive Control | draw | first | decide | second | finish
  deriving DecidableEq

instance : Fintype Control :=
  ⟨{.draw, .first, .decide, .second, .finish}, by intro c; cases c <;> simp⟩

/-- One ordinary instruction without moving heads. -/
def action (next : Option Control) (output : Option Bool := none)
    (write : Option (Option Bool) := none) : Turing.Action 1 Bool Control :=
  { inputTape := 0, workTapes := fun _ => (write, 0), output, state := next }

/-- A real open native machine retaining its coin on a work tape. -/
def machine : MultiTapePTM 1 Bool Control Unit where
  initial := .draw
  tr control _ work answer bit := match control with
    | .draw => .step (action (some .first) none (some (some bit)))
        (fun _ => some false) (fun _ => 0)
    | .first => .query () .decide
    | .decide =>
      let b := (work 0).getD false
      let u := (answer ()).getD false
      if b && u then .step (action none (some u)) (fun _ => none) (fun _ => 0)
      else .step (action (some .second)) (fun _ => some (b ^^ u)) (fun _ => 0)
    | .second => .query () .finish
    | .finish => .step (action none (answer ())) (fun _ => none) (fun _ => 0)

/-- The first reply's latent bit, charge and elapsed time. -/
def firstReply (u : Bool) : Reply := ⟨[u], 1, 2⟩

/-- Later replies retain the same latent bit, with query-dependent resources. -/
def laterReply (word : List Bool) (u : Bool) : Reply :=
  ⟨[u], if word = [true] then 7 else 2, if word = [true] then 5 else 1⟩

/-- The environment reads its full prior history and shares a hidden bit across
both calls. No response or charge independence is imposed. -/
def env : Environment Unit Bool := fun q memory =>
  if memory.events.isEmpty then
    (PMF.uniformOfFintype Bool).map (fun u => (firstReply u, u))
  else PMF.pure (laterReply q.2 memory.privateState, memory.privateState)

/-- Initial actual native tapes and empty observed history. -/
def start : World 1 Control Unit Bool [] := ⟨machine.initialConfig [], ⟨false, []⟩⟩

/-- Native first instruction writes the hidden bit, without exporting it. -/
def drawn (b : Bool) : World 1 Control Unit Bool [] :=
  ⟨start.config.step (action (some .first) none (some (some b)))
    (fun _ => some false) (fun _ => 0), start.memory⟩

/-- Actual first response installed on the answer tape. -/
def answered (b u : Bool) : World 1 Control Unit Bool [] :=
  ⟨(drawn b).config.receive () .decide [u],
    (drawn b).memory.record ((), [false]) (firstReply u) u⟩

/-- Native early halting branch, with its existing charge retained. -/
def early (b u : Bool) : World 1 Control Unit Bool [] :=
  ⟨(answered b u).config.step (action none (some u)) (fun _ => none) (fun _ => 0),
    (answered b u).memory⟩

/-- Native follow-up query encodes the stored coin xor the first reply. -/
def prepared (b u : Bool) : World 1 Control Unit Bool [] :=
  ⟨(answered b u).config.step (action (some .second))
    (fun _ => some (b ^^ u)) (fun _ => 0), (answered b u).memory⟩

/-- Actual correlated second response, preserving the same work tape. -/
def answeredAgain (b u : Bool) : World 1 Control Unit Bool [] :=
  ⟨(prepared b u).config.receive () .finish [u],
    (prepared b u).memory.record ((), [b ^^ u]) (laterReply [b ^^ u] u) u⟩

/-- Actual native final instruction, or the earlier halted configuration. -/
def finalWorld (b u : Bool) : World 1 Control Unit Bool [] :=
  if b && u then early b u else
    ⟨(answeredAgain b u).config.step (action none (some u)) (fun _ => none) (fun _ => 0),
      (answeredAgain b u).memory⟩

private theorem step_start : step machine env start =
    (PMF.uniformOfFintype Bool).map drawn := by
  simp only [step, start, MultiTapeMachine.initialConfig, machine, action, Cfg.init]
  rfl

private theorem step_drawn (b : Bool) : step machine env (drawn b) =
    (PMF.uniformOfFintype Bool).map (answered b) := by
  conv_rhs =>
    arg 1
    ext u
    unfold answered
  simp [step, drawn, start, machine, action, Action.apply, MultiTapeMachine.initialConfig,
    Config.step, env, Memory.record, PMF.map_comp, Function.comp_def, firstReply]

private theorem step_answered (b u : Bool) : step machine env (answered b u) =
    PMF.pure (if b && u then early b u else prepared b u) := by
  cases b <;> cases u <;>
    simp [step, answered, drawn, start, machine, action, Action.apply,
      MultiTapeMachine.initialConfig, Config.step, Config.receive, Config.answerSymbols,
      Channel.answerSymbol, Cfg.workTapeSymbols, early, prepared]

private theorem step_prepared (b u : Bool) : step machine env (prepared b u) =
    PMF.pure (answeredAgain b u) := by
  simp [step, prepared, answered, drawn, start, machine, action, Action.apply,
    MultiTapeMachine.initialConfig, Config.step, Config.receive, env, Memory.record,
    answeredAgain, laterReply]

private theorem step_answeredAgain (b u : Bool) : step machine env (answeredAgain b u) =
    PMF.pure (⟨(answeredAgain b u).config.step (action none (some u))
      (fun _ => none) (fun _ => 0), (answeredAgain b u).memory⟩ :
        World 1 Control Unit Bool []) := by
  simp [step, answeredAgain, prepared, answered, drawn, start, machine, action, Action.apply,
    MultiTapeMachine.initialConfig, Config.step, Config.receive, Config.answerSymbols,
    Channel.answerSymbol]

private theorem early_halted (b u : Bool) : (early b u).config.tapes.state = none := rfl

private theorem step_early (b u : Bool) :
    step machine env (early b u) = PMF.pure (early b u) := rfl

private theorem final_halted (b u : Bool) : (finalWorld b u).config.tapes.state = none := by
  cases b <;> cases u <;> rfl

/-- Full actual joint native law: control, work tape, channels, oracle private
state and every query/response/resource observation, not just the output marginal. -/
theorem native_joint_law : execute machine env 5 start =
    (PMF.uniformOfFintype Bool).bind (fun b =>
      (PMF.uniformOfFintype Bool).map (finalWorld b)) := by
  rw [execute_eq_stateLaw]
  simp only [ObservedProcess.stateLaw, PMF.pure_bind, step_start, PMF.bind_map,
    Function.comp_def, step_drawn, PMF.bind_bind]
  congr 1
  funext b
  congr 1
  funext u
  rw [step_answered]
  cases b <;> cases u
  all_goals simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
    ite_false, ite_true, PMF.pure_bind]
  · rw [step_prepared, PMF.pure_bind, step_answeredAgain]; rfl
  · rw [step_prepared, PMF.pure_bind, step_answeredAgain]; rfl
  · rw [step_prepared, PMF.pure_bind, step_answeredAgain]; rfl
  · rw [step_early, PMF.pure_bind, step_early]; rfl

/-- The private machine coin survives both calls on the actual work tape. -/
example (b u : Bool) : (finalWorld b u).config.tapes.workTapeSymbols 0 = some b := by
  cases b <;> cases u <;>
    simp [finalWorld, early, answeredAgain, prepared, answered, drawn, start, machine,
      action, Config.step, Config.receive, MultiTapeMachine.initialConfig, Action.apply,
      Cfg.workTapeSymbols]

/-- Every supported actual run has actually halted by the stated instruction clock. -/
theorem native_halted : ∀ next ∈ (execute machine env 5 start).support,
    next.config.tapes.state = none := by
  intro next hn
  rw [native_joint_law] at hn
  obtain ⟨b, _, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
  obtain ⟨u, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
  subst next
  exact final_halted b u

example : execute machine env 20 start = execute machine env 5 start := by
  exact execute_padding machine env 5 15 start native_halted

private theorem final_bill (b u : Bool) : tokenBill (finalWorld b u).memory.events =
    if b && u then 1 else if b ^^ u then 8 else 3 := by
  cases b <;> cases u <;>
    norm_num [finalWorld, early, answeredAgain, prepared, answered, drawn, start,
      tokenBill, firstReply, laterReply, Memory.record]

private theorem final_duration (b u : Bool) : elapsed (finalWorld b u).memory.events =
    if b && u then 2 else if b ^^ u then 7 else 3 := by
  cases b <;> cases u <;>
    norm_num [finalWorld, early, answeredAgain, prepared, answered, drawn, start,
      elapsed, firstReply, laterReply, Memory.record]

/-- Actual expected token charge includes the early stop and the correlated
query-dependent later charge. No expectation bound is a client premise. -/
theorem expected_bill : (∑' next, execute machine env 5 start next *
    (tokenBill next.memory.events : ℝ≥0∞)) = 5 := by
  rw [native_joint_law, PMF.tsum_bind_mul]
  simp only [PMF.tsum_map_mul, final_bill, tsum_fintype]
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]
  have h : (2 : ℝ≥0)⁻¹ * (2⁻¹ + 2⁻¹ * 8) + 2⁻¹ * (2⁻¹ * 8 + 2⁻¹ * 3) = 5 := by norm_num
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_inv_two, ENNReal.coe_ofNat] using hc

/-- Local native instructions do not contribute to the physical duration sum. -/
theorem expected_duration : (∑' next, execute machine env 5 start next *
    (elapsed next.memory.events : ℝ≥0∞)) = 19 / 4 := by
  rw [native_joint_law, PMF.tsum_bind_mul]
  simp only [PMF.tsum_map_mul, final_duration, tsum_fintype]
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]
  have h : (2 : ℝ≥0)⁻¹ * (2⁻¹ * 2 + 2⁻¹ * 7) + 2⁻¹ * (2⁻¹ * 7 + 2⁻¹ * 3) = 19 / 4 := by
    norm_num
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_inv_two, ENNReal.coe_ofNat,
    ENNReal.coe_div (show (4 : ℝ≥0) ≠ 0 by norm_num)] using hc

private theorem final_output (b u : Bool) : (finalWorld b u).config.tapes.output = [u] := by
  cases b <;> cases u <;>
    simp [finalWorld, early, answeredAgain, prepared, answered, drawn, start, machine,
      action, Config.step, Config.receive, MultiTapeMachine.initialConfig, Action.apply]

open Cslib.Probability.NativeOpenSelection

/-- Proposed candidate indices are parsed from actual answer words. -/
def parse (_ : Unit) (_ : List Bool) (answer : List Bool) : Finset Bool := answer.toFinset

/-- A real successful output on a true reply, but a fabricated family on a false
reply. The fabricated family will be rejected rather than assumed proposed. -/
def decode (word : List Bool) : Option (Finset Bool) :=
  if word = [true] then some {true} else some {false, true}

/-- Only singleton proposals are accepted by this client criterion. -/
def accept (C : Finset Bool) : Bool := decide (C.card = 1)

private theorem actual_proposal (b u : Bool) :
    u ∈ proposals parse (finalWorld b u).memory.events := by
  cases b <;> cases u <;>
    simp [proposals, parse, finalWorld, early, answeredAgain, prepared, answered,
      drawn, start, Memory.record, firstReply, laterReply]

/-- Actual successful-output-only provenance is established from the native law,
while the false-reply paths are allowed to contain unproposed failed outputs. -/
theorem source_selection_only : SelectionOnly machine env parse decode accept 5 start := by
  intro next hn C hr ha
  rw [native_joint_law] at hn
  obtain ⟨b, _, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
  obtain ⟨u, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
  subst next
  simp only [result, final_halted, Option.isNone_none, ite_true, final_output] at hr
  cases u with
  | false =>
    simp only [decode, Bool.false_eq_true, List.cons.injEq, and_true,
      ite_false, Option.some.injEq] at hr
    subst C
    norm_num [accept] at ha
  | true =>
    simp only [decode, ite_true, Option.some.injEq] at hr
    subst C
    exact Finset.singleton_subset_iff.mpr (actual_proposal b true)

/-- End-to-end actual native to public behavioral joint outcome law. -/
example :
    (ObservedProcess.publicLaw (step machine env) (view parse decode) 5 start).map
        (fun history => outcome accept (history.headD (view parse decode start))) =
      (PMF.uniformOfFintype Bool).bind (fun b =>
        (PMF.uniformOfFintype Bool).map (fun u =>
          outcome accept
            ⟨(finalWorld b u).memory.events, (finalWorld b u).config.tapes.state.isNone,
              result decode (finalWorld b u)⟩)) := by
  rw [behavioral_outcome_law machine env parse decode accept 5 start source_selection_only,
    native_joint_law, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

/-- The public behavioral representation preserves the actual stopped bill. -/
example : (∑' out,
    ((ObservedProcess.publicLaw (step machine env) (view parse decode) 5 start).map
      (fun history => outcome accept (history.headD (view parse decode start)))) out *
        (out.tokens : ℝ≥0∞)) = 5 := by
  rw [behavioral_outcome_law machine env parse decode accept 5 start source_selection_only,
    PMF.tsum_map_mul]
  exact expected_bill

/-- A live native output prefix is never accepted merely because the clock ends. -/
example : result decode (answeredAgain false true) = none := rfl

example : (view parse decode (answeredAgain false true)).halted = false := rfl

/-- Empty-ground completion uses a real native halting instruction and no query. -/
def noQuery : MultiTapePTM 1 Bool Control Unit where
  initial := .draw
  tr _ _ _ _ _ := .step (action none) (fun _ => none) (fun _ => 0)

def noQueryStart : World 1 Control Unit Bool [] := ⟨noQuery.initialConfig [], ⟨false, []⟩⟩

def emptyDone : World 1 Control Unit Bool [] :=
  ⟨noQueryStart.config.step (action none) (fun _ => none) (fun _ => 0), noQueryStart.memory⟩

/-- The accepted-empty stopping state is derived from actual initial native tapes. -/
theorem no_query_halts : execute noQuery env 1 noQueryStart = PMF.pure emptyDone := by
  rw [execute_one]
  change (PMF.uniformOfFintype Bool).bind (fun _ => PMF.pure emptyDone) = _
  exact PMF.bind_const _ _

example : execute machine env 100 emptyDone = PMF.pure emptyDone :=
  execute_halted machine env 100 emptyDone rfl

example : normalized parse (fun _ => some ∅) emptyDone = some ∅ ∧
    accepted (fun _ => true) (normalized parse (fun _ => some ∅) emptyDone) = true ∧
    tokenBill emptyDone.memory.events = 0 ∧ elapsed emptyDone.memory.events = 0 := by
  have hh : emptyDone.config.tapes.state = none := rfl
  simp only [normalized, result, hh, Option.isNone_none, ite_true]
  simp [emptyDone, noQueryStart, accepted, tokenBill, elapsed]

example : result (fun _ => some (∅ : Finset Bool)) start = none := rfl

end ComplexityTests.NativeOpenExecution
