/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Probabilistic.NativeEpoch
import CslibFrontierTests.NativeUnboundedExecution
import CslibFrontierTests.NativeOpenExecution
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Actual stopping epochs through unbounded private native computation

The native selector waits for a favorable private coin, issues a single actual
query, then verifies/halts locally. Its first-query law is derived without a
uniform local clock. Response/cost/duration correlation, full native continuation
and silent divergence remain explicit. The two-query fixture checks memory and
actual response-record accounting at epochs.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution NativeInterface NativeEpoch
open scoped ENNReal NNReal
namespace CslibFrontierTests.NativeEpoch
open CslibFrontierTests.NativeUnboundedExecution

abbrev P := Phase 0 Control Unit Bool []

def queryCheckpoint : P := .pending (.query start () .finish)

def localCheckpoint : P := .pending (.local start)

private theorem wait_instruction (bit : Bool) : instruction machine start bit =
    if bit then .query start () .finish else .local start := by
  cases bit
  · have hw : start.config.step (action (some .wait)) (fun _ => none) (fun _ => 0) =
        start.config := by
      simp only [start, machine, action, MultiTapeMachine.initialConfig,
        MultiTapeMachine.Config.step, Action.apply, Cfg.init]
      congr 2 <;> funext i <;> exact Fin.elim0 i
    change Instruction.local (⟨start.config.step (action (some .wait)) (fun _ => none)
      (fun _ => 0), start.memory⟩ : World 0 Control Unit Bool []) = .local start
    rw [hw]
  · rfl

private theorem silent_start : silentStep machine env (.ready start) =
    (PMF.uniformOfFintype Bool).map
      (fun bit => if bit then queryCheckpoint else localCheckpoint) := by
  simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
    NativeUnboundedExecution.halted, show start.config.tapes.state = some .wait from rfl,
    reduceCtorEq, ite_false, phaseStep, Option.isNone_some, Bool.false_eq_true,
    prepare, PMF.map_comp, Function.comp_def, wait_instruction]
  congr 1
  funext bit
  cases bit <;> rfl

private theorem silent_local :
    silentStep machine env localCheckpoint = PMF.pure (.ready start) := by
  simp [silentStep, StoppedProcess.beforeBoundary, boundary, localCheckpoint, phaseStep, dispatch]

private theorem absorbs (phase : P) (h : boundary phase) :
    silentStep machine env phase = PMF.pure phase :=
  StoppedProcess.beforeBoundary_absorbs _ _ _ h

private def mass (phase next : P) : ℝ≥0∞ :=
  StoppedProcess.terminalMass (silentStep machine env) boundary phase next

private theorem mass_local (next : P) : mass localCheckpoint next = mass (.ready start) next := by
  unfold mass
  rw [StoppedProcess.terminalMass_unfold (silentStep machine env) boundary absorbs, silent_local]
  simp [PMF.pure_apply, ite_mul]

private theorem mass_query (next : P) : mass queryCheckpoint next = PMF.pure queryCheckpoint next :=
  StoppedProcess.terminalMass_halted _ _
    absorbs queryCheckpoint trivial next

/-- Genuine first-query stopping law of the actual geometric private-coin loop. -/
theorem first_query : seek machine env start = PMF.pure (some queryCheckpoint) := by
  classical
  apply StoppedProcess.option_ext
  intro next
  have he : mass (.ready start) next = (2 : ℝ≥0∞)⁻¹ * mass (.ready start) next +
      (2 : ℝ≥0∞)⁻¹ * PMF.pure queryCheckpoint next := by
    conv_lhs =>
      unfold mass
      rw [StoppedProcess.terminalMass_unfold (silentStep machine env) boundary absorbs,
        silent_start]
    change (∑' phase, ((PMF.uniformOfFintype Bool).map _ : PMF P) phase * mass phase next) = _
    rw [PMF.tsum_map_mul, tsum_bool]
    simp only [Bool.false_eq_true, ite_false, ite_true, mass_local, mass_query]
    norm_num [PMF.uniformOfFintype_apply]
  have hm : mass (.ready start) next ≠ ⊤ := ne_top_of_le_ne_top (show (1 : ℝ≥0∞) ≠ ⊤ by norm_num)
    ((le_tsum (mass (.ready start)) next).trans (StoppedProcess.terminalMass_sum_le _ _
      absorbs (.ready start)))
  have hq := (PMF.pure queryCheckpoint).apply_ne_top next
  have hc : (2 : ℝ≥0∞)⁻¹ ≠ ⊤ := by norm_num
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hc hm) (ENNReal.mul_ne_top hc hq)] at hr
  norm_num only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hr
  have eqm : mass (.ready start) next = PMF.pure queryCheckpoint next :=
    (ENNReal.toReal_eq_toReal_iff' hm hq).mp (by linarith)
  change mass (.ready start) next = _
  rw [eqm]
  simp [PMF.pure_apply]

/-- Only one actual response is dispatched after any amount of silent waiting. -/
theorem first_response : nextEpoch machine env start =
    (PMF.uniformOfFintype Bool).map (fun u => some (answered u)) := by
  rw [nextEpoch, first_query, PMF.pure_bind]
  simp only [respond, queryCheckpoint, dispatch, env, PMF.map_comp]
  rfl

private theorem finish_instruction (u bit : Bool) : instruction machine (answered u) bit =
    .local (done u) := rfl

private theorem silent_answered (u : Bool) : silentStep machine env (.ready (answered u)) =
    PMF.pure (.pending (.local (done u))) := by
  simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
    NativeUnboundedExecution.halted, show (answered u).config.tapes.state = some .finish from rfl,
    reduceCtorEq, ite_false, phaseStep, Option.isNone_some, Bool.false_eq_true,
    prepare, PMF.map_comp, Function.comp_def, finish_instruction]
  exact PMF.map_const _ _

/-- Native verification and halting after the response are silent; they do not
consume another oracle turn or add token/physical-time receipts. -/
theorem next_halt (u : Bool) : seek machine env (answered u) =
    PMF.pure (some (.ready (done u))) := by
  unfold seek
  rw [StoppedProcess.terminal_step (silentStep machine env) boundary absorbs,
    silent_answered, PMF.pure_bind]
  rw [StoppedProcess.terminal_step (silentStep machine env) boundary absorbs]
  have hl : silentStep machine env (.pending (.local (done u))) =
      PMF.pure (Phase.ready (done u) : P) := by
    simp [silentStep, StoppedProcess.beforeBoundary, boundary, phaseStep, dispatch]
  rw [hl, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ _ _ rfl

example (u : Bool) : nextEpoch machine env (answered u) = PMF.pure (some (done u)) := by
  rw [nextEpoch, next_halt, PMF.pure_bind]
  rfl

/-- One true query epoch followed by silent native completion has exactly the
actual original unbounded native world law. -/
example : (ObservedProcess.stateLaw (epochStep machine env) 1 (some start)).bind
      (finish machine env) = (PMF.uniformOfFintype Bool).map (fun u => some (done u)) := by
  rw [resume_after_epochs, terminal_law]

private theorem diverging_ready : silentStep diverging env (.ready start) =
    PMF.pure localCheckpoint := by
  have hi (bit : Bool) : instruction diverging start bit = .local start := by
    change instruction machine start false = .local start
    exact wait_instruction false
  simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
    NativeUnboundedExecution.halted, show start.config.tapes.state = some .wait from rfl,
    reduceCtorEq, ite_false, phaseStep, Option.isNone_some, Bool.false_eq_true,
    prepare, PMF.map_comp, Function.comp_def, hi]
  exact PMF.map_const _ _

private theorem diverging_local : silentStep diverging env localCheckpoint =
    PMF.pure (.ready start) := by
  change silentStep machine env localCheckpoint = _
  exact silent_local

/-- An actual infinite local loop never selects an oracle or halts. Its missing
first-boundary mass is retained as silent divergence, not a halt token. -/
theorem silent_divergence : seek diverging env start = PMF.pure none := by
  classical
  have hc (n : ℕ) :
      ObservedProcess.stateLaw (silentStep diverging env) n (.ready start) =
        PMF.pure (if n % 2 = 0 then .ready start else localCheckpoint) ∧
      ObservedProcess.stateLaw (silentStep diverging env) n localCheckpoint =
        PMF.pure (if n % 2 = 0 then localCheckpoint else .ready start) := by
    induction n with
    | zero => simp [ObservedProcess.stateLaw]
    | succ n ih =>
      constructor
      · rw [StoppedProcess.stateLaw_succ_left, diverging_ready, PMF.pure_bind, ih.2]
        by_cases hn : n % 2 = 0
        · have hs : (n + 1) % 2 = 1 := by omega
          simp [hn, hs]
        · have hs : (n + 1) % 2 = 0 := by omega
          simp [hn, hs]
      · rw [StoppedProcess.stateLaw_succ_left, diverging_local, PMF.pure_bind, ih.1]
        by_cases hn : n % 2 = 0
        · have hs : (n + 1) % 2 = 1 := by omega
          simp [hn, hs]
        · have hs : (n + 1) % 2 = 0 := by omega
          simp [hn, hs]
  apply StoppedProcess.option_ext
  intro phase
  have hz (n : ℕ) : StoppedProcess.stopped (silentStep diverging env) boundary n
      (.ready start) phase = 0 := by
    by_cases hr : phase = .ready start
    · subst phase
      simp [StoppedProcess.stopped, boundary, NativeUnboundedExecution.halted, start,
        MultiTapeMachine.initialConfig, Cfg.init, machine]
    by_cases hl : phase = localCheckpoint
    · subst phase
      simp [StoppedProcess.stopped, boundary, localCheckpoint]
    simp only [StoppedProcess.stopped, (hc n).1]
    split_ifs <;> simp [PMF.pure_apply, hr, hl]
  change (⨆ n, StoppedProcess.stopped (silentStep diverging env) boundary n
    (.ready start) phase) = _
  simp [hz, PMF.pure_apply]

section TwoQuery
local notation "om" => CslibFrontierTests.NativeOpenExecution.machine
local notation "oe" => CslibFrontierTests.NativeOpenExecution.env

open CslibFrontierTests.NativeOpenExecution in
/-- The actual second query is reached after its native query-writing action,
retaining the original work bit, first reply and full oracle state. -/
example (b u : Bool) : seek om oe (prepared b u) =
    PMF.pure (some (.pending (.query (prepared b u) () .finish))) := by
  apply seek_query
  · change (some CslibFrontierTests.NativeOpenExecution.Control.second) ≠ none
    simp
  · intro bit
    rfl

open CslibFrontierTests.NativeOpenExecution in
/-- The epoch dispatch preserves the response correlated through oracle memory,
with its query-dependent charge and duration on the very same joint record. -/
example (b u : Bool) : nextEpoch om oe (prepared b u) =
    PMF.pure (some (answeredAgain b u)) := by
  have hs : seek om oe (prepared b u) =
      PMF.pure (some (.pending (.query (prepared b u) () .finish))) := by
    apply seek_query
    · change (some CslibFrontierTests.NativeOpenExecution.Control.second) ≠ none
      simp
    · intro bit
      rfl
  rw [nextEpoch, hs, PMF.pure_bind]
  simp [respond, dispatch, CslibFrontierTests.NativeOpenExecution.env, prepared,
    CslibFrontierTests.NativeOpenExecution.answered, drawn,
    CslibFrontierTests.NativeOpenExecution.start, CslibFrontierTests.NativeOpenExecution.machine,
    CslibFrontierTests.NativeOpenExecution.action,
    Action.apply,
    MultiTapeMachine.Config.step, MultiTapeMachine.Config.receive, Memory.record, answeredAgain,
    laterReply, MultiTapeMachine.initialConfig]

open CslibFrontierTests.NativeOpenExecution in
example : seek om oe (early true true) = PMF.pure (some (.ready (early true true))) :=
  seek_halted om oe _ rfl

end TwoQuery

end CslibFrontierTests.NativeEpoch
