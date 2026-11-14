/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.NativeEpoch.Interaction
public import CslibFrontierTests.NativeInteraction
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.StoppedProcess.Map
import Mathlib.Tactic

/-!
# Actual raw query epochs and billed silent divergence

The ordinary native fixture writes its real query, receives an invoice-bearing
empty reply, and privately randomizes its output. Two actual raw epochs preserve
its joint history, output and real ledger. A second program queries once and then
loops silently forever: its native configuration diverges while its separately
retained source memory still contains the incurred bill and duration.
-/

public section
noncomputable section
namespace CslibFrontierTests.NativeRawEpochs
open Cslib.Probability Turing Turing.MultiTapeMachine Turing.MultiTapeTM
open NativeOpenExecution NativeInterface NativeEpoch
open scoped NNReal ENNReal

namespace Happy
open CslibFrontierTests.NativeInteraction
  (machine reply env initial config realMemory realAfter dummyAfter)

private def before (memory : Memory Unit Unit) : World 0 (Fin 3) Unit Unit [] :=
  ⟨config (some 0) [] [], memory⟩
private def queried (memory : Memory Unit Unit) : World 0 (Fin 3) Unit Unit [] :=
  ⟨config (some 1) [true] [], memory⟩
private def answered (memory : Memory Unit Unit) : World 0 (Fin 3) Unit Unit [] :=
  ⟨config (some 2) [] [], memory⟩
private def done (memory : Memory Unit Unit) (bit : Bool) : World 0 (Fin 3) Unit Unit [] :=
  ⟨config none [] [bit], memory⟩

private theorem seek_first (localEnv : Environment Unit Unit) (memory : Memory Unit Unit) :
    seek machine localEnv (before memory) =
      PMF.pure (some (.pending (.query (queried memory) () 2))) := by
  have hr : silentStep machine localEnv (.ready (before memory)) =
      PMF.pure (.pending (.local (queried memory))) := by
    have hi (bit : Bool) : instruction machine (before memory) bit =
        .local (queried memory) := NativeInteraction.instruction_write memory bit
    have hb : (before memory).config.tapes.state = some 0 := rfl
    simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
      NativeUnboundedExecution.halted, hb, reduceCtorEq, ite_false, phaseStep,
      Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def, hi]
    exact PMF.map_const _ _
  have hl : silentStep machine localEnv (.pending (.local (queried memory))) =
      PMF.pure (.ready (queried memory)) := by
    simp [silentStep, StoppedProcess.beforeBoundary, boundary, phaseStep, dispatch]
  unfold seek
  rw [StoppedProcess.terminal_step, hr, PMF.pure_bind,
    StoppedProcess.terminal_step, hl, PMF.pure_bind]
  change seek machine localEnv (queried memory) = _
  apply seek_query machine localEnv (queried memory) () 2
  · simp [NativeUnboundedExecution.halted, queried, config]
  · intro bit
    rfl

private theorem seek_last (localEnv : Environment Unit Unit) (memory : Memory Unit Unit) :
    seek machine localEnv (answered memory) =
      (PMF.uniformOfFintype Bool).map fun bit => some (.ready (done memory bit)) := by
  have hr : silentStep machine localEnv (.ready (answered memory)) =
      (PMF.uniformOfFintype Bool).map fun bit => .pending (.local (done memory bit)) := by
    have hi (bit : Bool) : instruction machine (answered memory) bit =
        .local (done memory bit) := NativeInteraction.instruction_output memory bit
    have hb : (answered memory).config.tapes.state = some 2 := rfl
    simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
      NativeUnboundedExecution.halted, hb, reduceCtorEq, ite_false, phaseStep,
      Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def, hi]
  unfold seek
  rw [StoppedProcess.terminal_step, hr, PMF.bind_map]
  change (PMF.uniformOfFintype Bool).bind _ = _
  rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro bit _
  simp only [Function.comp_def]
  rw [StoppedProcess.terminal_step]
  have hl : silentStep machine localEnv (.pending (.local (done memory bit))) =
      PMF.pure (.ready (done memory bit)) := by
    simp [silentStep, StoppedProcess.beforeBoundary, boundary, phaseStep, dispatch]
  rw [hl, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ _ _ rfl

/-- Two raw epochs contain one actual query, followed by local completion. -/
def history (s : Bool) : List (Option (Unit × List Bool) × Reply) :=
  [(none, reply false), (some ((), [true]), reply s)]

private def state0 (s : Bool) : NativeEpoch.Interaction.State 0 (Fin 3) Unit Bool [] :=
  ⟨[], some (.ready (before ⟨(), []⟩)), realMemory s⟩
private def state1 (s : Bool) : NativeEpoch.Interaction.State 0 (Fin 3) Unit Bool [] :=
  ⟨[(some ((), [true]), reply s)], some (.ready (answered (dummyAfter s))), realAfter s⟩
private def state2 (s bit : Bool) : NativeEpoch.Interaction.State 0 (Fin 3) Unit Bool [] :=
  ⟨history s, some (.ready (done (dummyAfter s) bit)), realAfter s⟩
private def actualPolicy := NativeEpoch.Interaction.policy machine (machine.initialConfig [])
private def actualSource := NativeInterface.Interaction.source env initial

private theorem initial_law : InteractionProcess.initialLaw actualPolicy actualSource =
    (PMF.uniformOfFintype Bool).map state0 := by
  simp only [InteractionProcess.initialLaw, actualPolicy, actualSource,
    NativeEpoch.Interaction.policy, NativeInterface.Interaction.source,
    PMF.pure_bind, NativeInteraction.initial, PMF.map_comp, Function.comp_def]
  rfl

private theorem first_step (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state0 s) = PMF.pure (state1 s) := by
  simp only [InteractionProcess.step, actualPolicy, actualSource, NativeEpoch.Interaction.policy,
    state0, Option.map_some, worldOf, seekFrom]
  rw [seek_first]
  cases s <;> simp [NativeInterface.Interaction.source, NativeInterface.Interaction.response,
    state1, answered, NativeEpoch.Interaction.selectedRequest, NativeInterface.Interaction.request,
    respond, dispatch,
    env, realMemory, realAfter, dummyAfter, reply, queried, config, Config.receive,
    Function.update_eq_const_of_subsingleton, PMF.map_comp, Function.comp_def]
  all_goals rfl

private theorem last_step (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state1 s) =
      (PMF.uniformOfFintype Bool).map (state2 s) := by
  simp [InteractionProcess.step, actualPolicy, actualSource,
    NativeEpoch.Interaction.policy, NativeInterface.Interaction.source,
    NativeInterface.Interaction.response, state1, state2, history, seekFrom,
    worldOf, seek_last, NativeEpoch.Interaction.selectedRequest, respond,
    PMF.map, Function.comp_def, reply]

private theorem process_two : InteractionProcess.law actualPolicy actualSource 2 =
    (PMF.uniformOfFintype Bool).bind fun s =>
      (PMF.uniformOfFintype Bool).map (state2 s) := by
  rw [InteractionProcess.law_succ, InteractionProcess.law_succ]
  simp only [InteractionProcess.law, ObservedProcess.stateLaw, PMF.bind_pure, initial_law,
    PMF.bind_map, PMF.bind_bind, Function.comp_def, first_step, PMF.pure_bind, last_step]

/-- Raw stopping derives the exact joint random output and invoice-bearing source history. -/
theorem execution_two :
    NativeEpoch.Interaction.execution machine env initial (machine.initialConfig []) 2 =
      (PMF.uniformOfFintype Bool).bind fun s =>
        (PMF.uniformOfFintype Bool).map fun bit =>
          (history s, (⟨some (config none [] [bit]), realAfter s⟩ :
            NativeEpoch.Interaction.Outcome 0 (Fin 3) Unit Bool [])) := by
  change (InteractionProcess.law actualPolicy actualSource 2).map
    (fun state => (state.history, NativeEpoch.Interaction.outcome state)) = _
  rw [process_two]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

/-- Every hidden-bit branch is actually reached after the real query and local completion. -/
theorem reached (s : Bool) :
    history s ∈ ((NativeEpoch.Interaction.execution machine env initial
      (machine.initialConfig []) 2).map Prod.fst).support := by
  rw [execution_two, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨s, by simp, ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨false, by simp, rfl⟩

private theorem common_filter (s : Bool) :
    (NativeInterface.Interaction.source env initial).filter (history s) =
      PMF.pure (realAfter s) := by
  have he : (NativeInterface.Interaction.source env initial).filter (history s) =
      (NativeInterface.Interaction.source env initial).filter (NativeInteraction.history s) := by
    have hz : reply false = (⟨[], 0, 0⟩ : Reply) := rfl
    rw [history, NativeInteraction.history, hz, NativeInterface.Interaction.filter_none,
      NativeInterface.Interaction.filter_none]
    rw [InteractionProcess.Source.filter_cons, InteractionProcess.Source.filter_cons]
    simp only [InteractionProcess.Source.draw, NativeInterface.Interaction.filter_none]
    rfl
  exact he.trans (NativeInteraction.common_source_filter s)

/-- Raw epoch conditioning uses the same source filter as actual native instruction execution. -/
theorem source_posterior (s : Bool) :
    (PMF.conditionalSnd (NativeEpoch.Interaction.execution machine env initial
      (machine.initialConfig []) 2) (history s)).map
      NativeEpoch.Interaction.Outcome.memory = PMF.pure (realAfter s) := by
  rw [NativeEpoch.Interaction.source_posterior machine env initial (machine.initialConfig [])
    2 (history s) (reached s), common_filter]

/-- Halting output coins do not change the actual source bill or physical duration. -/
example (s bit : Bool) :
    (⟨some (config none [] [bit]), realAfter s⟩ :
      NativeEpoch.Interaction.Outcome 0 (Fin 3) Unit Bool []).world =
      some ⟨config none [] [bit], realAfter s⟩ ∧
      tokenBill (realAfter s).events = (reply s).tokens ∧
      elapsed (realAfter s).events = (reply s).duration := by
  simp [NativeEpoch.Interaction.Outcome.world, realAfter, realMemory,
    Memory.record, tokenBill, elapsed]

end Happy

namespace Diverging

/-- Query immediately, then execute an infinite private local identity loop. -/
def machine : MultiTapePTM 0 Bool Bool Unit where
  initial := false
  tr c _ _ _ _ := if c then .step
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }
    (fun _ => none) (fun _ => 0) else .query () true

/-- The actual call incurs a nonzero bill before private computation diverges. -/
def fee : Reply := ⟨[], 2, 1⟩
/-- A fixed real source shared by the query and the later silent computation. -/
def env : Environment Unit Unit := fun _ _ => PMF.pure (fee, ())
/-- Initially no source invoice has been incurred. -/
def initial : PMF (Memory Unit Unit) := PMF.pure ⟨(), []⟩
/-- The actual completed raw call remains in the external ledger. -/
def paid : Memory Unit Unit := (⟨(), []⟩ : Memory Unit Unit).record ((), []) fee ()
/-- Public query followed by silent private divergence. -/
def history : List (Option (Unit × List Bool) × Reply) :=
  [(none, ⟨[], 0, 0⟩), (some ((), []), fee)]

private def loopConfig : Config 0 Bool Bool Unit [] :=
  { machine.initialConfig [] with
    tapes := { (machine.initialConfig []).tapes with state := some true } }
private def loopWorld (memory : Memory Unit Unit) : World 0 Bool Unit Unit [] :=
  ⟨loopConfig, memory⟩

private theorem instruction_loop (memory : Memory Unit Unit) (bit : Bool) :
    instruction machine (loopWorld memory) bit = .local (loopWorld memory) := by
  simp only [instruction, loopWorld, loopConfig, machine, MultiTapeMachine.initialConfig,
    Cfg.init, ite_true]
  simp only [Config.step, Action.apply, moveInputPos_zero, Option.toList_none,
    List.append_nil, SignType.coe_zero, add_zero]
  congr 4 <;> funext i <;> exact Fin.elim0 i

private def cycleStep (b : Bool) : PMF Bool := PMF.pure (!b)
private def embed (memory : Memory Unit Unit) (b : Bool) : Phase 0 Bool Unit Unit [] :=
  if b then .pending (.local (loopWorld memory)) else .ready (loopWorld memory)

private theorem silent_ready (memory : Memory Unit Unit) :
    silentStep machine env (.ready (loopWorld memory)) =
      PMF.pure (.pending (.local (loopWorld memory))) := by
  have hb : (loopWorld memory).config.tapes.state = some true := rfl
  simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
    NativeUnboundedExecution.halted, hb, reduceCtorEq, ite_false, phaseStep,
    Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def,
    instruction_loop]
  exact PMF.map_const _ _

private theorem silent_pending (memory : Memory Unit Unit) :
    silentStep machine env (.pending (.local (loopWorld memory))) =
      PMF.pure (.ready (loopWorld memory)) := by
  simp [silentStep, StoppedProcess.beforeBoundary, boundary, phaseStep, dispatch]

/-- Silent divergence is proved from the actual instruction loop, not assumed as an epoch law. -/
private theorem seek_diverges (memory : Memory Unit Unit) :
    seek machine env (loopWorld memory) = PMF.pure none := by
  have hc : StoppedProcess.terminal cycleStep (fun _ : Bool => False)
      (fun _ h => h.elim) false = PMF.pure none := by
    apply StoppedProcess.option_ext
    intro b
    simp [StoppedProcess.terminal_some, StoppedProcess.terminalMass, StoppedProcess.stopped]
  have he := StoppedProcess.terminal_map cycleStep (fun _ : Bool => False)
    (fun _ h => h.elim) (silentStep machine env) boundary (silent_absorbs machine env)
    (embed memory) (fun b => by
      cases b <;> simp [cycleStep, embed, silent_ready, silent_pending])
    (fun b => by
      cases b <;> simp [embed, boundary, NativeUnboundedExecution.halted,
        loopWorld, loopConfig, machine]) false
  rw [hc, PMF.pure_map] at he
  exact he.symm

private theorem seek_first (localEnv : Environment Unit Unit) :
    seek machine localEnv (⟨machine.initialConfig [], ⟨(), []⟩⟩ : World 0 Bool Unit Unit []) =
      PMF.pure (some (.pending (.query ⟨machine.initialConfig [], ⟨(), []⟩⟩ () true))) := by
  apply seek_query machine localEnv _ () true
  · simp [NativeUnboundedExecution.halted, machine, MultiTapeMachine.initialConfig, Cfg.init]
  · intro bit
    rfl

private def actualPolicy := NativeEpoch.Interaction.policy machine (machine.initialConfig [])
private def actualSource := NativeInterface.Interaction.source env initial
private def state0 : NativeEpoch.Interaction.State 0 Bool Unit Unit [] :=
  ⟨[], some (.ready ⟨machine.initialConfig [], ⟨(), []⟩⟩), ⟨(), []⟩⟩
private def state1 : NativeEpoch.Interaction.State 0 Bool Unit Unit [] :=
  ⟨[(some ((), []), fee)], some (.ready (loopWorld paid)), paid⟩
private def state2 : NativeEpoch.Interaction.State 0 Bool Unit Unit [] :=
  ⟨history, none, paid⟩

private theorem first_step :
    InteractionProcess.step actualPolicy actualSource state0 = PMF.pure state1 := by
  simp only [InteractionProcess.step, actualPolicy, actualSource, NativeEpoch.Interaction.policy,
    state0, Option.map_some, worldOf, seekFrom]
  rw [seek_first]
  simp [NativeInterface.Interaction.source, NativeInterface.Interaction.response, state1,
    NativeEpoch.Interaction.selectedRequest, NativeInterface.Interaction.request,
    respond, dispatch, env, paid, loopWorld,
    loopConfig, Config.receive, machine, MultiTapeMachine.initialConfig, Cfg.init,
    Function.update_eq_const_of_subsingleton, PMF.map_comp, Function.comp_def]
  rfl

private theorem last_step :
    InteractionProcess.step actualPolicy actualSource state1 = PMF.pure state2 := by
  have hs : seek machine (fun _ _ => PMF.pure (⟨[], 0, 0⟩, ())) (loopWorld paid) =
      PMF.pure none := by
    rw [← seek_independent machine env, seek_diverges]
  simp [InteractionProcess.step, actualPolicy, actualSource, NativeEpoch.Interaction.policy,
    NativeInterface.Interaction.source, NativeInterface.Interaction.response, state1, state2,
    history, seekFrom, worldOf, hs, NativeEpoch.Interaction.selectedRequest, respond,
    PMF.map_comp, Function.comp_def]

/-- The real ledger survives an actual silent divergent second epoch. -/
theorem execution_two : NativeEpoch.Interaction.execution machine env initial
    (machine.initialConfig []) 2 = PMF.pure
      (history, (⟨none, paid⟩ : NativeEpoch.Interaction.Outcome 0 Bool Unit Unit [])) := by
  have hi : InteractionProcess.initialLaw actualPolicy actualSource = PMF.pure state0 := by
    simp [InteractionProcess.initialLaw, actualPolicy, actualSource, NativeEpoch.Interaction.policy,
      NativeInterface.Interaction.source, initial, state0]
  have hl : InteractionProcess.law actualPolicy actualSource 2 = PMF.pure state2 := by
    rw [InteractionProcess.law_succ, InteractionProcess.law_succ]
    simp only [InteractionProcess.law, ObservedProcess.stateLaw, PMF.bind_pure,
      hi, PMF.pure_bind, first_step, last_step]
  change (InteractionProcess.law actualPolicy actualSource 2).map
    (fun state => (state.history, NativeEpoch.Interaction.outcome state)) = _
  rw [hl, PMF.pure_map]
  rfl

/-- The original native program actually diverges after its billed query. -/
theorem terminal_diverges : NativeUnboundedExecution.terminal machine env
    (⟨machine.initialConfig [], ⟨(), []⟩⟩ : World 0 Bool Unit Unit []) = PMF.pure none := by
  have he := NativeEpoch.Interaction.execution_resume machine env initial
    (machine.initialConfig []) 2
  rw [execution_two, PMF.pure_bind] at he
  simpa only [NativeEpoch.Interaction.Outcome.world, Option.map_none, finish,
    initial, PMF.pure_bind] using he.symm

/-- The retained source posterior remains the paid ledger after private divergence. -/
example :
    (PMF.conditionalSnd (NativeEpoch.Interaction.execution machine env initial
      (machine.initialConfig []) 2) history).map NativeEpoch.Interaction.Outcome.memory =
      PMF.pure paid := by
  rw [execution_two]
  have he := PMF.conditionalSnd_bind_pair (PMF.pure history)
    (fun _ => PMF.pure (⟨none, paid⟩ : NativeEpoch.Interaction.Outcome 0 Bool Unit Unit []))
    history (by simp)
  simpa only [PMF.pure_bind, PMF.pure_map] using congrArg (PMF.map
    NativeEpoch.Interaction.Outcome.memory) he

/-- Divergence is not reported as a halted world, and still has its actual two-token bill. -/
example :
    (⟨none, paid⟩ : NativeEpoch.Interaction.Outcome 0 Bool Unit Unit []).world = none ∧
      tokenBill paid.events = 2 ∧ elapsed paid.events = 1 := by
  norm_num [NativeEpoch.Interaction.Outcome.world, paid, Memory.record, tokenBill, elapsed, fee]

end Diverging

end CslibFrontierTests.NativeRawEpochs
