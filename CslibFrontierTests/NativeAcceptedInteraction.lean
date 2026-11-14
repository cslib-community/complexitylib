/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction
public import CslibFrontierTests.NativeBatchProgram
import CslibFrontier.Probability.Conditioning.Map
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual accepted native batches reveal a latent invoice bit

The shared native program writes the genuine two-bit batch packet, receives one
accepted singleton-cover receipt, and halts with its covering output. The source
starts with a fair latent bit: both trajectories return the same family at the
same physical time, but charge two or four tokens. The complete analytical
Exchange therefore identifies the latent source state. Native code receives only
replyOf that same receipt. No packet, epoch law or source posterior is assumed.
-/

public section
noncomputable section
namespace CslibFrontierTests.NativeAcceptedInteraction
open Cslib.Probability Turing Turing.MultiTapeMachine NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle ConcurrentBatch NativeBatch
open CslibFrontierTests.NativeBatchSingleton (limits batch)
open CslibFrontierTests.NativeBatchProgram (machine world)
open scoped NNReal ENNReal

/-- Persistent hidden source state, independent of the actual native program. -/
def initial : PMF Bool := PMF.uniformOfFintype Bool

/-- Equal covering words and stop times, with distinct actual token invoices. -/
def path (s : Bool) : CallTrace :=
  ⟨some (1, encodeFamily ({0} : Finset (Fin 1))), fun _ => if s then 2 else 4,
    by intro _ _ _; exact le_rfl⟩

/-- The same source sampler is used before and after native private computation. -/
def sample : Sampler 1 Bool := fun server _ =>
  PMF.pure (fun _ => path server.privateState, server.privateState)

/-- The full actual receipt from the unique accepted source opportunity. -/
def receipt (s : Bool) : Exchange 1 := observe limits 2 batch (fun _ => path s)

/-- First admitted public snapshot and batch, before any source response. -/
def request : ConcurrentBatch.Interaction.Request 1 := ⟨ConcurrentBatch.initial (), batch⟩

/-- Complete first accepted observation, including analytical timing metadata. -/
def history (s : Bool) :
    List (Option (ConcurrentBatch.Interaction.Request 1) × Option (Exchange 1)) :=
  [(some request, some (receipt s))]

/-- Real native/server memory after the source has committed that same receipt. -/
def realMemory (s : Bool) : Memory Unit (ServerState 1 Bool) :=
  (⟨ConcurrentBatch.initial s, []⟩ : Memory Unit (ServerState 1 Bool)).record
    ((), encodeBatch batch) (replyOf (receipt s)) (commit (ConcurrentBatch.initial s) (receipt s) s)

private def dummyMemory (s : Bool) : Memory Unit (ServerState 1 Unit) :=
  (⟨ConcurrentBatch.initial (), []⟩ : Memory Unit (ServerState 1 Unit)).record
    ((), encodeBatch batch) (replyOf (receipt s))
    (commit (ConcurrentBatch.initial ()) (receipt s) ())

private def state0 (s : Bool) : NativeBatch.Interaction.State 1 0 Bool (Fin 4) [] :=
  ⟨[], some (.ready ⟨machine.initialConfig [], ⟨ConcurrentBatch.initial (), []⟩⟩), s⟩
/-- Actual separated state after the accepted receipt is installed. -/
def state1 (s : Bool) : NativeBatch.Interaction.State 1 0 Bool (Fin 4) [] :=
  ⟨history s, some (.ready (world (some 3) [] (replyOf (receipt s)).word [] (dummyMemory s))), s⟩
/-- Actual separated state after local output and committed halt. -/
def state2 (s : Bool) : NativeBatch.Interaction.State 1 0 Bool (Fin 4) [] :=
  ⟨(none, none) :: history s,
    some (.ready (world none [] (replyOf (receipt s)).word [true] (dummyMemory s))), s⟩

private def actualPolicy := NativeBatch.Interaction.policy limits machine (machine.initialConfig [])
private def actualSource := ConcurrentBatch.Interaction.source limits sample initial

private theorem admit_first :
    admit limits (ConcurrentBatch.initial ()) (encodeBatch batch) = some batch := by
  simp [admit, decodeBatch_encode, ConcurrentBatch.initial, NativeBatchSingleton.limits]

private theorem first_step (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state0 s) = PMF.pure (state1 s) := by
  simp only [InteractionProcess.step, actualPolicy, actualSource, NativeBatch.Interaction.policy,
    state0]
  have hs : seekSourceFrom limits NativeBatch.Interaction.silentSampler machine
      (some (.ready ⟨machine.initialConfig [], ⟨ConcurrentBatch.initial (), []⟩⟩)) =
      PMF.pure (some (.pending (.query
        (world (some 2) (encodeBatch batch) [] [] ⟨ConcurrentBatch.initial (), []⟩) () 3))) := by
    exact NativeBatchProgram.seek_first _ _ admit_first
  rw [hs]
  have hr : NativeBatch.Interaction.request limits
      (some (.pending (.query
        (world (some 2) (encodeBatch batch) [] [] ⟨ConcurrentBatch.initial (), []⟩) () 3))) =
      some request := by
    change (admit limits (ConcurrentBatch.initial ()) (encodeBatch batch)).map _ = _
    rw [admit_first]
    rfl
  simp only [PMF.pure_map, PMF.pure_bind, hr]
  cases s <;> simp [ConcurrentBatch.Interaction.source, ConcurrentBatch.Interaction.draw,
    ConcurrentBatch.Interaction.Request.restore, request, sample, receipt, path,
    NativeBatch.Interaction.advance,
    phaseStep, dispatch, NativeBatchProgram.world, ConcurrentBatch.initial,
    dummyMemory, state1, history, Config.receive, Function.update_eq_const_of_subsingleton,
    NativeBatchSingleton.limits]
  all_goals rfl

private theorem last_step (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state1 s) = PMF.pure (state2 s) := by
  simp only [InteractionProcess.step, actualPolicy, actualSource, NativeBatch.Interaction.policy,
    state1]
  rw [NativeBatchProgram.seek_output]
  simp [ConcurrentBatch.Interaction.source, NativeBatch.Interaction.request,
    NativeBatch.Interaction.advance, respondSource, phaseStep, state2,
    NativeBatchProgram.world]

/-- The first accepted epoch is derived from actual two-bit packet writing and guarded dispatch. -/
theorem execution_one : NativeBatch.Interaction.execution limits sample initial machine
    (machine.initialConfig []) 1 = initial.map state1 := by
  have hi : InteractionProcess.initialLaw actualPolicy actualSource = initial.map state0 := by
    simp only [InteractionProcess.initialLaw, actualPolicy, actualSource,
      NativeBatch.Interaction.policy, ConcurrentBatch.Interaction.source, PMF.pure_bind]
    rfl
  change InteractionProcess.law actualPolicy actualSource 1 = _
  rw [InteractionProcess.law_succ]
  simp only [InteractionProcess.law, ObservedProcess.stateLaw, PMF.bind_pure, hi,
    Function.comp_def, first_step, PMF.map, PMF.bind_bind, PMF.pure_bind]

/-- The same actual native program halts after its received receipt without another source call. -/
theorem execution_two : NativeBatch.Interaction.execution limits sample initial machine
    (machine.initialConfig []) 2 = initial.map state2 := by
  change InteractionProcess.law actualPolicy actualSource 2 = _
  rw [InteractionProcess.law_succ]
  change (NativeBatch.Interaction.execution limits sample initial machine
    (machine.initialConfig []) 1).bind _ = _
  rw [execution_one, PMF.bind_map]
  simp only [Function.comp_def, last_step, PMF.map]

/-- Each analytical invoice branch is genuinely reached by the native implementation. -/
theorem reached (s : Bool) : history s ∈ ((NativeBatch.Interaction.execution limits sample initial
    machine (machine.initialConfig []) 1).map InteractionProcess.State.history).support := by
  rw [execution_one, PMF.map_comp]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨s, by simp [initial], rfl⟩

/-- Invoices differ while the physical duration and completed family are identical. -/
theorem receipt_resources (s : Bool) :
    (receipt s).tokens = (if s then 2 else 4) ∧ (receipt s).duration = 1 := by
  cases s <;> norm_num [receipt, observe, Exchange.tokens, Exchange.duration,
    batch, active, NativeBatchSingleton.batch, NativeBatchSingleton.limits, path,
    CallTrace.report, CallTrace.stop, CallTrace.response]

private theorem history_injective : Function.Injective history := by
  intro s t h
  have hr : receipt s = receipt t := by
    simpa [history] using h
  have ht := congrArg Exchange.tokens hr
  rw [(receipt_resources s).1, (receipt_resources t).1] at ht
  cases s <;> cases t <;> first | rfl | norm_num at ht

/-- The actual native source posterior is fixed by its received analytical invoice. -/
theorem actual_posterior (s : Bool) :
    (PMF.conditionalSnd ((NativeBatch.Interaction.execution limits sample initial machine
      (machine.initialConfig []) 1).map fun state =>
        (state.history, (state.policyState, state.sourceState))) (history s)).map Prod.snd =
      PMF.pure s := by
  classical
  let joint := (NativeBatch.Interaction.execution limits sample initial machine
    (machine.initialConfig []) 1).map fun state =>
      (state.history, (state.policyState, state.sourceState))
  have hh : history s ∈ (joint.map Prod.fst).support := by
    simpa only [joint, PMF.map_comp, Function.comp_def] using reached s
  rw [← PMF.conditionalSnd_map_snd joint Prod.snd (history s) hh]
  have he : joint.map (fun pair => (pair.1, Prod.snd pair.2)) =
      (PMF.uniformOfFintype Bool).map (fun t => (history t, t)) := by
    dsimp only [joint]
    rw [execution_one]
    simp only [PMF.map_comp, Function.comp_def, initial, state1]
  rw [he]
  have : Nonempty {t : Bool // history t = history s} := ⟨⟨s, rfl⟩⟩
  rw [PMF.conditionalSnd_uniform_map]
  have hf : (Subtype.val : {t : Bool // history t = history s} → Bool) = (fun _ => s) := by
    funext t
    exact history_injective t.property
  rw [hf]
  exact PMF.map_const _ _

/-- The common source filter agrees with this derived actual native posterior. -/
theorem common_filter (s : Bool) :
    (ConcurrentBatch.Interaction.source limits sample initial).filter (history s) = PMF.pure s := by
  rw [← NativeBatch.Interaction.source_posterior limits sample initial machine
    (machine.initialConfig []) 1 (history s) (reached s)]
  exact actual_posterior s

/-- Unbounded native execution has the same covering output and committed real memory. -/
theorem native_terminal :
    (initial.bind fun s => NativeUnboundedExecution.terminal machine (environment limits sample)
      (⟨machine.initialConfig [], ⟨ConcurrentBatch.initial s, []⟩⟩ :
        World 0 (Fin 4) Unit (ServerState 1 Bool) [])) =
      initial.map (fun s =>
        some (world none [] (replyOf (receipt s)).word [true] (realMemory s))) := by
  rw [← NativeBatch.Interaction.execution_terminal]
  change (NativeBatch.Interaction.execution limits sample initial machine
    (machine.initialConfig []) 2).map _ = _
  rw [execution_two, PMF.map_comp]
  rfl

/-- The real native event log carries the invoice and time of the same analytical receipt. -/
theorem native_resources (s : Bool) :
    tokenBill (realMemory s).events = (receipt s).tokens ∧
      elapsed (realMemory s).events = (receipt s).duration := by
  simp [realMemory, Memory.record, tokenBill, elapsed, replyOf]

-- Both hidden states return exactly the same completed original-family word.
example (s : Bool) : (path s).response 1 = some (encodeFamily ({0} : Finset (Fin 1))) := by
  norm_num [path, CallTrace.response]

-- The query packet is actually written; it is not a preloaded response or caller hypothesis.
example : encodeBatch batch = [true, false] := by rfl

end CslibFrontierTests.NativeAcceptedInteraction
