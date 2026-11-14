/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction.Envelopes
public import CslibFrontierTests.NativeBatchProgram
import CslibFrontier.Probability.Conditioning.Map
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Actual accepted native batches reveal a latent invoice bit

The shared native program writes the genuine two-bit batch packet, receives one
accepted singleton-cover receipt, and halts with its covering output. The source
starts with a fair latent bit: both trajectories return the same family at the
same physical time, but charge two or four tokens. The complete analytical
Exchange therefore identifies the latent source state. Native code receives only
replyOf that same receipt. No packet, epoch law or source posterior is assumed.

The actual observation before the first response has invoice mean three. Its
positive mass and the primitive empty-history source mean are derived separately;
the fixed-source envelope theorem then recovers the native conditional lower bound.
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

private theorem source_draw_initial (s : Bool) :
    ConcurrentBatch.Interaction.draw limits sample s request = PMF.pure (receipt s, s) := by
  simp [ConcurrentBatch.Interaction.draw, ConcurrentBatch.Interaction.Request.restore,
    sample, request, receipt, ConcurrentBatch.initial, NativeBatchSingleton.limits]

private theorem admit_first {P : Type} (s : P) :
    admit limits (ConcurrentBatch.initial s) (encodeBatch batch) = some batch := by
  simp [admit, decodeBatch_encode, ConcurrentBatch.initial, NativeBatchSingleton.limits]

private theorem seek_initial {P : Type} (sampler : Sampler 1 P) (s : P) :
    seekSourceFrom limits sampler machine
      (some (.ready ⟨machine.initialConfig [], ⟨ConcurrentBatch.initial s, []⟩⟩)) =
      PMF.pure (some (.pending (.query (world (some 2) (encodeBatch batch) [] []
        ⟨ConcurrentBatch.initial s, []⟩) () 3))) := by
  exact NativeBatchProgram.seek_first _ _ (admit_first s)

private theorem request_initial : NativeBatch.Interaction.request limits
    (some (.pending (.query
      (world (some 2) (encodeBatch batch) [] [] ⟨ConcurrentBatch.initial (), []⟩) () 3))) =
    some request := by
  change (admit limits (ConcurrentBatch.initial ()) (encodeBatch batch)).map _ = _
  rw [admit_first]
  rfl

private theorem first_step (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state0 s) = PMF.pure (state1 s) := by
  simp only [InteractionProcess.step, actualPolicy, actualSource, NativeBatch.Interaction.policy,
    state0]
  rw [seek_initial]
  simp only [PMF.pure_map, PMF.pure_bind, request_initial]
  simp [ConcurrentBatch.Interaction.source, source_draw_initial,
    NativeBatch.Interaction.advance, phaseStep, dispatch, NativeBatchProgram.world,
    ConcurrentBatch.initial, dummyMemory, state1, history, Config.receive,
    Function.update_eq_const_of_subsingleton]
  rfl

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

private theorem average_invoice :
    (∑' s, initial s * Trace.charge (some (receipt s))) = 3 := by
  rw [tsum_fintype, Fintype.sum_bool]
  norm_num [initial, PMF.uniformOfFintype_apply, Trace.charge,
    (receipt_resources false).1, (receipt_resources true).1]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

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

/-- Original native prior before the actual first accepted batch. -/
def prior0 : PMF (Trace.State 1 0 Bool (Fin 4) []) := initial.bind fun s =>
  Trace.law limits sample machine 0
    ⟨machine.initialConfig [], ⟨ConcurrentBatch.initial s, []⟩⟩

/-- Concrete native checkpoint selected before the source returns either invoice. -/
def selected0 (s : Bool) : Quantitative.Selected 1 0 Bool (Fin 4) [] :=
  ⟨Trace.initial ⟨machine.initialConfig [], ⟨ConcurrentBatch.initial s, []⟩⟩,
    some (.pending (.query (world (some 2) (encodeBatch batch) [] []
      ⟨ConcurrentBatch.initial s, []⟩) () 3))⟩

/-- The actual positive-mass first-batch observation contains no future invoice information. -/
def observation0 : Quantitative.Observation 1 := ⟨[], some ([], some batch)⟩

private theorem select_zero : Quantitative.select limits sample machine prior0 =
    initial.map selected0 := by
  simp only [Quantitative.select, prior0, Trace.law, ObservedProcess.stateLaw,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    Trace.initial]
  change initial.bind _ = initial.bind (fun s => PMF.pure (selected0 s))
  apply congrArg initial.bind
  funext s
  rw [seek_initial, PMF.pure_bind]
  rfl

private theorem observe_selected0 (s : Bool) :
    Quantitative.observe limits (selected0 s) = observation0 := by
  change (⟨[], (admit limits (ConcurrentBatch.initial s) (encodeBatch batch)).map
    (fun b => ([], some b))⟩ : Quantitative.Observation 1) = _
  rw [admit_first]
  rfl

/-- The observation is selected with probability one by actual native silent execution. -/
theorem observed_zero :
    (Quantitative.select limits sample machine prior0).map (Quantitative.observe limits) =
      PMF.pure observation0 := by
  rw [select_zero, PMF.map_comp]
  have he : Quantitative.observe limits ∘ selected0 = (fun _ => observation0) := by
    funext s
    exact observe_selected0 s
  rw [he]
  exact PMF.map_const _ _

/-- Thus the conditional invoice computation is made at an actual positive-probability batch. -/
theorem observation0_support : observation0 ∈
    ((Quantitative.select limits sample machine prior0).map
      (Quantitative.observe limits)).support := by
  rw [observed_zero]
  simp

private theorem conditional_zero : Quantitative.conditional limits sample machine prior0
    observation0 = prior0.bind (Trace.step limits sample machine) := by
  have he := Quantitative.selection_factor limits sample machine prior0
  rw [observed_zero, PMF.pure_bind] at he
  exact he

private theorem next_zero : prior0.bind (Trace.step limits sample machine) =
    initial.map (fun s => NativeBatch.Interaction.trace (state1 s)) := by
  have he := congrArg (PMF.map NativeBatch.Interaction.trace) execution_one
  rw [NativeBatch.Interaction.execution_trace, PMF.map_comp] at he
  simpa only [prior0, Trace.law, ObservedProcess.stateLaw, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def] using he

/-- Actual selected invoice mean before either source realization is exactly three tokens. -/
theorem conditional_invoice_mean :
    Quantitative.conditionalMean limits sample machine prior0 observation0 Trace.charge = 3 := by
  simp only [Quantitative.conditionalMean, Quantitative.mean, conditional_zero, next_zero,
    PMF.tsum_map_mul, Quantitative.newest, NativeBatch.Interaction.trace, state1, history,
    List.map_cons, List.map_nil, List.headD_cons, Trace.charge]
  exact average_invoice

private def view0 : NativeBatch.Interaction.Selection 1 0 Unit (Fin 4) [] :=
  ⟨[], some request, some (.pending (.query
    (world (some 2) (encodeBatch batch) [] [] ⟨ConcurrentBatch.initial (), []⟩) () 3)), ()⟩

private theorem query_law_zero : actualPolicy.queryLaw [] =
    PMF.pure ((some request), view0.policyState) := by
  simp only [InteractionProcess.Policy.queryLaw, InteractionProcess.Policy.filter_nil,
    actualPolicy, NativeBatch.Interaction.policy, PMF.pure_bind]
  rw [seek_initial]
  simp only [PMF.pure_map, request_initial]
  rfl

private theorem selectionViews_zero : NativeBatch.Interaction.selectionViews limits sample initial
    machine (machine.initialConfig []) 0 = PMF.pure view0 := by
  rw [NativeBatch.Interaction.selectionViews, InteractionProcess.selectionLaw_factorization]
  simp only [InteractionProcess.historyLaw, PMF.seqProcess, PMF.seqHistory_zero,
    PMF.pure_map, PMF.pure_bind]
  change ((actualPolicy.queryLaw []).bind _).map _ = _
  rw [query_law_zero, PMF.pure_bind]
  simp only [PMF.map_comp, Function.comp_def, InteractionProcess.Selected.policyView]
  exact PMF.map_const _ _

/-- The primitive fixed source has the same three-token filtered invoice mean at empty history. -/
theorem source_invoice_mean :
    (∑' pair, ((ConcurrentBatch.Interaction.source limits sample initial).draw []
      (some request)) pair * Trace.charge pair.1) = 3 := by
  classical
  rw [InteractionProcess.Source.draw, InteractionProcess.Source.filter_nil]
  rw [PMF.tsum_bind_mul]
  simp only [ConcurrentBatch.Interaction.source, source_draw_initial, PMF.pure_map]
  simpa only [PMF.pure_apply, ite_mul, zero_mul, one_mul, tsum_ite_eq] using average_invoice

/-- A primitive fixed-source lower envelope yields the actual pre-response native invoice bound. -/
theorem transferred_invoice_lower_bound :
    3 ≤ Quantitative.conditionalMean limits sample machine prior0 observation0 Trace.charge := by
  change 3 ≤ History.conditionalMean limits sample machine prior0 observation0
    (fun _ record => Trace.charge record)
  apply NativeBatch.Interaction.conditional_reward_ge limits sample initial machine
    (machine.initialConfig []) 0 observation0 (fun _ record => Trace.charge record) 3
    observation0_support
  intro view hv _
  rw [selectionViews_zero, PMF.mem_support_pure_iff] at hv
  subst view
  change 3 ≤ ∑' pair, ((ConcurrentBatch.Interaction.source limits sample initial).draw []
    (some request)) pair * Trace.charge pair.1
  exact source_invoice_mean.ge

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
