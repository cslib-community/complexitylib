/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Memory
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Trace
public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Interaction
import CslibFrontier.Probability.PMF.ObservedProcess.Map
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual accepted native epochs with a fixed enriched source

The external accounting follows [Wang2027], model PDF p. 5. This connection uses
discrete PMF source laws, without requiring finite response support.

Actual silent native computation, including rejected transactions, selects the
next accepted batch before its response is sampled. The private policy stores
native checkpoints with dummy latent state; the fixed source stores only real
latent state. Requests carry the accepted public snapshot and selected batch.

The analytical reply is the complete `Exchange`, including per-call stop times.
Native control receives only `replyOf`. Posterior claims therefore condition on
the enriched analytical history, not merely the machine-readable transcript.
The generated native policies obey the original protocol; arbitrary interaction
policies could forge snapshots and are not certified native competitors.

## Main definitions

* `policy`, `execution`: actual unbounded accepted selection and separated execution.
* `trace`: original native trace readback with accepted receipts retained on divergence.

## Main results

* `step_trace`, `execution_trace`: exact original native accepted-trace laws.
* `execution_terminal`: original unbounded terminal law at the source budget horizon.
* `execution_ledger_bound`: actual turn, deadline and nonreuse feasibility.
* `execution_histories`, `source_posterior`: one shared enriched-history source filter.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Interaction
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
open StochasticOracle.ConcurrentBatch.Interaction (Request)
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- Separated actual native state with real latent source state retained even
when the optional private checkpoint diverges. -/
abbrev State (n k : ℕ) (Private Control : Type) (input : List Bool) :=
  InteractionProcess.State (Option (Request n)) (Option (Exchange n))
    (Option (Phase k Control Unit (ServerState n Unit) input)) Private

/-- A silent placeholder sampler. Actual silent selection holds admitted queries
before sampling and rejects invalid requests without consulting this sampler. -/
def silentSampler : Sampler n Unit := fun _ _ =>
  PMF.pure (fun _ => ⟨none, fun _ => 0, fun _ _ _ => le_rfl⟩, ())

/-- The actual selected packet and public accepted snapshot, without native tapes,
raw event logs or latent source state. Halt and divergence make no request. -/
@[expose] def request (limits : Limits n) :
    Option (Phase k Control Unit (ServerState n Unit) input) → Option (Request n)
  | some (.pending (.query world _ _)) =>
      (admit limits world.memory.privateState (world.config.channels ()).queryBuffer).map
        fun batch => ⟨world.memory.privateState, batch⟩
  | _ => none

/-- Native dispatch receives only the actual encoded reply. The enriched receipt
updates the dummy accepted ledger without exposing latent state to native control. -/
@[expose] def advance (limits : Limits n) (machine : MultiTapePTM k Bool Control Unit)
    (hit : Option (Phase k Control Unit (ServerState n Unit) input))
    (response : Option (Exchange n)) :
    PMF (Option (Phase k Control Unit (ServerState n Unit) input)) :=
  match response with
  | none => respondSource limits silentSampler machine hit
  | some receipt => hit.elim (PMF.pure none) fun phase =>
      (phaseStep machine (fun _ memory =>
        PMF.pure (replyOf receipt, commit memory.privateState receipt ())) phase).map some

/-- Actual unbounded accepted-batch selection followed by native response dispatch. -/
@[expose] def policy (limits : Limits n) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) :
    InteractionProcess.Policy (Option (Request n)) (Option (Exchange n))
      (Option (Phase k Control Unit (ServerState n Unit) input)) where
  initial := PMF.pure (some (.ready ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial (), []⟩⟩))
  choose _ current := (seekSourceFrom limits silentSampler machine current).map
    fun hit => (request limits hit, hit)
  update _ hit _ response := advance limits machine hit response

/-- Replace only dummy latent state, preserving the complete native configuration,
accepted public ledger and every finite raw event. -/
@[expose] def hidden (state : State n k Private Control input) :
    Option (Phase k Control Unit (ServerState n Private) input) :=
  state.policyState.map
    (Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate fun _ => state.sourceState)))

/-- Actual native trace readback; accepted receipts survive private divergence
through the external analytical history, without recovering an infinite raw log. -/
@[expose] def trace (state : State n k Private Control input) :
    Trace.State n k Private Control input :=
  ⟨hidden state, state.history.map Prod.snd⟩

/-- The actual enriched execution law, from independent private initialization. -/
@[expose] def execution (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ) :
    PMF (State n k Private Control input) :=
  InteractionProcess.law (policy limits machine config)
    (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs

private theorem response_trace (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (state : State n k Private Control input)
    (hit : Option (Phase k Control Unit (ServerState n Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) :
    ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).step
      state.history state.sourceState (request limits hit)).bind
      (fun (response, nextPrivate) => (advance limits machine hit response).map fun next =>
        (⟨next.map (Phase.mapMemory (Memory.mapPrivate
          (ServerState.mapPrivate fun _ => nextPrivate))),
          response :: state.history.map Prod.snd⟩ : Trace.State n k Private Control input)) =
      Trace.respond limits sample machine (trace state)
        (hit.map (Phase.mapMemory (Memory.mapPrivate
          (ServerState.mapPrivate fun _ => state.sourceState)))) := by
  cases hit with
  | none =>
    simp [request, StochasticOracle.ConcurrentBatch.Interaction.source, advance,
      respondSource, Trace.respond, Trace.receipt, trace]
  | some phase =>
    have hb := hb phase rfl
    cases phase with
    | ready world =>
      change world.config.tapes.state = none at hb
      simp [request, StochasticOracle.ConcurrentBatch.Interaction.source, advance,
        respondSource, phaseStep, Phase.mapMemory, World.mapMemory, hb, Trace.respond,
        Trace.receipt, trace]
    | pending chosen =>
      cases chosen with
      | halted world => exact hb.elim
      | «local» world => exact hb.elim
      | query world op next =>
        cases op
        change (admit limits world.memory.privateState
          (world.config.channels ()).queryBuffer).isSome at hb
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [ha] at hb
        | some batch =>
          let selected : Request n := ⟨world.memory.privateState, batch⟩
          have hword := (admit_sound limits world.memory.privateState
            (world.config.channels ()).queryBuffer batch ha).2.1
          have hadmit : admit limits (selected.restore state.sourceState) (encodeBatch batch) =
              some batch := by
            simpa only [selected, StochasticOracle.ConcurrentBatch.Interaction.Request.restore,
              admit_mapPrivate, hword] using ha
          have hs := StochasticOracle.ConcurrentBatch.Interaction.draw_serve
            limits sample state.sourceState selected hadmit
          dsimp only [selected, StochasticOracle.ConcurrentBatch.Interaction.Request.restore] at hs
          simp only [request, ha, Option.map_some,
            StochasticOracle.ConcurrentBatch.Interaction.source, PMF.bind_map,
            Function.comp_def, advance, Option.elim_some, phaseStep, dispatch, PMF.pure_map,
            Trace.respond, respondSource, Phase.mapMemory, Instruction.mapMemory,
            World.mapMemory_config, World.mapMemory_memory, Memory.mapPrivate_privateState,
            environment]
          rw [← hword, ← hs]
          simp only [PMF.map_comp, Function.comp_def]
          rfl

/-- One separated interaction is exactly one original accepted native trace step,
including rejected raw requests, analytical receipts and silent divergence. -/
theorem step_trace (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input)
    (state : State n k Private Control input) :
    (InteractionProcess.step (policy limits machine config)
      (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) state).map trace =
      Trace.step limits sample machine (trace state) := by
  rw [Trace.step]
  change _ = (seekSourceFrom limits sample machine (hidden state)).bind
    (Trace.respond limits sample machine (trace state))
  rw [hidden,
    ← seekSourceFrom_mapPrivate limits silentSampler sample machine
      (fun _ => state.sourceState) state.policyState, PMF.bind_map]
  simp only [InteractionProcess.step, policy, PMF.bind_map, PMF.map_bind,
    PMF.map_comp, Function.comp_def, trace, hidden, List.map_cons]
  apply PMF.bind_congr_on_support
  intro hit hh
  apply response_trace limits sample initial machine state hit
  intro phase he
  rw [he] at hh
  cases hc : state.policyState with
  | none => simp [hc, seekSourceFrom] at hh
  | some previous =>
    simp only [hc, seekSourceFrom] at hh
    exact ((StoppedProcess.terminal_support _ _ _ _ _).mp hh).1

/-- The complete separated execution projects to the original actual native
accepted trace law, with earlier receipts retained on silent divergence. -/
theorem execution_trace (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ) :
    (execution limits sample initial machine config epochs).map trace =
      initial.bind fun privateState => Trace.law limits sample machine epochs
        ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩ := by
  have hi : InteractionProcess.initialLaw (policy limits machine config)
      (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) =
      initial.map fun privateState =>
        (⟨[], some (.ready ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial (), []⟩⟩),
          privateState⟩ : State n k Private Control input) := by
    simp only [InteractionProcess.initialLaw, policy,
      StochasticOracle.ConcurrentBatch.Interaction.source, PMF.pure_bind]
  rw [execution, InteractionProcess.law, hi, PMF.bind_map, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro privateState _
  exact ObservedProcess.stateLaw_map
    (InteractionProcess.step (policy limits machine config)
      (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial))
    (Trace.step limits sample machine) trace
    (step_trace limits sample initial machine config) epochs
    ⟨[], some (.ready ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial (), []⟩⟩), privateState⟩

/-- Generated native policies preserve the original accepted-turn, deadline and
nonreuse guards. This makes no feasibility claim for arbitrary forged snapshots. -/
theorem execution_ledger_bound (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
    (state : State n k Private Control input)
    (hs : state ∈ (execution limits sample initial machine config epochs).support) :
    ((state.history.map Prod.snd).filterMap id).length ≤ limits.turns ∧
      (((state.history.map Prod.snd).filterMap id).map Exchange.duration).sum ≤ limits.deadline ∧
      noReuse ((state.history.map Prod.snd).filterMap id) := by
  have ht : trace state ∈
      ((execution limits sample initial machine config epochs).map trace).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨state, hs, rfl⟩
  rw [execution_trace, PMF.mem_support_bind_iff] at ht
  obtain ⟨privateState, _, ht⟩ := ht
  have hb := Trace.law_ledger_bound limits sample machine epochs
    (⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩ :
      World k Control Unit (ServerState n Private) input)
    (initial_invariant limits privateState) (trace state) ht
  simpa only [trace, StochasticOracle.ConcurrentBatch.initial, List.append_nil] using hb

/-- The finite accepted-turn horizon recovers the original unbounded native
terminal law. Fresh source initialization supplies the protocol invariant. -/
theorem execution_terminal (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) :
    (execution limits sample initial machine config (limits.turns + 1)).map
      (fun state => (hidden state).map worldOf) =
      initial.bind fun privateState => NativeUnboundedExecution.terminal machine
        (environment limits sample)
        ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩ := by
  have he := congrArg (PMF.map (fun state : Trace.State n k Private Control input =>
    state.hidden.map worldOf)) (execution_trace limits sample initial machine config
      (limits.turns + 1))
  rw [PMF.map_comp, PMF.map_bind] at he
  change (execution limits sample initial machine config (limits.turns + 1)).map
    (fun state => (hidden state).map worldOf) = initial.bind (fun privateState =>
    (Trace.law limits sample machine (limits.turns + 1)
      ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩).map
        (fun state => state.hidden.map worldOf)) at he
  rw [he]
  apply PMF.bind_congr_on_support
  intro privateState _
  exact Trace.law_native_terminal limits sample machine _ (initial_invariant limits privateState)

/-- Actual enriched histories use the explicit sequential law with one fixed
source filter; only the generated private query policy depends on the machine. -/
theorem execution_histories (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ) :
    (execution limits sample initial machine config epochs).map InteractionProcess.State.history =
      InteractionProcess.historyLaw (policy limits machine config)
        (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs :=
  InteractionProcess.histories_law (policy limits machine config)
    (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs

/-- At each reached enriched accepted history the retained latent source state
has the same filter for every generated native machine. This conditioning includes
analytical receipt metadata, not only the machine-readable reply bytes. -/
theorem source_posterior (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
    (history : List (Option (Request n) × Option (Exchange n)))
    (hh : history ∈ ((execution limits sample initial machine config epochs).map
      InteractionProcess.State.history).support) :
    (PMF.conditionalSnd ((execution limits sample initial machine config epochs).map
      fun state => (state.history, (state.policyState, state.sourceState))) history).map Prod.snd =
      (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).filter history :=
  InteractionProcess.source_posterior (policy limits machine config)
    (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs history hh

end Cslib.Probability.NativeBatch.Interaction
