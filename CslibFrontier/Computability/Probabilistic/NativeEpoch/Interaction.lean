/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeEpoch.Memory
public import CslibFrontier.Computability.Probabilistic.NativeInterface.Interaction
import CslibFrontier.Probability.PMF.ObservedProcess.Map
import CslibFrontier.Probability.Conditioning.Map
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual raw-query epochs with private stopping and retained source memory

Native private computation runs to an actual query or committed halt, and may
diverge silently. Its stopping sampler uses only dummy `Unit` oracle memory.
The fixed real source then answers the selected raw query. Real source memory is
retained independently of the optional private checkpoint, including on paths
that diverge after already incurring a bill.

## Main definitions

* `policy` runs the actual native silent stopping sampler with dummy source memory.
* `execution` records raw-query histories and an `Outcome` whose real source memory
  survives private divergence. `Outcome.world` recovers the ordinary optional native
  world; accounting on divergent paths must instead use `Outcome.memory`.

## Main results

* `execution_epochs` recovers the existing actual raw-query epoch process.
* `execution_resume` resumes each finite prefix to the native unbounded terminal law.
* `outcome_posterior` derives the conditional product at every supported history.
* `source_posterior` identifies the real-memory posterior with one fixed source filter,
  independently of the native machine and including silent divergence.

These are raw query epochs. Accepted-batch guards, rejection skipping and source
opportunity/deadline budgets are separate obligations.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeEpoch.Interaction
open NativeOpenExecution NativeInterface Turing Turing.MultiTapeMachine
variable {Operation Private Control : Type} {k : ℕ} {input : List Bool}

/-- Private divergence is optional; real source memory remains a separate component. -/
abbrev State (k : ℕ) (Control Operation Private : Type) (input : List Bool) :=
  InteractionProcess.State (Option (Operation × List Bool)) Reply
    (Option (Phase k Control Operation Unit input)) (Memory Operation Private)

/-- Actual native snapshot with a retained external ledger even after private divergence. -/
structure Outcome (k : ℕ) (Control Operation Private : Type) (input : List Bool) where
  /-- A native checkpoint, or `none` when silent private computation diverges. -/
  configuration : Option (Config k Bool Control Operation input)
  /-- The real external source memory, preserving earlier events and charges. -/
  memory : Memory Operation Private

/-- Ordinary optional native-world readback. Source accounting uses `memory`
directly when private divergence leaves no native world. -/
@[expose] def Outcome.world (outcome : Outcome k Control Operation Private input) :
    Option (World k Control Operation Private input) :=
  outcome.configuration.map fun config => ⟨config, outcome.memory⟩

/-- Retain the real ledger while forgetting private dummy logs and saved controls. -/
@[expose, simps configuration memory] def outcome
    (state : State k Control Operation Private input) : Outcome k Control Operation Private input :=
  ⟨state.policyState.map (fun phase => (worldOf phase).config), state.sourceState⟩

/-- A query request is read from the actual stopping checkpoint. Halt and private
divergence both issue no query and remain distinct in the private checkpoint. -/
@[expose] def selectedRequest {P : Type} : Option (Phase k Control Operation P input) →
    Option (Operation × List Bool)
  | none => none
  | some (.ready _) => none
  | some (.pending chosen) => NativeInterface.Interaction.request chosen

variable [DecidableEq Operation]

/-- Actual unbounded private local stopping before a raw response. The handler
parameter used during silent selection is never called before a boundary. -/
@[expose] def policy (machine : MultiTapePTM k Bool Control Operation)
    (config : Config k Bool Control Operation input) :
    InteractionProcess.Policy (Option (Operation × List Bool)) Reply
      (Option (Phase k Control Operation Unit input)) where
  initial := PMF.pure (some (.ready ⟨config, ⟨(), []⟩⟩))
  choose _ current :=
    (seekFrom machine (fun _ _ => PMF.pure (⟨[], 0, 0⟩, ())) (current.map worldOf)).map
      fun hit => (selectedRequest hit, hit)
  update _ hit _ reply :=
    (respond (fun _ _ => PMF.pure (reply, ())) hit).map (Option.map Phase.ready)

/-- Actual complete raw-epoch history, private checkpoint and retained real ledger. -/
@[expose] def execution (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (epochs : ℕ) :
    PMF (List (Option (Operation × List Bool) × Reply) ×
      Outcome k Control Operation Private input) :=
  (InteractionProcess.law (policy machine config)
    (NativeInterface.Interaction.source env initial) epochs).map
      fun state => (state.history, outcome state)

private theorem respond_response (env : Environment Operation Private)
    (memory : Memory Operation Private) (hit : Option (Phase k Control Operation Unit input)) :
    (NativeInterface.Interaction.response env memory (selectedRequest hit)).bind
      (fun (reply, nextMemory) =>
        (respond (fun _ _ => PMF.pure (reply, ())) hit).map
          (Option.map fun next => next.mapMemory (fun _ => nextMemory))) =
      respond env (hit.map (Phase.mapMemory (fun _ => memory))) := by
  cases hit with
  | none => simp [selectedRequest, NativeInterface.Interaction.response, respond]
  | some phase =>
    cases phase with
    | ready w =>
      simp [selectedRequest, NativeInterface.Interaction.response, respond, Phase.mapMemory]
    | pending chosen =>
      have he := congrArg (PMF.map some)
        (NativeInterface.Interaction.dispatch_response env memory chosen)
      simpa only [selectedRequest, respond, Option.map_some, Phase.mapMemory,
        PMF.map_bind, PMF.map_comp, Function.comp_def, World.mapMemory] using he

/-- One interaction executes the actual unbounded private stopping computation
and dispatches at most its selected raw query. -/
theorem step_world (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input)
    (state : State k Control Operation Private input) :
    (InteractionProcess.step (policy machine config)
      (NativeInterface.Interaction.source env initial) state).map
        (fun next => (outcome next).world) =
      epochStep machine env (outcome state).world := by
  cases hc : state.policyState with
  | none =>
    simp [InteractionProcess.step, policy, hc, seekFrom, selectedRequest,
      NativeInterface.Interaction.source, NativeInterface.Interaction.response,
      respond, outcome, Outcome.world, epochStep]
  | some phase =>
    have hw : (outcome state).world =
        some ((worldOf phase).mapMemory (fun _ => state.sourceState)) := by
      simp only [outcome, Outcome.world, hc, Option.map_some]
      rfl
    rw [hw, epochStep, nextEpoch,
      ← seek_mapMemory machine (fun _ _ => PMF.pure (⟨[], 0, 0⟩, ())) env
        (fun _ => state.sourceState) (worldOf phase), PMF.bind_map]
    simp only [InteractionProcess.step, policy, hc, Option.map_some, seekFrom,
      NativeInterface.Interaction.source, PMF.bind_map, PMF.map_bind,
      PMF.map_comp, Function.comp_def, outcome, Outcome.world, Option.map_map, worldOf]
    apply PMF.bind_congr_on_support
    intro hit _
    exact respond_response env state.sourceState hit

/-- Optional native-world readback is the original raw epoch process. The richer
interaction state also retains real memory on the divergent branch. -/
theorem law_world (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (epochs : ℕ) :
    (InteractionProcess.law (policy machine config)
      (NativeInterface.Interaction.source env initial) epochs).map
        (fun state => (outcome state).world) =
      initial.bind fun memory => ObservedProcess.stateLaw (epochStep machine env) epochs
        (some (⟨config, memory⟩ : World k Control Operation Private input)) := by
  have hi : InteractionProcess.initialLaw (policy machine config)
      (NativeInterface.Interaction.source env initial) =
      initial.map (fun memory =>
        (⟨[], some (.ready ⟨config, ⟨(), []⟩⟩), memory⟩ :
          State k Control Operation Private input)) := by
    simp only [InteractionProcess.initialLaw, policy, NativeInterface.Interaction.source,
      PMF.pure_bind]
  rw [InteractionProcess.law, hi, PMF.bind_map, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro memory _
  exact ObservedProcess.stateLaw_map
    (InteractionProcess.step (policy machine config)
      (NativeInterface.Interaction.source env initial))
    (epochStep machine env) (fun state => (outcome state).world)
    (step_world machine env initial config) epochs
    ⟨[], some (.ready ⟨config, ⟨(), []⟩⟩), memory⟩

/-- Forgetting the separately retained ledger recovers the existing actual raw
query-epoch process, including halt and silent divergence. -/
theorem execution_epochs (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (epochs : ℕ) :
    (execution machine env initial config epochs).map (fun pair => pair.2.world) =
      initial.bind fun memory => ObservedProcess.stateLaw (epochStep machine env) epochs
        (some (⟨config, memory⟩ : World k Control Operation Private input)) := by
  simpa only [execution, PMF.map_comp, Function.comp_def] using
    law_world machine env initial config epochs

/-- Every finite actual raw-epoch prefix resumes to the original unbounded native
terminal law. The richer epoch outcomes retain their ledger even on divergence. -/
theorem execution_resume (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (epochs : ℕ) :
    (execution machine env initial config epochs).bind
      (fun pair => finish machine env pair.2.world) =
      initial.bind fun memory =>
        NativeUnboundedExecution.terminal machine env ⟨config, memory⟩ := by
  change (execution machine env initial config epochs).bind
    (finish machine env ∘ fun pair => pair.2.world) = _
  rw [← PMF.bind_map, execution_epochs, PMF.bind_bind]
  apply PMF.bind_congr_on_support
  intro memory _
  exact resume_after_epochs machine env epochs ⟨config, memory⟩

/-- At a reached raw-epoch history the optional private configuration and retained
real source memory have the derived conditional product, including divergent outcomes. -/
theorem outcome_posterior (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (epochs : ℕ)
    (history : List (Option (Operation × List Bool) × Reply))
    (hh : history ∈ ((execution machine env initial config epochs).map Prod.fst).support) :
    PMF.conditionalSnd (execution machine env initial config epochs) history =
      ((policy machine config).filter history).bind fun current =>
        ((NativeInterface.Interaction.source env initial).filter history).map fun memory =>
          (⟨current.map (fun phase => (worldOf phase).config), memory⟩ :
            Outcome k Control Operation Private input) := by
  let joint := (InteractionProcess.law (policy machine config)
      (NativeInterface.Interaction.source env initial) epochs).map
    fun state => (state.history, (state.policyState, state.sourceState))
  let readback : Option (Phase k Control Operation Unit input) × Memory Operation Private →
      Outcome k Control Operation Private input :=
    fun cs => ⟨cs.1.map (fun phase => (worldOf phase).config), cs.2⟩
  have he : execution machine env initial config epochs =
      joint.map (fun (h, cs) => (h, readback cs)) := by
    simp only [execution, joint, PMF.map_comp, Function.comp_def, readback, outcome]
  have hj : history ∈ (joint.map Prod.fst).support := by
    simpa only [he, PMF.map_comp, Function.comp_def] using hh
  have ha : history ∈ ((InteractionProcess.law (policy machine config)
      (NativeInterface.Interaction.source env initial) epochs).map
        InteractionProcess.State.history).support := by
    simpa only [joint, PMF.map_comp, Function.comp_def] using hj
  rw [he, PMF.conditionalSnd_map_snd joint readback history hj,
    InteractionProcess.private_posterior (policy machine config)
      (NativeInterface.Interaction.source env initial) epochs history ha]
  simp only [InteractionProcess.privateLaw, PMF.map_bind, PMF.map_comp,
    Function.comp_def, readback]

/-- One machine-independent source filter describes the real ledger at every
reached raw-query epoch, even when private computation diverges silently. -/
theorem source_posterior (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (epochs : ℕ)
    (history : List (Option (Operation × List Bool) × Reply))
    (hh : history ∈ ((execution machine env initial config epochs).map Prod.fst).support) :
    (PMF.conditionalSnd (execution machine env initial config epochs) history).map Outcome.memory =
      (NativeInterface.Interaction.source env initial).filter history := by
  rw [outcome_posterior machine env initial config epochs history hh, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_id _

end Cslib.Probability.NativeEpoch.Interaction
