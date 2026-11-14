/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeInterface.Memory
public import CslibFrontier.Probability.PMF.Interaction.Process
import CslibFrontier.Probability.PMF.ObservedProcess.Map
import CslibFrontier.Probability.Conditioning.Map
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual native instructions as separated private interactions

A single interaction prepares and commits one actual native instruction. The
policy carries configurations and saved instructions with only dummy `Unit`
oracle memory; the source alone carries the real private oracle memory. Replies
retain their complete words, invoices and physical durations. Local and halted
instructions emit `none`, distinct from a genuine zero-resource query.

`execution_native` identifies the complete-world marginal with the original
clocked native interpreter. `source_posterior` derives one source-memory filter
independent of the machine at supported complete instruction histories. Arbitrary
discrete initial source memory is sampled independently of the fixed initial
configuration, retaining pre-existing events and resources.

This realizes typed `MultiTapePTM` programs at an instruction clock. It does not
collapse unbounded silent work into source stopping epochs or infer a native
deadline/turn-budget theorem.

## Main definitions

* `source`, `response`: one actual shared stateful oracle and complete replies.
* `policy`: actual native private selection and fixed-reply dispatch.
* `execution`: joint complete instruction history and actual native world.

## Main results

* `step_world`, `law_world`: exact native transition and finite-clock realization.
* `execution_native`, `execution_pure`: original native interpreter readback.
* `world_posterior`, `source_posterior`: actual conditional private-world products and
  a machine-independent source filter.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeInterface.Interaction
open NativeOpenExecution Turing Turing.MultiTapeMachine
open scoped NNReal
variable {Operation Private Control : Type} {k : ℕ} {input : List Bool}

/-- Actual native private interaction state. Its policy phase contains no real
oracle-private state; the source component is the real complete memory. -/
abbrev State (k : ℕ) (Control Operation Private : Type) (input : List Bool) :=
  InteractionProcess.State (Option (Operation × List Bool)) Reply
    (Phase k Control Operation Unit input) (Memory Operation Private)

/-- Public selected request, with no-call padding separate from an actual query. -/
@[expose] def request {P : Type} : Instruction k Control Operation P input →
    Option (Operation × List Bool)
  | .halted _ => none
  | .local _ => none
  | .query w op _ => some (op, (w.config.channels op).queryBuffer)

/-- The same real source handler for every native machine. No-call padding leaves
real memory unchanged; an actual reply records all resources exactly once. -/
@[expose] def response (env : Environment Operation Private) (memory : Memory Operation Private) :
    Option (Operation × List Bool) → PMF (Reply × Memory Operation Private)
  | none => PMF.pure (⟨[], 0, 0⟩, memory)
  | some q => (env q memory).map fun (reply, privateState) =>
      (reply, memory.record q reply privateState)

/-- Machine-independent source with arbitrary discrete initial private memory. -/
@[expose] def source (env : Environment Operation Private)
    (initial : PMF (Memory Operation Private)) :
    InteractionProcess.Source (Option (Operation × List Bool)) Reply (Memory Operation Private) :=
  ⟨initial, fun _ memory q => response env memory q⟩

variable [DecidableEq Operation]

/-- The actual private native instruction sampler. Saved selections retain the
original continuation and fresh private coin; only dummy memory is stored here. -/
@[expose] def policy (machine : MultiTapePTM k Bool Control Operation)
    (config : Config k Bool Control Operation input) :
    InteractionProcess.Policy (Option (Operation × List Bool)) Reply
      (Phase k Control Operation Unit input) where
  initial := PMF.pure (.ready ⟨config, ⟨(), []⟩⟩)
  choose _ phase := (prepare machine (worldOf phase)).map fun chosen =>
    (request chosen, .pending chosen)
  update _ phase _ reply := match phase with
    | .ready w => PMF.pure (.ready w)
    | .pending chosen =>
      (dispatch (fun _ _ => PMF.pure (reply, ())) chosen).map Phase.ready

/-- Actual-world readback uses the real source memory, never the dummy policy log. -/
@[expose, simps config memory] def world (state : State k Control Operation Private input) :
    World k Control Operation Private input :=
  ⟨(worldOf state.policyState).config, state.sourceState⟩

/-- Joint complete instruction history and actual native world after a finite clock. -/
@[expose] def execution (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (fuel : ℕ) :
    PMF (List (Option (Operation × List Bool) × Reply) ×
      World k Control Operation Private input) :=
  (InteractionProcess.law (policy machine config) (source env initial) fuel).map
    fun state => (state.history, world state)

private theorem dispatch_response (env : Environment Operation Private)
    (memory : Memory Operation Private) (chosen : Instruction k Control Operation Unit input) :
    (response env memory (request chosen)).bind (fun (reply, nextMemory) =>
      (dispatch (fun _ _ => PMF.pure (reply, ())) chosen).map fun next =>
        (⟨next.config, nextMemory⟩ : World k Control Operation Private input)) =
      dispatch env (chosen.mapMemory (fun _ => memory)) := by
  cases chosen with
  | halted w => simp [request, response, dispatch, Instruction.mapMemory, World.mapMemory]
  | «local» w => simp [request, response, dispatch, Instruction.mapMemory, World.mapMemory]
  | query w op next =>
    simp only [request, response, dispatch, PMF.bind_map, PMF.pure_map,
      Instruction.mapMemory, World.mapMemory_config, World.mapMemory_memory]
    rfl

/-- One separated interaction is exactly one actual native instruction, preserving
full configurations and real memory rather than only output words. -/
theorem step_world (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input)
    (state : State k Control Operation Private input) :
    (InteractionProcess.step (policy machine config) (source env initial) state).map world =
      NativeOpenExecution.step machine env (world state) := by
  rw [← prepare_dispatch machine env (world state)]
  have hw : world state = (worldOf state.policyState).mapMemory (fun _ => state.sourceState) := rfl
  rw [hw, prepare_mapMemory, PMF.bind_map]
  simp only [InteractionProcess.step, policy, source, PMF.bind_map, PMF.map_bind,
    PMF.map_comp, Function.comp_def, world, worldOf]
  apply PMF.bind_congr_on_support
  intro chosen _
  exact dispatch_response env state.sourceState chosen

/-- The complete simulated native state projects to the actual original clocked
interpreter, with arbitrary discrete initial source memory and every resource field. -/
theorem law_world (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (fuel : ℕ) :
    (InteractionProcess.law (policy machine config) (source env initial) fuel).map world =
      initial.bind fun memory => execute machine env fuel ⟨config, memory⟩ := by
  have hi : InteractionProcess.initialLaw (policy machine config) (source env initial) =
      initial.map (fun memory =>
        (⟨[], .ready ⟨config, ⟨(), []⟩⟩, memory⟩ : State k Control Operation Private input)) := by
    simp only [InteractionProcess.initialLaw, policy, source, PMF.pure_bind]
  rw [InteractionProcess.law, hi, PMF.bind_map, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro memory _
  exact (ObservedProcess.stateLaw_map
    (InteractionProcess.step (policy machine config) (source env initial))
    (NativeOpenExecution.step machine env) world (step_world machine env initial config)
    fuel ⟨[], .ready ⟨config, ⟨(), []⟩⟩, memory⟩).trans
      (execute_eq_stateLaw machine env fuel ⟨config, memory⟩).symm

/-- Forgetting the constructed public history recovers actual native execution,
without assuming any machine-to-process representation equality. -/
theorem execution_native (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (fuel : ℕ) :
    (execution machine env initial config fuel).map Prod.snd =
      initial.bind fun memory => execute machine env fuel ⟨config, memory⟩ := by
  simpa only [execution, PMF.map_comp, Function.comp_def] using
    law_world machine env initial config fuel

/-- Ordinary point-initial native execution is the special case of deterministic
initial source memory, including already accrued events and resources. -/
theorem execution_pure (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (start : World k Control Operation Private input)
    (fuel : ℕ) :
    (execution machine env (PMF.pure start.memory) start.config fuel).map Prod.snd =
      execute machine env fuel start := by
  simpa only [PMF.pure_bind] using execution_native machine env (PMF.pure start.memory)
    start.config fuel

/-- Conditioning an actual reached native history separates the remaining private
configuration from one shared source-memory filter. -/
theorem world_posterior (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (fuel : ℕ)
    (history : List (Option (Operation × List Bool) × Reply))
    (hh : history ∈ ((execution machine env initial config fuel).map Prod.fst).support) :
    PMF.conditionalSnd (execution machine env initial config fuel) history =
      ((policy machine config).filter history).bind fun phase =>
        ((source env initial).filter history).map fun memory =>
          (⟨(worldOf phase).config, memory⟩ : World k Control Operation Private input) := by
  let joint := (InteractionProcess.law (policy machine config) (source env initial) fuel).map
    fun state => (state.history, (state.policyState, state.sourceState))
  let readback : Phase k Control Operation Unit input × Memory Operation Private →
      World k Control Operation Private input :=
    fun cs => ⟨(worldOf cs.1).config, cs.2⟩
  have he : execution machine env initial config fuel =
      joint.map (fun (h, cs) => (h, readback cs)) := by
    simp only [execution, joint, PMF.map_comp, Function.comp_def, readback, world]
  have hj : history ∈ (joint.map Prod.fst).support := by
    simpa only [he, PMF.map_comp, Function.comp_def] using hh
  have ha : history ∈ ((InteractionProcess.law (policy machine config)
      (source env initial) fuel).map InteractionProcess.State.history).support := by
    simpa only [joint, PMF.map_comp, Function.comp_def] using hj
  rw [he, PMF.conditionalSnd_map_snd joint readback history hj,
    InteractionProcess.private_posterior (policy machine config) (source env initial)
      fuel history ha]
  simp only [InteractionProcess.privateLaw, PMF.map_bind, PMF.map_comp,
    Function.comp_def, readback]

/-- The real source-memory posterior depends on the fixed source and complete
instruction history, uniformly over native machines and private configurations. -/
theorem source_posterior (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (initial : PMF (Memory Operation Private))
    (config : Config k Bool Control Operation input) (fuel : ℕ)
    (history : List (Option (Operation × List Bool) × Reply))
    (hh : history ∈ ((execution machine env initial config fuel).map Prod.fst).support) :
    (PMF.conditionalSnd (execution machine env initial config fuel) history).map World.memory =
      (source env initial).filter history := by
  rw [world_posterior machine env initial config fuel history hh, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_id _

end Cslib.Probability.NativeInterface.Interaction
