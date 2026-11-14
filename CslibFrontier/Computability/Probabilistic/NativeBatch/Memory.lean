/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch
public import CslibFrontier.Computability.Probabilistic.NativeInterface.Memory
public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Memory
import CslibFrontier.Probability.PMF.StoppedProcess.Map
import Mathlib.Tactic

/-!
# Accepted-batch private stopping preserves latent-state transport

The accepted-batch guard reads public source history and meters, but not latent
source state. Silent native computation includes rejected requests: these append
zero-charge raw events while preserving the accepted ledger. Mapping only latent
state therefore commutes with the entire actual stopping law, even across unrelated
source samplers. Accepted requests are held before either sampler is invoked.

## Main results

* `sourceSilent_mapPrivate`: silent native transitions preserve latent-state mapping.
* `seekSourceFrom_mapPrivate`: the actual unbounded accepted-boundary law preserves
  this mapping, including silent divergence.
* `sourceSignal_mapPrivate`: the complete selected-before-response signal is unchanged.

This is a stopping-law transport, not yet an accepted-epoch posterior factorization.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
variable {n k : ℕ} {Private Other Control : Type} {input : List Bool}

/-- Accepted source boundaries use only public guard fields and native configuration. -/
@[simp] theorem sourceBoundary_mapPrivate (limits : Limits n) (f : Private → Other)
    (phase : Phase k Control Unit (ServerState n Private) input) :
    sourceBoundary limits
      (phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate f))) ↔
      sourceBoundary limits phase := by
  cases phase with
  | ready world => rfl
  | pending chosen =>
    cases chosen <;>
      simp [sourceBoundary, Phase.mapMemory, Instruction.mapMemory, World.mapMemory,
        Memory.mapPrivate, admit_mapPrivate]

/-- Actual silent execution, including zero-charge rejected requests, commutes
with latent-state mapping without any relation between the two source samplers. -/
theorem sourceSilent_mapPrivate (limits : Limits n) (sample : Sampler n Private)
    (other : Sampler n Other) (machine : MultiTapePTM k Bool Control Unit)
    (f : Private → Other) (phase : Phase k Control Unit (ServerState n Private) input) :
    (sourceSilent limits sample machine phase).map
        (Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate f))) =
      sourceSilent limits other machine
        (phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate f))) := by
  cases phase with
  | ready world =>
    cases hs : world.config.tapes.state with
    | none =>
      simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
        NativeUnboundedExecution.halted, hs, Phase.mapMemory, World.mapMemory]
    | some control =>
      simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
        NativeUnboundedExecution.halted, hs, reduceCtorEq, Option.isNone_some, Bool.false_eq_true,
        ite_false, phaseStep, Phase.mapMemory, World.mapMemory_config,
        prepare_mapMemory, PMF.map_comp, Function.comp_def]
  | pending chosen =>
    cases chosen with
    | halted world =>
      simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, Phase.mapMemory,
        Instruction.mapMemory, phaseStep, dispatch, World.mapMemory]
    | «local» world =>
      simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, Phase.mapMemory,
        Instruction.mapMemory, phaseStep, dispatch, World.mapMemory]
    | query world op next =>
      cases op
      cases ha : admit limits world.memory.privateState (world.config.channels ()).queryBuffer <;>
        simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, Phase.mapMemory,
          Instruction.mapMemory, World.mapMemory, Memory.mapPrivate, phaseStep, dispatch,
          environment, serve, admit_mapPrivate, ha, Memory.record]

/-- Silent execution is independent of the source sampler because no admitted
query is dispatched. This is the identity-map case of latent-state transport. -/
theorem sourceSilent_independent (limits : Limits n) (sample : Sampler n Private)
    (machine : MultiTapePTM k Bool Control Unit) (other : Sampler n Private) :
    sourceSilent (input := input) limits sample machine = sourceSilent limits other machine := by
  funext phase
  have hid : Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate (id : Private → Private))) =
      (id : Phase k Control Unit (ServerState n Private) input → _) := by
    funext phase
    cases phase with
    | ready world => rfl
    | pending chosen => cases chosen <;> rfl
  simpa only [hid, PMF.map_id, id_eq] using
    sourceSilent_mapPrivate limits sample other machine id phase

/-- Mapping latent state commutes with actual unbounded selection of the next
accepted batch or halt, without assuming termination or an epoch-law identity. -/
theorem seekSourceFrom_mapPrivate (limits : Limits n) (sample : Sampler n Private)
    (other : Sampler n Other) (machine : MultiTapePTM k Bool Control Unit)
    (f : Private → Other) (hit : Option (Phase k Control Unit (ServerState n Private) input)) :
    (seekSourceFrom limits sample machine hit).map
        (Option.map (Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate f)))) =
      seekSourceFrom limits other machine
        (hit.map (Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate f)))) := by
  cases hit with
  | none => simp [seekSourceFrom]
  | some phase =>
    exact StoppedProcess.terminal_map (sourceSilent limits sample machine)
      (sourceBoundary limits) (sourceSilent_absorbs limits sample machine)
      (sourceSilent limits other machine) (sourceBoundary limits)
      (sourceSilent_absorbs limits other machine)
      (Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate f)))
      (sourceSilent_mapPrivate limits sample other machine f)
      (sourceBoundary_mapPrivate limits f) phase

/-- The selected accepted-history/batch signal does not reveal latent source state. -/
@[simp] theorem sourceSignal_mapPrivate (limits : Limits n) (f : Private → Other)
    (hit : Option (Phase k Control Unit (ServerState n Private) input)) :
    sourceSignal limits
        (hit.map (Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate f)))) =
      sourceSignal limits hit := by
  cases hit with
  | none => rfl
  | some phase =>
    cases phase with
    | ready world => rfl
    | pending chosen =>
      cases chosen <;>
        simp [sourceSignal, Phase.mapMemory, Instruction.mapMemory, World.mapMemory,
          Memory.mapPrivate, admit_mapPrivate]

end Cslib.Probability.NativeBatch
