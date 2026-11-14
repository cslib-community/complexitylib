/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeEpoch
public import CslibFrontier.Computability.Probabilistic.NativeInterface.Memory
import CslibFrontier.Probability.PMF.StoppedProcess.Map
import Mathlib.Tactic

/-!
# Unbounded raw-query selection is blind to source-private memory

Actual silent native computation stops before dispatching any query. Mapping the
oracle memory to another private-state type therefore commutes with its entire
stopping law, including missing mass from silent divergence. Arbitrary response
handlers are allowed on the two sides because neither is invoked before stopping.

## Main results

* `silentStep_mapMemory`: exact one-step silent memory transport.
* `seek_mapMemory`: actual unbounded next-query/halting transport.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeEpoch
open NativeOpenExecution NativeInterface Turing
variable {Operation Private Other Control : Type} {k : ℕ} {input : List Bool}

/-- Query and committed-halt boundaries depend on configuration and instruction,
not on the source-private memory carried by the checkpoint. -/
@[simp] theorem boundary_mapMemory (f : Memory Operation Private → Memory Operation Other)
    (phase : Phase k Control Operation Private input) :
    boundary (phase.mapMemory f) ↔ boundary phase := by
  cases phase with
  | ready world => rfl
  | pending chosen => cases chosen <;> rfl

variable [DecidableEq Operation]

/-- Silent native transitions commute with arbitrary memory replacement, even
across different private-state types and unrelated response handlers. -/
theorem silentStep_mapMemory (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (other : Environment Operation Other)
    (f : Memory Operation Private → Memory Operation Other)
    (phase : Phase k Control Operation Private input) :
    (silentStep machine env phase).map (Phase.mapMemory f) =
      silentStep machine other (phase.mapMemory f) := by
  cases phase with
  | ready world =>
    cases hs : world.config.tapes.state with
    | none =>
      simp [silentStep, StoppedProcess.beforeBoundary, boundary,
        NativeUnboundedExecution.halted, hs, Phase.mapMemory, World.mapMemory]
    | some c =>
      simp only [silentStep, StoppedProcess.beforeBoundary, boundary, phaseStep,
        NativeUnboundedExecution.halted, hs, reduceCtorEq, ite_false,
        Option.isNone_some, Bool.false_eq_true, Phase.mapMemory,
        World.mapMemory_config, prepare_mapMemory, PMF.map_comp, Function.comp_def]
  | pending chosen =>
    cases chosen <;> simp [silentStep, StoppedProcess.beforeBoundary, boundary,
      Phase.mapMemory, Instruction.mapMemory, phaseStep, dispatch, World.mapMemory]

/-- Actual unbounded private query selection preserves memory replacement and
silent divergence, without a finite-clock or termination premise. -/
theorem seek_mapMemory (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (other : Environment Operation Other)
    (f : Memory Operation Private → Memory Operation Other)
    (world : World k Control Operation Private input) :
    (seek machine env world).map (Option.map (Phase.mapMemory f)) =
      seek machine other (world.mapMemory f) := by
  exact StoppedProcess.terminal_map (silentStep machine env) boundary
    (silent_absorbs machine env) (silentStep machine other) boundary
    (silent_absorbs machine other) (Phase.mapMemory f)
    (silentStep_mapMemory machine env other f) (boundary_mapMemory f) (.ready world)

end Cslib.Probability.NativeEpoch
