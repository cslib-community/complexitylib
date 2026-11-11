/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
public import CslibFrontier.Probability.PMF.StoppedProcess.Map
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Native output buffering through unbounded execution

The existing native output-to-work-tape compiler preserves every finite joint run.
Consequently it preserves the actual unbounded terminal law, including divergence,
full shared oracle state, channels and all resources. The work buffer is created by
ordinary output instructions, not populated with an assumed intermediate value.

## Main results

* `execute_buffer`: the actual clocked native compiler law.
* `terminal_buffer`: its unbounded stopped law, with no uniform clock premise.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeOutputBuffer
open Turing Turing.MultiTapeMachine NativeOpenExecution
variable {k : ℕ} {Control Operation Private : Type} [DecidableEq Operation] {input : List Bool}

/-- Retain every source tape/channel and memory while redirecting its output to
one fresh work tape through the existing native compiler. -/
@[expose] def world (w : World k Control Operation Private input) :
    World (k + 1) Control Operation Private input :=
  ⟨OutputToTape.config w.config, w.memory⟩

/-- Output redirection preserves the entire actual clocked configuration program,
not only its output marginal or its halting probability. -/
theorem execute_buffer (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (fuel : ℕ) (w : World k Control Operation Private input) :
    execute machine.outputToTape env fuel (world w) =
      (execute machine env fuel w).map world := by
  simp only [execute, MultiTapePTM.runConfigFrom_outputToTape, world,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
  rfl

/-- Unbounded native output buffering preserves the full terminal law, including
any divergent mass, arbitrary hidden-state correlation and all accrued resources. -/
theorem terminal_buffer (machine : MultiTapePTM k Bool Control Operation)
    (env : Environment Operation Private) (w : World k Control Operation Private input) :
    NativeUnboundedExecution.terminal machine.outputToTape env (world w) =
      (NativeUnboundedExecution.terminal machine env w).map (Option.map world) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step machine env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (NativeOpenExecution.step machine.outputToTape env) NativeUnboundedExecution.halted
    (NativeUnboundedExecution.step_halted _ _) world _ _ w
  · intro next
    rw [← execute_one, ← execute_one]
    exact (execute_buffer machine env 1 next).symm
  · intro next
    rfl

omit [DecidableEq Operation] in
/-- The copied word is on a genuine readable work tape, with its head at the
write frontier; the original output tape of the compiled machine stays empty. -/
theorem buffer_contents (w : World k Control Operation Private input) :
    (world w).config.tapes.workTapes (Fin.last k) = tapeOfList w.config.tapes.output ∧
      (world w).config.tapes.workTapePos (Fin.last k) = w.config.tapes.output.length ∧
      (world w).config.tapes.output = [] ∧ (world w).memory = w.memory := by
  exact ⟨MultiTapeTM.outCfg_workTapes_last _, MultiTapeTM.outCfg_workTapePos_last _, rfl, rfl⟩

end Cslib.Probability.NativeOutputBuffer
