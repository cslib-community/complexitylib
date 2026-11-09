/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeUnboundedExecution
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import Complexity.Probability.PMF.StoppedProcess.Map
public import Complexity.Probability.PMF.StoppedProcess.Boundary
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual native sequential composition without common phase clocks

The existing native `seq` compiler hands off all tapes, channels and shared oracle
memory. Its actual unbounded stopped law is monadic composition of the two actual
native terminal laws. Each phase may have an unbounded response-dependent running
time or diverge. No terminating clock or representation contract is supplied.

## Main results

* `terminal_seq`: exact whole-state unbounded native sequential composition.
* `terminal_mapControl`: structural transition-table control relabeling.
* `terminal_embedStorage`: actual tape embedding preserves the unbounded law.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeSequential
open Turing Turing.MultiTapeMachine NativeOpenExecution
open scoped ENNReal
variable {k : ℕ} {Control First Second Operation Private : Type} [DecidableEq Operation]
  {input : List Bool}

/-- Relabel native control while preserving tapes, channels and shared oracle memory. -/
@[expose] def mapControl (f : First → Second) (world : World k First Operation Private input) :
    World k Second Operation Private input := ⟨world.config.mapState f, world.memory⟩

/-- A structural transition-table simulation preserves the entire unbounded native
law, including divergence. Branch compilers discharge the transition identity directly. -/
theorem terminal_mapControl (source : MultiTapePTM k Bool First Operation)
    (target : MultiTapePTM k Bool Second Operation) (f : First → Second)
    (htr : ∀ state inp work answer bit,
      target.tr (f state) inp work answer bit =
        Action.mapState f (source.tr state inp work answer bit))
    (env : Environment Operation Private) (world : World k First Operation Private input) :
    NativeUnboundedExecution.terminal target env (mapControl f world) =
      (NativeUnboundedExecution.terminal source env world).map (Option.map (mapControl f)) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step source env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (NativeOpenExecution.step target env) NativeUnboundedExecution.halted
    (NativeUnboundedExecution.step_halted _ _) (mapControl f) _ _ world
  · intro next
    rw [← execute_one, ← execute_one]
    have hr := MultiTapeMachine.runConfigFrom_mapState
      (Choose := ReaderT Bool Id)
      (spec := probOracleSpec (fun _ : Operation × List Bool => List Bool))
      source target
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun _ _ => by simp only [Functor.map_map]; rfl)
      (fun op word => ProbOracleComp.query (op, word)) f
      (fun state inp work answer => funext fun bit => htr state inp work answer bit)
      1 next.config
    change target.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word => ProbOracleComp.query
        (spec := fun _ : Operation × List Bool => List Bool) (op, word))
      1 (next.config.mapState f) =
      (fun cfg => cfg.mapState f) <$> source.runConfigFrom
        (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => ProbOracleComp.query
          (spec := fun _ : Operation × List Bool => List Bool) (op, word)) 1 next.config at hr
    simp only [execute, mapControl, hr, OracleComp.interpret_map,
      StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
    rfl
  · intro next
    simp [mapControl, Config.mapState, NativeUnboundedExecution.halted, Cfg.mapState]

/-- Embed ordinary native storage into selected work tapes, leaving extras blank. -/
@[expose] def embedStorage {width : ℕ} (e : Fin k ↪ Fin width)
    (world : World k First Operation Private input) : World width First Operation Private input :=
  ⟨world.config.embed e (fun _ _ => none) (fun _ => 0), world.memory⟩

/-- Tape embedding preserves the unbounded native joint law, including divergence. -/
theorem terminal_embedStorage {width : ℕ} (e : Fin k ↪ Fin width)
    (source : MultiTapePTM k Bool First Operation) (env : Environment Operation Private)
    (world : World k First Operation Private input) :
    NativeUnboundedExecution.terminal (source.extendTapes e) env (embedStorage e world) =
      (NativeUnboundedExecution.terminal source env world).map (Option.map (embedStorage e)) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step source env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (NativeOpenExecution.step (source.extendTapes e) env) NativeUnboundedExecution.halted
    (NativeUnboundedExecution.step_halted _ _) (embedStorage e) _ _ world
  · intro next
    rw [← execute_one, ← execute_one]
    simp only [execute, embedStorage, MultiTapePTM.runConfigFrom_embed,
      OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
    rfl
  · intro next
    rfl

/-- Embed a first-phase world into the actual native sequential machine. -/
@[expose] def left (second : MultiTapePTM k Bool Second Operation)
    (w : World k First Operation Private input) :
    World k (First ⊕ Second) Operation Private input :=
  ⟨Sequential.left second w.config, w.memory⟩

/-- Start the second native phase on the complete retained tapes and channels. -/
@[expose] def resume (second : MultiTapePTM k Bool Second Operation)
    (w : World k First Operation Private input) : World k Second Operation Private input :=
  ⟨Sequential.start second w.config, w.memory⟩

/-- Embed an executing continuation, retaining every tape, channel and resource. -/
@[expose] def right (w : World k Second Operation Private input) :
    World k (First ⊕ Second) Operation Private input := ⟨Sequential.right w.config, w.memory⟩

private theorem step_left (first : MultiTapePTM k Bool First Operation)
    (second : MultiTapePTM k Bool Second Operation) (env : Environment Operation Private)
    (w : World k First Operation Private input) (hw : w.config.tapes.state ≠ none) :
    NativeOpenExecution.step (first.seq second) env (left second w) =
      (NativeOpenExecution.step first env w).map (left second) := by
  rw [← execute_one, ← execute_one]
  have he := Sequential.runConfigFrom_one first second
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun f choices => by rw [Functor.map_map]; rfl)
    (fun op word =>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
    w.config hw
  change MultiTapePTM.runConfigFrom (first.seq second)
      (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word =>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
      1 (Sequential.left second w.config) =
    Sequential.left second <$> MultiTapePTM.runConfigFrom first
      (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word =>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
      1 w.config at he
  simp only [execute, left, he, OracleComp.interpret_map, StateT.run_map,
    PMF.monad_map_eq_map, PMF.map_comp]
  rfl

private theorem step_right (first : MultiTapePTM k Bool First Operation)
    (second : MultiTapePTM k Bool Second Operation) (env : Environment Operation Private)
    (w : World k Second Operation Private input) :
    NativeOpenExecution.step (first.seq second) env (right w) =
      (NativeOpenExecution.step second env w).map right := by
  rw [← execute_one, ← execute_one]
  have he := Sequential.runConfigFrom_right first second
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun f choices => by rw [Functor.map_map]; rfl)
    (fun op word =>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
      1 w.config
  change MultiTapePTM.runConfigFrom (first.seq second)
      (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word =>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
      1 (Sequential.right w.config) =
    Sequential.right <$> MultiTapePTM.runConfigFrom second
      (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word =>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
      1 w.config at he
  simp only [execute, right, he, OracleComp.interpret_map, StateT.run_map,
    PMF.monad_map_eq_map, PMF.map_comp]
  rfl

private def boundary (w : World k (First ⊕ Second) Operation Private input) : Prop :=
  match w.config.tapes.state with
  | none => True
  | some (.inl _) => False
  | some (.inr _) => True

private instance : DecidablePred
    (boundary (k := k) (First := First) (Second := Second) (Operation := Operation)
      (Private := Private) (input := input)) := fun w => by
  unfold boundary
  split <;> infer_instance

omit [DecidableEq Operation] in
private theorem boundary_left (second : MultiTapePTM k Bool Second Operation)
    (w : World k First Operation Private input) :
    boundary (left second w) ↔ NativeUnboundedExecution.halted w := by
  cases hs : w.config.tapes.state <;>
    simp [boundary, left, Sequential.left, Cfg.mapState, NativeUnboundedExecution.halted, hs]

private theorem prefix_step (first : MultiTapePTM k Bool First Operation)
    (second : MultiTapePTM k Bool Second Operation) (env : Environment Operation Private)
    (w : World k First Operation Private input) :
    StoppedProcess.beforeBoundary (NativeOpenExecution.step (first.seq second) env)
        boundary (left second w) =
      (NativeOpenExecution.step first env w).map (left second) := by
  by_cases hw : NativeUnboundedExecution.halted w
  · rw [StoppedProcess.beforeBoundary, ite_eq_left ((boundary_left second w).mpr hw),
      NativeUnboundedExecution.step_halted first env w hw, PMF.pure_map]
  · rw [StoppedProcess.beforeBoundary, ite_eq_right (fun h => hw ((boundary_left second w).mp h))]
    exact step_left first second env w hw

private theorem terminal_right (first : MultiTapePTM k Bool First Operation)
    (second : MultiTapePTM k Bool Second Operation) (env : Environment Operation Private)
    (w : World k Second Operation Private input) :
    NativeUnboundedExecution.terminal (first.seq second) env (right w) =
      (NativeUnboundedExecution.terminal second env w).map (Option.map right) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step second env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (NativeOpenExecution.step (first.seq second) env) NativeUnboundedExecution.halted
    (NativeUnboundedExecution.step_halted _ _) right _ _ w
  · exact fun next => (step_right first second env next).symm
  · intro next
    simp [right, Sequential.right, NativeUnboundedExecution.halted, Cfg.mapState]

/-- The actual native compiler has the complete unbounded sequential law. Both
phases may diverge or have arbitrarily long correlated reply-dependent clocks.
The continuation receives the actual retained world, never freshly sampled state. -/
theorem terminal_seq (first : MultiTapePTM k Bool First Operation)
    (second : MultiTapePTM k Bool Second Operation) (env : Environment Operation Private)
    (w : World k First Operation Private input) :
    NativeUnboundedExecution.terminal (first.seq second) env (left second w) =
      (NativeUnboundedExecution.terminal first env w).bind fun
        | none => PMF.pure none
        | some next => (NativeUnboundedExecution.terminal second env (resume second next)).map
            (Option.map right) := by
  have hf := StoppedProcess.terminal_map (NativeOpenExecution.step first env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (StoppedProcess.beforeBoundary (NativeOpenExecution.step (first.seq second) env) boundary)
    boundary (StoppedProcess.beforeBoundary_absorbs _ _) (left second)
    (fun next => (prefix_step first second env next).symm) (boundary_left second) w
  have hr := StoppedProcess.terminal_restart (NativeOpenExecution.step (first.seq second) env)
    NativeUnboundedExecution.halted boundary (NativeUnboundedExecution.step_halted _ _)
    (fun next hn => by simp [boundary, NativeUnboundedExecution.halted] at *; simp_all)
    (left second w)
  rw [← hf] at hr
  change NativeUnboundedExecution.terminal (first.seq second) env (left second w) = _ at hr
  rw [hr, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro next hn
  cases next with
  | none => rfl
  | some next =>
    have hh := (NativeUnboundedExecution.terminal_support first env w next).mp hn
    have he : left second next = right (resume second next) := by
      unfold left right resume
      rw [Sequential.left_halted second next.config hh.1]
    simp only [Function.comp_apply, Option.map_some, Option.elim_some]
    rw [he]
    exact terminal_right first second env (resume second next)

end Cslib.Probability.NativeSequential
