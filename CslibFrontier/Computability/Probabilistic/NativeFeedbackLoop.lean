/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeSequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Native feedback without a common round clock

The finite control tests an actual tape cell before each round and returns to that
same test after the actual body halts. The body may have unbounded response-dependent
local time or diverge. The unbounded native law factors through its real next handoff.

## Main definitions

* `machine`: finite native control for an executed test before every round.
* `run`, `check`, `stopped`: actual retained-storage control configurations.

## Main results

* `terminal_round`: real body termination returns to the same native test.
* `terminal_check`: exact unbounded law of the native test/round/restart.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeFeedbackLoop
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution
variable {k : ℕ} {S P : Type} {input : List Bool}

private abbrev checker : MultiTapePTM k Bool Unit Unit :=
  MultiTapePTM.ofDeterministic (nop k Bool)

/-- Test the selected cell before each body execution; only `some false` continues.
A body halt returns to the same native test, without reinitializing storage. -/
@[expose] def machine (i : Fin k) (body : MultiTapePTM k Bool S Unit) :
    MultiTapePTM k Bool (S ⊕ Unit) Unit where
  initial := .inr ()
  tr state inp work answer bit := match state with
    | .inl q =>
        (body.seq (MultiTapePTM.ofDeterministic (Oracle := Unit) (nop k Bool))).tr
          (.inl q) inp work answer bit
    | .inr _ => .step
        ⟨0, fun _ => (none, 0), none,
          if work i = some false then some (.inl body.initial) else none⟩
        (fun _ => none) (fun _ => 0)

/-- The finite feedback controller starts at the tape test, before running the body. -/
theorem machine_initial (i : Fin k) (body : MultiTapePTM k Bool S Unit) :
    (machine i body).initial = .inr () := rfl

/-- Embed one running round, sending its actual halt back to the native test. -/
@[expose] def run (world : World k S Unit P input) : World k (S ⊕ Unit) Unit P input :=
  ⟨{ world.config with tapes := (world.config.tapes.mapState
      (fun state => some (state.elim (.inr ()) Sum.inl))) }, world.memory⟩

/-- Actual test entry on retained tapes, channels and shared oracle state. -/
@[expose] def check (world : World k S Unit P input) : World k (S ⊕ Unit) Unit P input :=
  ⟨{ world.config with tapes := world.config.tapes.withState (some (.inr ())) }, world.memory⟩

/-- Actual stopped configuration, without changing runtime data or resources. -/
@[expose] def stopped (world : World k S Unit P input) : World k (S ⊕ Unit) Unit P input :=
  ⟨{ (check world).config with tapes := (check world).config.tapes.withState none }, world.memory⟩

private theorem prefix_eq (i : Fin k) (body : MultiTapePTM k Bool S Unit)
    (env : Environment Unit P) (world : World k (S ⊕ Unit) Unit P input) :
    StoppedProcess.beforeBoundary (NativeOpenExecution.step (machine i body) env)
        NativeSequential.boundary world =
      StoppedProcess.beforeBoundary (NativeOpenExecution.step (body.seq checker) env)
        NativeSequential.boundary world := by
  by_cases hb : NativeSequential.boundary world
  · simp [StoppedProcess.beforeBoundary, hb]
  · simp only [StoppedProcess.beforeBoundary, ite_eq_right hb]
    cases hs : world.config.tapes.state with
    | none => simp [NativeSequential.boundary, hs] at hb
    | some state =>
      cases state with
      | inr q => simp [NativeSequential.boundary, hs] at hb
      | inl q => simp only [NativeOpenExecution.step, hs, machine]

/-- A real native round, including any divergent mass, factors through its actual
halt and resumes the same loop on the exact retained configuration. -/
theorem terminal_round (i : Fin k) (body : MultiTapePTM k Bool S Unit)
    (env : Environment Unit P) (world : World k S Unit P input) :
    NativeUnboundedExecution.terminal (machine i body) env
      (run world) =
      (NativeUnboundedExecution.terminal body env world).bind fun
        | none => PMF.pure none
        | some next => NativeUnboundedExecution.terminal (machine i body) env (check next) := by
  change NativeUnboundedExecution.terminal (machine i body) env
    (NativeSequential.left checker world) = _
  have hf := StoppedProcess.terminal_map (NativeOpenExecution.step body env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (StoppedProcess.beforeBoundary (NativeOpenExecution.step (machine i body) env)
      NativeSequential.boundary)
    NativeSequential.boundary (StoppedProcess.beforeBoundary_absorbs _ _)
    (NativeSequential.left checker)
    (fun next => by rw [prefix_eq]; exact (NativeSequential.prefix_step body checker env next).symm)
    (NativeSequential.boundary_left checker) world
  have hr := StoppedProcess.terminal_restart (NativeOpenExecution.step (machine i body) env)
    NativeUnboundedExecution.halted NativeSequential.boundary
    (NativeUnboundedExecution.step_halted _ _)
    (fun next hn => by
      change next.config.tapes.state = none at hn
      simp [NativeSequential.boundary, hn])
    (NativeSequential.left checker world)
  rw [← hf] at hr
  change NativeUnboundedExecution.terminal (machine i body) env _ = _ at hr
  rw [hr, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro next hn
  cases next with
  | none => rfl
  | some next =>
    have hh := (NativeUnboundedExecution.terminal_support body env world next).mp hn
    have he : NativeSequential.left checker next = check next := by
      unfold check NativeSequential.left
      rw [Sequential.left_halted checker next.config hh.1]
      rfl
    simp only [Function.comp_apply, Option.map_some, Option.elim_some]
    rw [he]
    rfl

private theorem step_check (i : Fin k) (body : MultiTapePTM k Bool S Unit)
    (env : Environment Unit P) (world : World k S Unit P input) :
    NativeOpenExecution.step (machine i body) env (check world) =
      PMF.pure (if world.config.tapes.workTapeSymbols i = some false then
        NativeSequential.left checker (NativeSequential.resume body world) else stopped world) := by
  have hw : (check world).config.tapes.workTapeSymbols i =
      world.config.tapes.workTapeSymbols i := rfl
  simp only [NativeOpenExecution.step, check, Cfg.withState, machine] at hw ⊢
  rw [hw]
  split_ifs <;> simp only [PMF.bind_const]
  all_goals
    congr 1
    apply congrArg (fun cfg => (⟨cfg, world.memory⟩ : World k (S ⊕ Unit) Unit P input))
    apply Config.ext
    · simp [NativeSequential.resume, Sequential.left, Sequential.start,
        check, Config.step, Action.apply, Cfg.mapState, Cfg.withState]
    · simp [NativeSequential.resume, Sequential.left, Sequential.start,
        check, Config.step]

/-- The executed tape test either halts immediately or runs a whole actual round
and returns to the same test. No finite per-round clock or restart law is assumed. -/
theorem terminal_check (i : Fin k) (body : MultiTapePTM k Bool S Unit)
    (env : Environment Unit P) (world : World k S Unit P input) :
    NativeUnboundedExecution.terminal (machine i body) env (check world) =
      if world.config.tapes.workTapeSymbols i = some false then
        (NativeUnboundedExecution.terminal body env (NativeSequential.resume body world)).bind fun
          | none => PMF.pure none
          | some next => NativeUnboundedExecution.terminal (machine i body) env (check next)
      else PMF.pure (some (stopped world)) := by
  rw [NativeUnboundedExecution.terminal, StoppedProcess.terminal_step, step_check, PMF.pure_bind]
  split_ifs
  · exact terminal_round i body env (NativeSequential.resume body world)
  · exact StoppedProcess.terminal_halted _ _ (NativeUnboundedExecution.step_halted _ _) _ rfl

end Cslib.Probability.NativeFeedbackLoop
