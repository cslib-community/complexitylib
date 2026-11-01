/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Halting
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Sequencing effectful machines

The first machine's halting transition transfers control to the second, retaining every tape
and communication channel. The transition-choice mechanism only needs to support mapping its
actions. Execution commutes with this mapping when the choice interpreter does; in particular,
deterministic choices and sampling a supplied coin have this property.

Two actual halting bounds add even when stopping times depend on random choices or oracle
answers. The distributional theorem retains the final configuration and private interpreter
state. This is sequencing on shared tapes: supplying fresh encoded input and clean communication
state is a separate obligation of a higher-level composition compiler.

## Main definitions

* `Turing.MultiTapeMachine.seq`: sequential composition, with no extra handoff instruction.

## Main results

* `Turing.MultiTapeMachine.Sequential.runConfigFrom_right`: after handoff the continuation's
  complete program is unchanged, up to embedding its control states.
* `Turing.MultiTapeMachine.run_interpret_runConfigFrom_seq`: the joint distribution of a
  sequential run is the monadic composition of the two phases.
* `Turing.MultiTapeMachine.interpret_runConfigFrom_seq_list`: exact List bind, including repeated
  equal configurations, under the two phase halting bounds.
* `Turing.MultiTapeMachine.toTM_seq`: the deterministic compiler is exactly upstream's `seq`.

## References

Adapted from MultiTape/Oracle/Sequential.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed program interface.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State₀ State₁ Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} {input : List Symbol}

namespace Sequential

/-- Embed a first-phase action, transferring a halt directly to the continuation. -/
def leftAction (next : State₁) : Action k Symbol State₀ Oracle →
    Action k Symbol (State₀ ⊕ State₁) Oracle
  | .step action symbol move =>
    .step { action with state := some (action.state.elim (.inr next) .inl) } symbol move
  | .query oracle next => .query oracle (.inl next)

/-- Embed a continuation's action, preserving halting. -/
def rightAction : Action k Symbol State₁ Oracle → Action k Symbol (State₀ ⊕ State₁) Oracle
  | .step action symbol move => .step { action with state := action.state.map .inr } symbol move
  | .query oracle next => .query oracle (.inr next)

/-- Embed the first phase, dispatching its halt to the continuation's initial state. -/
def left (second : MultiTapeMachine k Symbol State₁ Oracle Choose)
    (cfg : Config k Symbol State₀ Oracle input) : Config k Symbol (State₀ ⊕ State₁) Oracle input :=
  { cfg with
    tapes := cfg.tapes.mapState (fun state => some (state.elim (.inr second.initial) .inl)) }

/-- Start the continuation on the complete tape and communication state left by the first phase. -/
def start (second : MultiTapeMachine k Symbol State₁ Oracle Choose)
    (cfg : Config k Symbol State₀ Oracle input) : Config k Symbol State₁ Oracle input :=
  { cfg with tapes := cfg.tapes.withState (some second.initial) }

/-- Embed a continuation's configuration, preserving halting and every tape. -/
def right (cfg : Config k Symbol State₁ Oracle input) :
    Config k Symbol (State₀ ⊕ State₁) Oracle input :=
  { cfg with tapes := cfg.tapes.mapState (Option.map .inr) }

theorem left_halted (second : MultiTapeMachine k Symbol State₁ Oracle Choose)
    (cfg : Config k Symbol State₀ Oracle input) (h : cfg.tapes.state = none) :
    left second cfg = right (start second cfg) := by
  simp [left, start, right, Cfg.mapState, Cfg.withState, h]

end Sequential

open Sequential

/-- Transfer control when the first machine halts, retaining all tapes and oracle channels. -/
@[simps! initial] def seq [Functor Choose]
    (first : MultiTapeMachine k Symbol State₀ Oracle Choose)
    (second : MultiTapeMachine k Symbol State₁ Oracle Choose) :
    MultiTapeMachine k Symbol (State₀ ⊕ State₁) Oracle Choose where
  initial := .inl first.initial
  tr state symbol work answer := match state with
    | .inl state => leftAction second.initial <$> first.tr state symbol work answer
    | .inr state => rightAction <$> second.tr state symbol work answer

variable [Functor Choose] [DecidableEq Oracle]
  (first : MultiTapeMachine k Symbol State₀ Oracle Choose)
  (second : MultiTapeMachine k Symbol State₁ Oracle Choose)
  (choose : {α : Type} → Choose α → OracleComp spec α)
  (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
    choose (f <$> choices) = f <$> choose choices)
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

include hchoose

namespace Sequential

/-- While the first phase is active, one instruction mirrors its complete program. -/
theorem runConfigFrom_one (cfg : Config k Symbol State₀ Oracle input)
    (h : cfg.tapes.state ≠ none) :
    (first.seq second).runConfigFrom choose query 1 (left second cfg) =
      left second <$> first.runConfigFrom choose query 1 cfg := by
  cases hs : cfg.tapes.state with
  | none => exact (h hs).elim
  | some state =>
    simp only [runConfigFrom, left, Cfg.mapState, hs, Option.elim_some,
      Cfg.inputSymbol, seq, hchoose, bind_map_left, map_bind]
    congr 1
    funext action
    cases action <;> simp [leftAction, left, Config.step, Config.receive, Turing.Action.apply,
      Cfg.mapState]

/-- After handoff, the continuation runs its unchanged program in right states. -/
theorem runConfigFrom_right (fuel : ℕ) (cfg : Config k Symbol State₁ Oracle input) :
    (first.seq second).runConfigFrom choose query fuel (right cfg) =
      right <$> second.runConfigFrom choose query fuel cfg :=
  runConfigFrom_mapState second (first.seq second) choose hchoose query
    Sum.inr (fun _ _ _ _ => rfl) fuel cfg

end Sequential

omit hchoose in
/-- In the deterministic effect-free case, this is exactly upstream's sequential compiler. -/
theorem toTM_seq (first : MultiTapeMachine k Symbol State₀ Empty Id)
    (second : MultiTapeMachine k Symbol State₁ Empty Id) :
    (first.seq second).toTM = first.toTM.seq second.toTM := by
  simp only [toTM, MultiTapeTM.seq, MultiTapeTM.combine, MultiTapeMachine.seq]
  congr 1
  funext state symbol work
  cases state with
  | inl state =>
    simp only [Sum.elim_inl, MultiTapeTM.adaptedTr, MultiTapeNTM.Adapter.mapState,
      id_eq, MultiTapeTM.tr_ofTr]
    cases first.tr state symbol work Empty.elim with
    | step action symbol move => rfl
    | query oracle next => exact oracle.elim
  | inr state =>
    simp only [Sum.elim_inr, MultiTapeTM.adaptedTr, MultiTapeNTM.Adapter.mapState,
      id_eq, MultiTapeTM.tr_ofTr]
    cases second.tr state symbol work Empty.elim with
    | step action symbol move => rfl
    | query oracle next => exact oracle.elim

/-- List interpretation of sequencing is exact list bind, retaining repeated equal endpoints.
The phase bounds are actual halting bounds. Excluding stuck branches is a separate obligation,
since an empty interpreted choice has no endpoints. -/
theorem interpret_runConfigFrom_seq_list (oracle : (q : Query) → List (spec q))
    (cfg : Config k Symbol State₀ Oracle input) (firstTime secondTime : ℕ)
    (hfirst : ∀ result ∈ OracleComp.interpret oracle
      (first.runConfigFrom choose query firstTime cfg), result.tapes.state = none)
    (hsecond : ∀ result ∈ OracleComp.interpret oracle
      (first.runConfigFrom choose query firstTime cfg),
      ∀ final ∈ OracleComp.interpret oracle
        (second.runConfigFrom choose query secondTime (start second result)),
        final.tapes.state = none) :
    OracleComp.interpret oracle ((first.seq second).runConfigFrom choose query
      (firstTime + secondTime) (left second cfg)) =
      (OracleComp.interpret oracle (first.runConfigFrom choose query firstTime cfg)).flatMap
        (fun result => (OracleComp.interpret oracle
          (second.runConfigFrom choose query secondTime (start second result))).map right) := by
  induction firstTime generalizing cfg with
  | zero =>
    have hhalt := hfirst cfg (by simp)
    simp only [Nat.zero_add, runConfigFrom_zero, OracleComp.interpret_pure,
      List.pure_def, List.flatMap_singleton]
    rw [left_halted second cfg hhalt, Sequential.runConfigFrom_right first second choose hchoose,
      OracleComp.interpret_map]
    rfl
  | succ firstTime ih =>
    by_cases hhalt : cfg.tapes.state = none
    · have hsecond' := hsecond cfg (by simp [hhalt])
      simp only [runConfigFrom_halted first choose query _ cfg hhalt, OracleComp.interpret_pure,
        List.pure_def, List.flatMap_singleton]
      rw [left_halted second cfg hhalt, Sequential.runConfigFrom_right first second choose hchoose,
        OracleComp.interpret_map, Nat.add_comm (firstTime + 1) secondTime,
        interpret_runConfigFrom_add_of_halted_list second choose query oracle _
          secondTime (firstTime + 1) hsecond']
      rfl
    · have hsplit : firstTime + 1 = 1 + firstTime := by lia
      have hstep : firstTime + 1 + secondTime = 1 + (firstTime + secondTime) := by lia
      rw [hstep, runConfigFrom_add,
        Sequential.runConfigFrom_one first second choose hchoose query cfg hhalt,
        OracleComp.interpret_bind, OracleComp.interpret_map]
      change List.flatMap _ (List.map _ _) = _
      rw [List.flatMap_map, hsplit, runConfigFrom_add, OracleComp.interpret_bind]
      change List.flatMap _ _ = List.flatMap _ (List.flatMap _ _)
      rw [List.flatMap_assoc]
      apply List.flatMap_congr
      intro next hnext
      apply ih
      · intro final hfinal
        apply hfirst final
        rw [hsplit, runConfigFrom_add, OracleComp.interpret_bind]
        exact List.mem_flatMap.mpr ⟨next, hnext, hfinal⟩
      · intro final hfinal
        apply hsecond final
        rw [hsplit, runConfigFrom_add, OracleComp.interpret_bind]
        exact List.mem_flatMap.mpr ⟨next, hnext, hfinal⟩

/-- Sequential halting bounds add even when the first stopping time depends on random choices.
The equality retains the final configuration and the interpreter's private state. -/
theorem run_interpret_runConfigFrom_seq {OracleState : Type}
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (cfg : Config k Symbol State₀ Oracle input) (firstTime secondTime : ℕ) (s : OracleState)
    (hfirst : ∀ result ∈
      ((OracleComp.interpret oracle
        (first.runConfigFrom choose query firstTime cfg)).run s).support,
      result.1.tapes.state = none)
    (hsecond : ∀ result ∈
      ((OracleComp.interpret oracle
        (first.runConfigFrom choose query firstTime cfg)).run s).support,
      ∀ final ∈ ((OracleComp.interpret oracle
        (second.runConfigFrom choose query secondTime
          (start second result.1))).run result.2).support,
        final.1.tapes.state = none) :
    (OracleComp.interpret oracle ((first.seq second).runConfigFrom choose query
      (firstTime + secondTime) (left second cfg))).run s =
      ((OracleComp.interpret oracle (first.runConfigFrom choose query firstTime cfg)).run s).bind
        (fun result => ((OracleComp.interpret oracle
          (second.runConfigFrom choose query secondTime (start second result.1))).run result.2).map
          (fun (final, s') => (right final, s'))) := by
  induction firstTime generalizing cfg s with
  | zero =>
    have hhalt := hfirst (cfg, s) (by simp)
    simp only [Nat.zero_add, runConfigFrom_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
    rw [left_halted second cfg hhalt, Sequential.runConfigFrom_right first second choose hchoose,
      OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  | succ firstTime ih =>
    by_cases hhalt : cfg.tapes.state = none
    · have hsecond' := hsecond (cfg, s) (by simp [hhalt])
      simp only [runConfigFrom_halted first choose query _ cfg hhalt, OracleComp.interpret_pure,
        StateT.run_pure, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
      rw [left_halted second cfg hhalt, Sequential.runConfigFrom_right first second choose hchoose,
        OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
        Nat.add_comm (firstTime + 1) secondTime,
        run_interpret_runConfigFrom_add_of_halted second choose query oracle _
          secondTime (firstTime + 1) s hsecond']
    · have hsplit : firstTime + 1 = 1 + firstTime := by lia
      have hstep : firstTime + 1 + secondTime = 1 + (firstTime + secondTime) := by lia
      rw [hstep, runConfigFrom_add,
        Sequential.runConfigFrom_one first second choose hchoose query cfg hhalt,
        OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
        OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.bind_map]
      rw [hsplit, runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
        Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
      apply Probability.PMF.bind_congr_on_support
      rintro ⟨next, s'⟩ hnext
      dsimp only [Function.comp_def]
      apply ih
      · intro final hfinal
        apply hfirst final
        rw [hsplit, runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
          Probability.PMF.monad_bind_eq_bind]
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨(next, s'), hnext, hfinal⟩
      · intro final hfinal
        apply hsecond final
        rw [hsplit, runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
          Probability.PMF.monad_bind_eq_bind]
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨(next, s'), hnext, hfinal⟩

/-- A deterministic preparation phase hands its exact restored configuration to the continuation. -/
theorem run_interpret_runConfigFrom_seq_pure {OracleState : Type}
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (cfg ready : Config k Symbol State₀ Oracle input) (firstTime secondTime : ℕ) (s : OracleState)
    (hfirst : (OracleComp.interpret oracle
      (first.runConfigFrom choose query firstTime cfg)).run s = PMF.pure (ready, s))
    (hready : ready.tapes.state = none)
    (hsecond : ∀ final ∈ ((OracleComp.interpret oracle
      (second.runConfigFrom choose query secondTime (start second ready))).run s).support,
      final.1.tapes.state = none) :
    (OracleComp.interpret oracle ((first.seq second).runConfigFrom choose query
      (firstTime + secondTime) (left second cfg))).run s =
      ((OracleComp.interpret oracle
        (second.runConfigFrom choose query secondTime (start second ready))).run s).map
        (fun (final, s') => (right final, s')) := by
  rw [run_interpret_runConfigFrom_seq first second choose hchoose query oracle cfg firstTime
    secondTime s (by simpa [hfirst] using hready) (by simpa [hfirst] using hsecond), hfirst,
    PMF.pure_bind]

/-- Observing only the output gives the usual monadic sequencing law under the same bounds. -/
theorem run_interpret_runFrom_seq {OracleState : Type}
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (cfg : Config k Symbol State₀ Oracle input) (firstTime secondTime : ℕ) (s : OracleState)
    (hfirst : ∀ result ∈
      ((OracleComp.interpret oracle
        (first.runConfigFrom choose query firstTime cfg)).run s).support,
      result.1.tapes.state = none)
    (hsecond : ∀ result ∈
      ((OracleComp.interpret oracle
        (first.runConfigFrom choose query firstTime cfg)).run s).support,
      ∀ final ∈ ((OracleComp.interpret oracle
        (second.runConfigFrom choose query secondTime
          (start second result.1))).run result.2).support,
        final.1.tapes.state = none) :
    (OracleComp.interpret oracle ((first.seq second).runFrom choose query
      (firstTime + secondTime) (left second cfg))).run s =
      ((OracleComp.interpret oracle (first.runConfigFrom choose query firstTime cfg)).run s).bind
        (fun result => (OracleComp.interpret oracle
          (second.runFrom choose query secondTime (start second result.1))).run result.2) := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (run_interpret_runConfigFrom_seq first second choose hchoose query oracle cfg firstTime
      secondTime s hfirst hsecond)
  simpa [runFrom, OracleComp.interpret_map, StateT.run_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, right] using h

end Turing.MultiTapeMachine
