/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Simulation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.AuxiliaryTape

/-!
# An internal clock on a work tape

`withClock` reserves a last work tape for a unary budget. Each true cell permits one source
instruction, implemented by two target instructions. The first other cell stops the controller.
After the source halts, the controller consumes the remaining budget without changing source
tapes or communication channels. Preparing this tape is a separate computation: a machine does
not receive a polynomial-sized budget for free.

The choice interpreter must commute with mapping and interpret a constant choice as a pure
result with unchanged private state. For probabilistic machines, stateless coin draws satisfy
these conditions even when controller instructions discard their result. Query programs may
modify shared private state.

## Main definitions

* `Turing.MultiTapeMachine.withClock`: consume a budget stored on a fresh work tape.
* `Turing.MultiTapeMachine.AuxiliaryTape.config`: retain source data beside the clock tape.

## Main results

* `Turing.MultiTapeMachine.run_interpret_runConfigFrom_withClock_add`: a budget of `t` cells
  reproduces the externally clocked source in `2 * t + 1` instructions, with arbitrary padding.
* `Turing.MultiTapeMachine.withClock_halted`: every supported final configuration has halted.

## References

Adapted from MultiTape/Oracle/Clock.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed program interface.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib AuxiliaryTape

universe u v

variable {k : ℕ} {State Oracle : Type} {Choose : Type → Type v} {input : List Bool}

namespace Clock

/-- A phase bit and the source's optional control state. -/
abbrev Control (State : Type) := Bool × Option State

/-- Leave all source tapes unchanged. -/
def idle (next : Option (Control State)) : Turing.Action (k + 1) Bool (Control State) :=
  AuxiliaryTape.move next 0

/-- Advance the budget head while leaving all source tapes unchanged. -/
def tick (next : Option State) : Turing.Action (k + 1) Bool (Control State) :=
  AuxiliaryTape.move (some (false, next)) 1

/-- Lift either a tape instruction or an oracle submission to the clock controller. -/
def liftInstruction : Action k Bool State Oracle → Action (k + 1) Bool (Control State) Oracle
  | .step action symbol move => .step (AuxiliaryTape.liftAction true action) symbol move
  | .query oracle next => .query oracle (true, some next)

end Clock

/-- Run under a unary budget on the last work tape; its construction is a separate computation. -/
@[simps! initial] def withClock [Applicative Choose]
    (machine : MultiTapeMachine k Bool State Oracle Choose) :
    MultiTapeMachine (k + 1) Bool (Clock.Control State) Oracle Choose where
  initial := (false, some machine.initial)
  tr control symbol work answer :=
    if control.1 then pure (.step (Clock.tick control.2) (fun _ => none) (fun _ => 0))
    else if work (Fin.last k) = some true then
      match control.2 with
      | none => pure (.step (Clock.idle (some (true, none))) (fun _ => none) (fun _ => 0))
      | some state => Clock.liftInstruction <$>
        machine.tr state symbol (fun i => work i.castSucc) answer
    else pure (.step (Clock.idle none) (fun _ => none) (fun _ => 0))

/-- Unfold one controller instruction without unfolding the machine in its continuation. -/
theorem withClock_tr [Applicative Choose] (machine : MultiTapeMachine k Bool State Oracle Choose)
    (control : Clock.Control State) (symbol : Option Bool) (work : Fin (k + 1) → Option Bool)
    (answer : Oracle → Option Bool) :
    machine.withClock.tr control symbol work answer =
      if control.1 then pure (.step (Clock.tick control.2) (fun _ => none) (fun _ => 0))
      else if work (Fin.last k) = some true then
        match control.2 with
        | none => pure (.step (Clock.idle (some (true, none))) (fun _ => none) (fun _ => 0))
        | some state => Clock.liftInstruction <$>
          machine.tr state symbol (fun i => work i.castSucc) answer
      else pure (.step (Clock.idle none) (fun _ => none) (fun _ => 0)) := rfl

namespace Clock

theorem step_tick (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) :
    (config cfg tape position true).step (tick cfg.tapes.state) (fun _ => none) (fun _ => 0) =
      config cfg tape (position + 1) false := by
  simpa [tick] using step_move cfg tape position true false 1

theorem step_pause (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) :
    (config cfg tape position false).step (idle (some (true, cfg.tapes.state)))
        (fun _ => none) (fun _ => 0) = config cfg tape position true := by
  simpa [idle] using step_move cfg tape position false true 0

end Clock

variable [Applicative Choose] [DecidableEq Oracle]
  {Query : Type u} {spec : OracleSpec.{u, 0} Query} {OracleState : Type}
  (machine : MultiTapeMachine k Bool State Oracle Choose)
  (choose : {α : Type} → Choose α → OracleComp spec α)
  (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
    choose (f <$> choices) = f <$> choose choices)
  (query : Oracle → List Bool → OracleComp spec (List Bool))
  (oracle : (q : Query) → StateT OracleState PMF (spec q))
  (hpure : ∀ {α : Type} (a : α) (s : OracleState),
    (OracleComp.interpret oracle (choose (pure a))).run s = PMF.pure (a, s))

include hpure

namespace Clock

/-- The clock-advance instruction leaves the source and private interpreter state unchanged. -/
theorem run_interpret_tick (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (s : OracleState) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query 1 (config cfg tape position true))).run s =
      PMF.pure (config cfg tape (position + 1) false, s) := by
  simp only [runConfigFrom, config_state, withClock_tr, ↓reduceIte, step_tick,
    OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
    hpure, PMF.pure_bind, OracleComp.interpret_pure, StateT.run_pure,
    Probability.PMF.monad_pure_eq_pure]

include hchoose in
/-- One available budget cell permits one source instruction and one clock advance. -/
theorem run_interpret_pair (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (s : OracleState)
    (hcell : tape position = some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query 2 (config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query 1 cfg)).run s).map
        (fun (final, s') => (config final tape (position + 1) false, s')) := by
  conv_lhs => rw [runConfigFrom]
  conv_rhs => rw [runConfigFrom]
  simp only [config_state, withClock_tr, Bool.false_eq_true, ↓reduceIte,
    config_workTapeSymbols_last, hcell, config_inputSymbol,
    config_workTapeSymbols_castSucc, config_answerSymbols]
  cases hs : cfg.tapes.state with
  | none =>
    simp only [OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, hpure, PMF.pure_bind]
    rw [← hs, step_pause, run_interpret_tick machine choose query oracle hpure]
    simp
  | some state =>
    simp only [hchoose, bind_map_left, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
    congr 1 with result : 1
    rcases result with ⟨instruction, s'⟩
    cases instruction with
    | step action symbol move =>
      simp [liftInstruction, step_liftAction, run_interpret_tick machine choose query oracle hpure]
    | query op next =>
      simp only [liftInstruction, config_channels, OracleComp.interpret_bind, StateT.run_bind,
        Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
      congr 1 with result : 1
      rcases result with ⟨answer, s''⟩
      simp [receive_config, run_interpret_tick machine choose query oracle hpure]

include hchoose in
/-- A bounded simulation advances the clock head once per source instruction. -/
theorem run_interpret_prefix (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (fuel : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < fuel → tape (position + i) = some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * fuel)
        (config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query fuel cfg)).run s).map
        (fun (final, s') => (config final tape (position + fuel) false, s')) := by
  have hstep : ∀ i, i < fuel → ∀ (cfg : Config k Bool State Oracle input) (s : OracleState),
      (OracleComp.interpret oracle
        (machine.withClock.runConfigFrom choose query 2
          (config cfg tape (position + i) false))).run s =
        ((OracleComp.interpret oracle (machine.runConfigFrom choose query 1 cfg)).run s).map
          (fun (final, s') => (config final tape (position + (i + 1 : ℕ)) false, s')) := by
    intro i hi cfg s
    simpa [Nat.cast_add, add_assoc] using
      run_interpret_pair machine choose hchoose query oracle hpure cfg tape (position + i) s
        (hbudget i hi)
  simpa only [Nat.cast_zero, add_zero] using
    run_interpret_runConfigFrom_mul_indexed machine machine.withClock choose choose query query
      2 fuel (fun i cfg => config cfg tape (position + i) false) oracle hstep cfg s

/-- At the budget's end, halt without another source instruction or oracle call. -/
theorem run_interpret_stop (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (s : OracleState) (hstop : tape position ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query 1 (config cfg tape position false))).run s =
      PMF.pure (stopped cfg tape position, s) := by
  simp only [runConfigFrom, config_state, withClock_tr, Bool.false_eq_true, ↓reduceIte,
    config_workTapeSymbols_last, hstop, OracleComp.interpret_bind, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind, hpure, PMF.pure_bind, idle, step_stop,
    OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure]

end Clock

include hchoose

/-- A prepared unary budget implements the source's external cutoff with actual halting.
All source tapes, channels, and private interpreter state are retained; the source control state
is discarded when the controller halts. Constant choices must have no interpreted effect. -/
theorem run_interpret_runConfigFrom_withClock (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * budget + 1)
        (AuxiliaryTape.config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query budget cfg)).run s).map
        (fun (final, s') => (AuxiliaryTape.stopped final tape (position + budget), s')) := by
  rw [runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind,
    Clock.run_interpret_prefix machine choose hchoose query oracle hpure cfg tape position budget s
      hbudget, PMF.bind_map]
  simp only [Function.comp_def,
    Clock.run_interpret_stop machine choose query oracle hpure _ tape _ _ hstop]
  rfl

/-- Extra time after budget exhaustion cannot change the configuration or private state. -/
theorem run_interpret_runConfigFrom_withClock_add (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * budget + 1 + padding)
        (AuxiliaryTape.config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query budget cfg)).run s).map
        (fun (final, s') => (AuxiliaryTape.stopped final tape (position + budget), s')) := by
  rw [runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind,
    run_interpret_runConfigFrom_withClock machine choose hchoose query oracle hpure cfg tape
      position budget s hbudget hstop, PMF.bind_map]
  simp only [Function.comp_def, runConfigFrom_halted _ _ _ _ _
    (AuxiliaryTape.stopped_state ..),
    OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure]
  rfl

/-- In particular, the output and final private state agree with the original clocked run. -/
theorem run_interpret_runFrom_withClock (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runFrom choose query (2 * budget + 1 + padding)
        (AuxiliaryTape.config cfg tape position false))).run s =
      (OracleComp.interpret oracle (machine.runFrom choose query budget cfg)).run s := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (run_interpret_runConfigFrom_withClock_add machine choose hchoose query oracle hpure cfg tape
      position budget padding s hbudget hstop)
  simpa [runFrom, OracleComp.interpret_map, StateT.run_map, PMF.map_comp, Function.comp_def] using h

/-- Every supported final configuration is halted when the prepared budget expires. -/
theorem withClock_halted (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true)
    (final : Config (k + 1) Bool (Clock.Control State) Oracle input) (s' : OracleState)
    (hfinal : (final, s') ∈ ((OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * budget + 1 + padding)
        (AuxiliaryTape.config cfg tape position false))).run s).support) :
    final.tapes.state = none := by
  rw [run_interpret_runConfigFrom_withClock_add machine choose hchoose query oracle hpure cfg tape
    position budget padding s hbudget hstop] at hfinal
  obtain ⟨⟨sourceFinal, sourceState⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  exact (congrArg (fun result => result.1.tapes.state) heq).symm

end Turing.MultiTapeMachine
