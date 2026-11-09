/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Equivalence
public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# Clocked machine execution as a typed program

The transition-choice and query handlers express one machine run in the shared `OracleComp`
language. A deterministic handler returns its action; a fair-coin handler samples a bit and
selects that branch. The handlers are explicit semantic parameters: an arbitrary handler need
not be fair, efficient, or even respect the choices supplied by the transition table.

Each unit of fuel executes one table instruction. Submitting a query costs one instruction;
writing its buffer and reading its reply cost ordinary instructions. The handler's internal
computation is external to this clock. Resource predicates must fix the intended choice handler
and separately account for substituted oracle implementations.

Clock exhaustion retains the entire configuration. Pausing and resuming, and replacing either
handler by another program, preserve the program itself, hence its interaction with every
stateful interpreter and the final private state.

The interpreter and proof patterns are adapted from the cslib `crypto` branch's fair-coin
interpreter at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common choice mechanism and
the typed program interface of cslib PR #1129.

## Main definitions

* `Turing.MultiTapeMachine.runConfigFrom`: a clocked run retaining all tapes and channels.
* `Turing.MultiTapeMachine.runFrom`, `Turing.MultiTapeMachine.run`: observe the output word.

## Main results

* `Turing.MultiTapeMachine.runConfigFrom_add`: exact pause/resume equality of programs.
* `Turing.MultiTapeMachine.interpret_runConfigFrom`: interpretation commutes with execution.
* `Turing.MultiTapeMachine.runConfigFrom_toTM`: deterministic execution is the upstream run.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query}
  {input : List Symbol} [DecidableEq Oracle]

/-- Unfold a bounded run, retaining the entire configuration on halting or clock exhaustion. -/
def runConfigFrom (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) :
    ℕ → Config k Symbol State Oracle input → OracleComp spec (Config k Symbol State Oracle input)
  | 0, cfg => pure cfg
  | fuel + 1, cfg => match cfg.tapes.state with
    | none => pure cfg
    | some state => do
      let action ← choose (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols)
      match action with
      | .step action symbol move =>
        machine.runConfigFrom choose query fuel (cfg.step action symbol move)
      | .query oracle next =>
        let answer ← query oracle (cfg.channels oracle).queryBuffer
        machine.runConfigFrom choose query fuel (cfg.receive oracle next answer)

/-- Observe only the output word after a bounded execution. -/
def runFrom (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) : OracleComp spec (List Symbol) :=
  (fun final => final.tapes.output) <$> machine.runConfigFrom choose query fuel cfg

/-- Run from blank work and communication tapes. -/
def run (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (fuel : ℕ) (input : List Symbol) : OracleComp spec (List Symbol) :=
  machine.runFrom choose query fuel (machine.initialConfig input)

variable (machine : MultiTapeMachine k Symbol State Oracle Choose)
  (choose : Choose (Action k Symbol State Oracle) → OracleComp spec (Action k Symbol State Oracle))
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

@[simp] theorem runConfigFrom_zero (cfg : Config k Symbol State Oracle input) :
    machine.runConfigFrom choose query 0 cfg = pure cfg := rfl

@[simp] theorem runConfigFrom_halted (fuel : ℕ) (cfg : Config k Symbol State Oracle input)
    (h : cfg.tapes.state = none) :
    machine.runConfigFrom choose query fuel cfg = pure cfg := by
  cases fuel <;> simp [runConfigFrom, h]

@[simp] theorem runFrom_zero (cfg : Config k Symbol State Oracle input) :
    machine.runFrom choose query 0 cfg = pure cfg.tapes.output := by
  simp [runFrom]

/-- Pausing and resuming preserves the entire program and uses the sum of the two clocks. -/
theorem runConfigFrom_add (first second : ℕ) (cfg : Config k Symbol State Oracle input) :
    machine.runConfigFrom choose query (first + second) cfg =
      (machine.runConfigFrom choose query first cfg >>=
        machine.runConfigFrom choose query second) := by
  induction first generalizing cfg with
  | zero => simp
  | succ first ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFrom, hs]
    | some state =>
      simp only [Nat.succ_add, runConfigFrom, hs, bind_assoc]
      congr 1
      funext action
      cases action <;> simp [ih, bind_assoc]

/-- Resume a paused execution and then observe its output. -/
theorem runFrom_add (first second : ℕ) (cfg : Config k Symbol State Oracle input) :
    machine.runFrom choose query (first + second) cfg =
      (machine.runConfigFrom choose query first cfg >>= machine.runFrom choose query second) := by
  simp only [runFrom, runConfigFrom_add, map_bind]
  rfl

/-- Substituting either handler commutes with clocked execution, before interpreting any effects.
In particular, substitution does not reset the private state shared by calls. -/
theorem interpret_runConfigFrom {Query' : Type u} {spec' : OracleSpec.{u, 0} Query'}
    (handler : (q : Query) → OracleComp spec' (spec q)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    OracleComp.interpret handler (machine.runConfigFrom choose query fuel cfg) =
      machine.runConfigFrom (fun choices => OracleComp.interpret handler (choose choices))
        (fun oracle word => OracleComp.interpret handler (query oracle word)) fuel cfg := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFrom, hs]
    | some state =>
      simp only [runConfigFrom, hs, OracleComp.interpret_bind]
      congr 1
      funext action
      cases action <;> simp [ih]

/-- Substituting handlers preserves the complete output program. -/
theorem interpret_run {Query' : Type u} {spec' : OracleSpec.{u, 0} Query'}
    (handler : (q : Query) → OracleComp spec' (spec q)) (fuel : ℕ) (input : List Symbol) :
    OracleComp.interpret handler (machine.run choose query fuel input) =
      machine.run (fun choices => OracleComp.interpret handler (choose choices))
        (fun oracle word => OracleComp.interpret handler (query oracle word)) fuel input := by
  simp only [run, runFrom, OracleComp.interpret_map, interpret_runConfigFrom]

/-- Every supported execution writes at most one output symbol per instruction, regardless of
the sizes of oracle replies or the private state shared by the handlers. -/
theorem length_output_runConfigFrom_le {OracleState : Type}
    (oracle : (q : Query) → StateT OracleState PMF (spec q)) (fuel : ℕ)
    (cfg final : Config k Symbol State Oracle input) (s s' : OracleState)
    (h : (final, s') ∈
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query fuel cfg)).run s).support) :
    final.tapes.output.length ≤ cfg.tapes.output.length + fuel := by
  induction fuel generalizing cfg s with
  | zero =>
    simp only [runConfigFrom_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    simp [h.1]
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [runConfigFrom, hs, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      simp [h.1]
    | some state =>
      simp only [runConfigFrom, hs, OracleComp.interpret_bind, StateT.run_bind,
        Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at h
      obtain ⟨⟨action, nextState⟩, _, h⟩ := h
      cases action with
      | step action symbol move =>
        have hout := ih (cfg.step action symbol move) nextState h
        have hstep : (cfg.step action symbol move).tapes.output.length ≤
            cfg.tapes.output.length + 1 := by
          simp only [Config.step, Turing.Action.apply, List.length_append]
          exact Nat.add_le_add_left action.output.length_toList_le _
        lia
      | query op next =>
        simp only [OracleComp.interpret_bind, StateT.run_bind,
          Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at h
        obtain ⟨⟨answer, nextState⟩, _, h⟩ := h
        have hout := ih (cfg.receive op next answer) nextState h
        simp only [Config.receive] at hout
        lia

/-- Observing only the output preserves the supported-output bound. -/
theorem length_output_runFrom_le {OracleState : Type}
    (oracle : (q : Query) → StateT OracleState PMF (spec q)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) (s s' : OracleState) (output : List Symbol)
    (h : (output, s') ∈
      ((OracleComp.interpret oracle (machine.runFrom choose query fuel cfg)).run s).support) :
    output.length ≤ cfg.tapes.output.length + fuel := by
  simp only [runFrom, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff] at h
  obtain ⟨⟨final, finalState⟩, hfinal, heq⟩ := h
  rw [← (Prod.mk.inj heq).1]
  exact machine.length_output_runConfigFrom_le choose query oracle fuel cfg final s finalState
    hfinal

/-- The deterministic run program computes exactly the iterated deterministic step. -/
theorem runConfigFrom_pure {Symbol State Query : Type} {input : List Symbol}
    {spec : Cslib.OracleSpec.{0, 0} Query}
    (machine : MultiTapeMachine k Symbol State Empty Id) (fuel : ℕ)
    (cfg : Config k Symbol State Empty input) :
    machine.runConfigFrom (spec := spec) pure (fun oracle => oracle.elim) fuel cfg =
      pure (machine.step^[fuel] cfg) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    cases hs : cfg.tapes.state with
    | none =>
      have hstep : machine.step cfg = cfg := by simp [step, hs]
      simp [runConfigFrom, hs, hstep, Function.iterate_fixed hstep]
    | some state =>
      simp only [runConfigFrom, hs, pure_bind, step]
      cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
      | step action symbol move => exact ih _
      | query oracle _ => exact oracle.elim

/-- Removing the empty channels from a deterministic run program gives the upstream clocked run. -/
theorem runConfigFrom_toTM {Symbol State Query : Type} {input : List Symbol}
    {spec : Cslib.OracleSpec.{0, 0} Query}
    (machine : MultiTapeMachine k Symbol State Empty Id) (fuel : ℕ)
    (cfg : Config k Symbol State Empty input) :
    Config.tapes <$>
        machine.runConfigFrom (spec := spec) pure (fun oracle => oracle.elim) fuel cfg =
      pure (machine.toTM.runFrom cfg.tapes fuel) := by
  rw [runConfigFrom_pure, map_pure]
  exact congrArg pure ((show Function.Semiconj Config.tapes machine.step machine.toTM.step from
    step_toTM machine).iterate_right fuel cfg)

end Turing.MultiTapeMachine
