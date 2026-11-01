/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Halting
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Reserving work tapes for effectful machines

Reindexing the source's tapes leaves every additional tape and head unchanged. The construction
uses upstream's configuration embedding and preserves the entire typed execution program, hence
also the joint distribution of configuration and private interpreter state. It requires only that
the choice interpreter commute with mapping; coin draws may be stateful.

## Main definitions

* `Turing.MultiTapeMachine.extendTapes`: run on tapes selected by an embedding.
* `Turing.MultiTapeMachine.Config.embed`: retain arbitrary data on the additional tapes.

## Main results

* `Turing.MultiTapeMachine.runConfigFrom_embed`: reindexing preserves the full clocked program.
* `Turing.MultiTapeMachine.toTM_extendTapes`: agreement with upstream's deterministic compiler.

## References

Adapted from MultiTape/Oracle/ExtendTapes.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed program interface.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k k' : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} {input : List Symbol}

/-- Reindex a tape action, leaving every additional tape and head untouched. -/
def extendAction (action : Turing.Action k Symbol State) (e : Fin k ↪ Fin k') :
    Turing.Action k' Symbol State where
  inputTape := action.inputTape
  workTapes := fun i => match MultiTapeTM.partialInv e i with
    | some j => action.workTapes j
    | none => (none, 0)
  output := action.output
  state := action.state

/-- Reindex ordinary tapes while retaining communication instructions verbatim. -/
def Action.extendTapes (e : Fin k ↪ Fin k') :
    Action k Symbol State Oracle → Action k' Symbol State Oracle
  | .step action symbol move => .step (extendAction action e) symbol move
  | .query oracle next => .query oracle next

/-- Run on the tapes selected by `e`, preserving all other tapes and every oracle interaction. -/
@[simps! initial] def extendTapes [Functor Choose]
    (machine : MultiTapeMachine k Symbol State Oracle Choose) (e : Fin k ↪ Fin k') :
    MultiTapeMachine k' Symbol State Oracle Choose where
  initial := machine.initial
  tr state symbol work answer :=
    Action.extendTapes e <$> machine.tr state symbol (fun i => work (e i)) answer

/-- Unfold a reindexed transition without unfolding its machine in a recursive continuation. -/
theorem extendTapes_tr [Functor Choose] (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (e : Fin k ↪ Fin k') (state : State) (symbol : Option Symbol)
    (work : Fin k' → Option Symbol) (answer : Oracle → Option Symbol) :
    (machine.extendTapes e).tr state symbol work answer =
      Action.extendTapes e <$> machine.tr state symbol (fun i => work (e i)) answer := rfl

/-- A source configuration with arbitrary contents and head positions on additional tapes. -/
def Config.embed (cfg : Config k Symbol State Oracle input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    Config k' Symbol State Oracle input :=
  { cfg with tapes := MultiTapeTM.embed e cfg.tapes extraTapes extraPos }

@[simp] theorem Config.embed_state (cfg : Config k Symbol State Oracle input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).tapes.state = cfg.tapes.state := rfl

@[simp] theorem Config.embed_inputSymbol (cfg : Config k Symbol State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem Config.embed_workTapeSymbols (cfg : Config k Symbol State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ)
    (i : Fin k) :
    (cfg.embed e extraTapes extraPos).tapes.workTapeSymbols (e i) =
      cfg.tapes.workTapeSymbols i :=
  MultiTapeTM.embed_workTapeSymbols_embed e cfg.tapes extraTapes extraPos i

@[simp] theorem Config.embed_channels (cfg : Config k Symbol State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).channels = cfg.channels := rfl

@[simp] theorem Config.embed_answerSymbols (cfg : Config k Symbol State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem Config.embed_output (cfg : Config k Symbol State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).tapes.output = cfg.tapes.output := rfl

theorem Config.step_embed (cfg : Config k Symbol State Oracle input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    (cfg.embed e extraTapes extraPos).step (extendAction action e) symbol move =
      (cfg.step action symbol move).embed e extraTapes extraPos := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    simp only [Config.step, Config.embed, extendAction, Turing.Action.apply, MultiTapeTM.embed] <;>
    cases MultiTapeTM.partialInv e i <;> simp

theorem Config.receive_embed [DecidableEq Oracle] (cfg : Config k Symbol State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ)
    (oracle : Oracle) (next : State) (answer : List Symbol) :
    (cfg.embed e extraTapes extraPos).receive oracle next answer =
      (cfg.receive oracle next answer).embed e extraTapes extraPos := rfl

variable [Functor Choose] [DecidableEq Oracle]
  (machine : MultiTapeMachine k Symbol State Oracle Choose) (e : Fin k ↪ Fin k')
  (choose : {α : Type} → Choose α → OracleComp spec α)
  (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
    choose (f <$> choices) = f <$> choose choices)
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

include hchoose

/-- Reindexing preserves the entire program, including all unused tape contents and heads. -/
theorem runConfigFrom_embed (cfg : Config k Symbol State Oracle input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    (machine.extendTapes e).runConfigFrom choose query fuel (cfg.embed e extraTapes extraPos) =
      (fun final => final.embed e extraTapes extraPos) <$>
        machine.runConfigFrom choose query fuel cfg := by
  apply runConfigFrom_map machine (machine.extendTapes e) choose choose query query
    (fun final => final.embed e extraTapes extraPos) ?_ fuel cfg
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [runConfigFrom, hs]
  | some state =>
    simp only [runConfigFrom, Config.embed_state, hs, Config.embed_inputSymbol,
      Config.embed_workTapeSymbols, Config.embed_answerSymbols, extendTapes_tr, hchoose,
      bind_map_left, map_bind]
    congr 1
    funext action
    cases action <;> simp [Action.extendTapes, Config.step_embed, Config.receive_embed]

/-- The additional work tapes do not affect the observable output program. -/
theorem runFrom_embed (cfg : Config k Symbol State Oracle input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    (machine.extendTapes e).runFrom choose query fuel (cfg.embed e extraTapes extraPos) =
      machine.runFrom choose query fuel cfg := by
  simp [runFrom, runConfigFrom_embed machine e choose hchoose query, Functor.map_map]

omit hchoose [DecidableEq Oracle] in
/-- Reserving additional tapes starts them blank, with every work head at zero. -/
theorem initialConfig_extendTapes (input : List Symbol) :
    (machine.extendTapes e).initialConfig input =
      (machine.initialConfig input).embed e (fun _ _ => none) (fun _ => 0) := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    simp only [initialConfig, Cfg.init, Config.embed, MultiTapeTM.embed] <;>
    cases MultiTapeTM.partialInv e i <;> rfl

/-- Reserving blank scratch tapes preserves the clocked output program. -/
theorem run_extendTapes (fuel : ℕ) (input : List Symbol) :
    (machine.extendTapes e).run choose query fuel input = machine.run choose query fuel input := by
  rw [run, initialConfig_extendTapes, runFrom_embed machine e choose hchoose query]
  rfl

/-- Tape extension preserves a halting bound against every stateful interpreter. -/
theorem HaltsWithin.extendTapes {fuel : ℕ} {input : List Symbol}
    (h : machine.HaltsWithin choose query fuel input) :
    (machine.extendTapes e).HaltsWithin choose query fuel input := by
  intro OracleState oracle s final s' hfinal
  rw [initialConfig_extendTapes, runConfigFrom_embed machine e choose hchoose query,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hfinal
  obtain ⟨⟨cfg, state⟩, hcfg, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  exact (congrArg (fun result => result.1.tapes.state) heq).symm.trans
    (h OracleState oracle s cfg state hcfg)

omit hchoose in
/-- In the effect-free deterministic case, tape extension is exactly upstream's compiler. -/
theorem toTM_extendTapes (machine : MultiTapeMachine k Symbol State Empty Id) :
    (machine.extendTapes e).toTM = machine.toTM.extendTapes e := by
  simp only [toTM, MultiTapeTM.extendTapes, MultiTapeTM.adapt, extendTapes]
  congr 1
  funext state symbol work
  simp only [MultiTapeTM.adaptedTr, MultiTapeTM.tr_ofTr, Function.comp_def]
  cases machine.tr state symbol (fun i => work (e i)) Empty.elim with
  | step action symbol move => rfl
  | query oracle next => exact oracle.elim

end Turing.MultiTapeMachine
