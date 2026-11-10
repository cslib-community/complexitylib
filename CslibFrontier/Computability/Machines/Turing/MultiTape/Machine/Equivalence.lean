/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Effect-free specializations of the common machine

With no oracle channels, an action is exactly an upstream `Turing.Action` and a configuration
is exactly an upstream `Turing.Cfg`. Choosing `Id` or `Set` supplies the deterministic or
nondeterministic transition interface. The conversions preserve each step, including halted
and stuck configurations; there is no clock rescaling or simulation overhead.

## Main definitions

* `Turing.MultiTapeMachine.Action.emptyOracleEquiv`: remove empty communication instructions.
* `Turing.MultiTapeMachine.Config.emptyOracleEquiv`: remove empty communication state.
* `Turing.MultiTapeTM.toMachine`, `Turing.MultiTapeNTM.toMachine`: embed upstream machines.
* `Turing.MultiTapeMachine.toTM`, `Turing.MultiTapeMachine.toNTM`: recover upstream machines.
* `Turing.MultiTapeMachine.tmEquiv`: equivalence with upstream's deterministic machine type.

## Main results

* `Turing.MultiTapeMachine.step_toTM`: deterministic steps commute with conversion.
* `Turing.MultiTapeMachine.step_toNTM_iff`: nondeterministic steps commute with conversion.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace MultiTapeMachine

/-- With no channels there are no queries or communication updates. -/
def Action.emptyOracleEquiv : Action k Symbol State Empty ≃ Turing.Action k Symbol State where
  toFun
    | .step action _ _ => action
    | .query oracle _ => oracle.elim
  invFun action := .step action Empty.elim Empty.elim
  left_inv action := by
    cases action with
    | step action symbol move =>
      change Action.step action Empty.elim Empty.elim = Action.step action symbol move
      congr 1 <;> funext oracle <;> exact oracle.elim
    | query oracle _ => exact oracle.elim
  right_inv _ := rfl

/-- Empty communication state contains no information beyond the upstream configuration. -/
def Config.emptyOracleEquiv : Config k Symbol State Empty input ≃ Cfg k Symbol State input where
  toFun := Config.tapes
  invFun cfg := ⟨cfg, Empty.elim⟩
  left_inv cfg := by
    apply Config.ext
    · rfl
    · funext oracle
      exact oracle.elim
  right_inv _ := rfl

/-- A configuration without communication channels is determined by its tapes. -/
theorem Config.eq_iff_tapes_eq {cfg cfg' : Config k Symbol State Empty input} :
    cfg = cfg' ↔ cfg.tapes = cfg'.tapes :=
  Config.emptyOracleEquiv.injective.eq_iff.symm

/-- Recover the deterministic upstream machine from an effect-free transition table. -/
def toTM (machine : MultiTapeMachine k Symbol State Empty Id) : MultiTapeTM k Symbol State :=
  MultiTapeTM.ofTr machine.initial fun state symbol work =>
    Action.emptyOracleEquiv (machine.tr state symbol work Empty.elim)

/-- Recover the nondeterministic upstream transition relation from the set of permitted actions. -/
def toNTM (machine : MultiTapeMachine k Symbol State Empty Set) : MultiTapeNTM k Symbol State where
  q₀ := machine.initial
  Tr state symbol work action :=
    Action.emptyOracleEquiv.symm action ∈ machine.tr state symbol work Empty.elim

/-- One deterministic step without oracle channels. Halted configurations are fixed points. -/
def step (machine : MultiTapeMachine k Symbol State Empty Id)
    (cfg : Config k Symbol State Empty input) : Config k Symbol State Empty input :=
  match cfg.tapes.state with
  | none => cfg
  | some state =>
    match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
    | .step action symbol move => cfg.step action symbol move
    | .query oracle _ => oracle.elim

/-- One nondeterministic step without channels. Empty transition sets remain stuck, while
halted configurations step only to themselves, as in upstream's relation. -/
def Step (machine : MultiTapeMachine k Symbol State Empty Set)
    (cfg next : Config k Symbol State Empty input) : Prop :=
  match cfg.tapes.state with
  | none => next = cfg
  | some state => ∃ action ∈ machine.tr state cfg.tapes.inputSymbol
      cfg.tapes.workTapeSymbols cfg.answerSymbols,
    match action with
    | .step action symbol move => next = cfg.step action symbol move
    | .query oracle _ => oracle.elim

/-- The initial configurations correspond without modifying any tape. -/
theorem initialConfig_toTM (machine : MultiTapeMachine k Symbol State Empty Id)
    (input : List Symbol) :
    (machine.initialConfig input).tapes = machine.toTM.initCfg input := rfl

/-- The initial configurations correspond for a nondeterministic transition table. -/
theorem initialConfig_toNTM (machine : MultiTapeMachine k Symbol State Empty Set)
    (input : List Symbol) :
    (machine.initialConfig input).tapes = machine.toNTM.initCfg input := rfl

/-- Recovering an upstream machine preserves a deterministic step exactly. -/
theorem step_toTM (machine : MultiTapeMachine k Symbol State Empty Id)
    (cfg : Config k Symbol State Empty input) :
    (machine.step cfg).tapes = machine.toTM.step cfg.tapes := by
  have hread : cfg.answerSymbols = Empty.elim := funext fun oracle => oracle.elim
  cases hs : cfg.tapes.state with
  | none =>
    rw [step, hs]
    exact (MultiTapeTM.step_iff.mp (by simp [MultiTapeNTM.Step, hs])).symm
  | some state =>
    rw [step, hs, hread, MultiTapeTM.step_of_state hs]
    simp only [toTM, MultiTapeTM.tr_ofTr]
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols Empty.elim with
    | step action symbol move => rfl
    | query oracle _ => exact oracle.elim

/-- Recovering an upstream machine preserves all nondeterministic successors, including the
absence of successors at a stuck configuration. -/
theorem step_toNTM_iff (machine : MultiTapeMachine k Symbol State Empty Set)
    (cfg next : Config k Symbol State Empty input) :
    machine.Step cfg next ↔ machine.toNTM.Step cfg.tapes next.tapes := by
  have hread : cfg.answerSymbols = Empty.elim := funext fun oracle => oracle.elim
  cases hs : cfg.tapes.state with
  | none =>
    simp only [Step, MultiTapeNTM.Step, hs]
    exact Config.emptyOracleEquiv.injective.eq_iff.symm
  | some state =>
    simp only [Step, MultiTapeNTM.Step, hs, hread, toNTM]
    constructor
    · rintro ⟨action, ha, hnext⟩
      cases action with
      | step action symbol move =>
        have heq : Action.step action symbol move = Action.emptyOracleEquiv.symm action := by
          congr 1 <;> funext oracle <;> exact oracle.elim
        exact ⟨action, heq ▸ ha, congrArg Config.tapes hnext⟩
      | query oracle _ => exact oracle.elim
    · rintro ⟨action, ha, hnext⟩
      refine ⟨Action.emptyOracleEquiv.symm action, ha, ?_⟩
      apply Config.emptyOracleEquiv.injective
      exact hnext

end MultiTapeMachine

/-- Embed a deterministic upstream machine in the common table using `Id` for its choices. -/
noncomputable def MultiTapeTM.toMachine (machine : MultiTapeTM k Symbol State) :
    MultiTapeMachine k Symbol State Empty Id where
  initial := machine.q₀
  tr state symbol work _ := MultiTapeMachine.Action.emptyOracleEquiv.symm
    (machine.tr state symbol work)

/-- Embed an upstream nondeterministic machine using precisely its permitted actions. -/
def MultiTapeNTM.toMachine (machine : MultiTapeNTM k Symbol State) :
    MultiTapeMachine k Symbol State Empty Set where
  initial := machine.q₀
  tr state symbol work _ := {action | machine.Tr state symbol work
    (MultiTapeMachine.Action.emptyOracleEquiv action)}

/-- A deterministic embedding retains the original transition function. -/
theorem MultiTapeTM.toMachine_toTM_tr (machine : MultiTapeTM k Symbol State)
    (state : State) (symbol : Option Symbol) (work : Fin k → Option Symbol) :
    machine.toMachine.toTM.tr state symbol work = machine.tr state symbol work := by
  simp [MultiTapeMachine.toTM, MultiTapeTM.toMachine, MultiTapeMachine.Action.emptyOracleEquiv]

/-- A deterministic embedding retains the original machine, including its transition relation. -/
theorem MultiTapeTM.toMachine_toTM (machine : MultiTapeTM k Symbol State) :
    machine.toMachine.toTM = machine := by
  have htr : (fun state symbol work action => machine.tr state symbol work = action) =
      machine.Tr := by
    funext state symbol work action
    exact propext MultiTapeTM.tr_iff.symm
  cases machine with
  | mk machine hdet =>
    cases machine
    simp_all [MultiTapeTM.toMachine, MultiTapeMachine.toTM, MultiTapeTM.ofTr,
      MultiTapeMachine.Action.emptyOracleEquiv]

/-- A nondeterministic embedding retains the original relation, including empty choices. -/
theorem MultiTapeNTM.toMachine_toNTM (machine : MultiTapeNTM k Symbol State) :
    machine.toMachine.toNTM = machine := rfl

namespace MultiTapeMachine

/-- Converting a deterministic table to upstream and back retains the complete table. -/
theorem toTM_toMachine (machine : MultiTapeMachine k Symbol State Empty Id) :
    machine.toTM.toMachine = machine := by
  apply MultiTapeMachine.ext
  · rfl
  · funext state symbol work answer
    have hanswer : answer = Empty.elim := funext fun oracle => oracle.elim
    simp [toTM, MultiTapeTM.toMachine, hanswer]

/-- Converting a nondeterministic table to upstream and back retains every permitted action. -/
theorem toNTM_toMachine (machine : MultiTapeMachine k Symbol State Empty Set) :
    machine.toNTM.toMachine = machine := by
  apply MultiTapeMachine.ext
  · rfl
  · funext state symbol work answer
    have hanswer : answer = Empty.elim := funext fun oracle => oracle.elim
    simp [toNTM, MultiTapeNTM.toMachine, hanswer]

/-- The effect-free deterministic machine is precisely upstream's machine type. -/
noncomputable def tmEquiv :
    MultiTapeMachine k Symbol State Empty Id ≃ MultiTapeTM k Symbol State where
  toFun := toTM
  invFun := MultiTapeTM.toMachine
  left_inv := toTM_toMachine
  right_inv := MultiTapeTM.toMachine_toTM

/-- The effect-free nondeterministic machine is precisely upstream's machine type. -/
def ntmEquiv : MultiTapeMachine k Symbol State Empty Set ≃ MultiTapeNTM k Symbol State where
  toFun := toNTM
  invFun := MultiTapeNTM.toMachine
  left_inv := toNTM_toMachine
  right_inv := MultiTapeNTM.toMachine_toNTM

end MultiTapeMachine

end Turing
