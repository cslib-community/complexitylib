/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape

/-!
# Reading an effectful machine's input from work tapes

Two fresh work tapes hold the virtual input and its left-boundary marker. The compiler reuses
upstream's clamped-input simulation, retaining all typed choices and oracle interactions. The
real input head stays at its original position, and the real input is never inspected.

The simulation starts from a prepared virtual input. Preparing these tapes is a separate
computation whose cost must be included when composing machines.

## Main definitions

* `Turing.MultiTapeMachine.inputFromTape`: read a virtual input without adding instructions.
* `Turing.MultiTapeMachine.InputFromTape.config`: embed the input and retain all oracle channels.

## Main results

* `Turing.MultiTapeMachine.runConfigFrom_inputFromTape`: preserve the complete clocked program.
* `Turing.MultiTapeMachine.toTM_inputFromTape`: agree with upstream's deterministic compiler.

## References

Adapted from MultiTape/Oracle/InputFromTape.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine and upstream input redirection
by Christian Reitwiessner and Samuel Schlesinger.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} {input : List Symbol}

namespace InputFromTape

/-- Move the virtual input and boundary heads together, clamping at either end. -/
def action (a : Turing.Action k Symbol State) (symbol flag : Option Symbol) :
    Turing.Action (k + 2) Symbol State :=
  { a with
    inputTape := 0
    workTapes := Fin.append a.workTapes
      (fun _ => (none, MultiTapeTM.clampMove symbol flag a.inputTape)) }

/-- Redirect input movement while retaining communication instructions. -/
def instruction (symbol flag : Option Symbol) :
    Action k Symbol State Oracle → Action (k + 2) Symbol State Oracle
  | .step a querySymbol answerMove => .step (action a symbol flag) querySymbol answerMove
  | .query oracle next => .query oracle next

/-- Embed the source input on work tapes while retaining every communication channel. -/
def config (mark : Symbol) (cfg : Config k Symbol State Oracle input) (outerInput : List Symbol)
    (outerPosition : Fin (outerInput.length + 2)) : Config (k + 2) Symbol State Oracle outerInput :=
  { cfg with
    tapes := { MultiTapeTM.inCfg mark cfg.tapes outerInput with inputPos := outerPosition } }

variable (mark : Symbol) (cfg : Config k Symbol State Oracle input) (outerInput : List Symbol)
  (outerPosition : Fin (outerInput.length + 2))

@[simp] theorem config_state :
    (config mark cfg outerInput outerPosition).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_workTapeSymbols (i : Fin k) :
    (config mark cfg outerInput outerPosition).tapes.workTapeSymbols (i.castAdd 2) =
      cfg.tapes.workTapeSymbols i :=
  MultiTapeTM.inCfg_workTapeSymbols_castAdd (outerInput := outerInput) cfg.tapes i

@[simp] theorem config_inputSymbol :
    (config mark cfg outerInput outerPosition).tapes.workTapeSymbols (Fin.natAdd k 0) =
      cfg.tapes.inputSymbol :=
  MultiTapeTM.inCfg_workTapeSymbols_vip (outerInput := outerInput) cfg.tapes

@[simp] theorem config_flagSymbol :
    (config mark cfg outerInput outerPosition).tapes.workTapeSymbols (Fin.natAdd k 1) =
      if cfg.tapes.inputPos.val = 0 then some mark else none :=
  MultiTapeTM.inCfg_workTapeSymbols_flag (outerInput := outerInput) cfg.tapes

@[simp] theorem config_channels :
    (config mark cfg outerInput outerPosition).channels = cfg.channels := rfl

@[simp] theorem config_answerSymbols :
    (config mark cfg outerInput outerPosition).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem config_output :
    (config mark cfg outerInput outerPosition).tapes.output = cfg.tapes.output := rfl

/-- Upstream's clamped move preserves the virtual input geometry after every instruction. -/
theorem step_config (a : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    (config mark cfg outerInput outerPosition).step
        (action a cfg.tapes.inputSymbol (if cfg.tapes.inputPos.val = 0 then some mark else none))
        symbol move = config mark (cfg.step a symbol move) outerInput outerPosition := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl (by simp [config, Config.step, action, Turing.Action.apply])
    ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases <;>
    simp [config, Config.step, action, Turing.Action.apply, MultiTapeTM.inCfg,
      MultiTapeTM.val_moveInputPos_sub_one_eq_clampMove mark]

theorem receive_config [DecidableEq Oracle] (oracle : Oracle) (next : State)
    (answer : List Symbol) :
    (config mark cfg outerInput outerPosition).receive oracle next answer =
      config mark (cfg.receive oracle next answer) outerInput outerPosition := rfl

end InputFromTape

/-- Read the input from two fresh work tapes: a word and its boundary marker. -/
@[simps! initial] def inputFromTape [Functor Choose]
    (machine : MultiTapeMachine k Symbol State Oracle Choose) :
    MultiTapeMachine (k + 2) Symbol State Oracle Choose where
  initial := machine.initial
  tr state _ work answer :=
    InputFromTape.instruction (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1)) <$>
      machine.tr state (work (Fin.natAdd k 0)) (fun i => work (i.castAdd 2)) answer

/-- Unfold a single virtual-input transition without unfolding its machine in continuations. -/
theorem inputFromTape_tr [Functor Choose] (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (state : State) (symbol : Option Symbol) (work : Fin (k + 2) → Option Symbol)
    (answer : Oracle → Option Symbol) :
    machine.inputFromTape.tr state symbol work answer =
      InputFromTape.instruction (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1)) <$>
        machine.tr state (work (Fin.natAdd k 0)) (fun i => work (i.castAdd 2)) answer := rfl

variable [Functor Choose] [DecidableEq Oracle]
  (machine : MultiTapeMachine k Symbol State Oracle Choose)
  (choose : {α : Type} → Choose α → OracleComp spec α)
  (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
    choose (f <$> choices) = f <$> choose choices)
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

include hchoose

/-- Virtual input preserves the complete program, including communication and private state. -/
theorem runConfigFrom_inputFromTape (mark : Symbol) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) (outerInput : List Symbol)
    (outerPosition : Fin (outerInput.length + 2)) :
    machine.inputFromTape.runConfigFrom choose query fuel
        (InputFromTape.config mark cfg outerInput outerPosition) =
      (fun final => InputFromTape.config mark final outerInput outerPosition) <$>
        machine.runConfigFrom choose query fuel cfg := by
  apply runConfigFrom_map machine machine.inputFromTape choose choose query query
    (fun cfg => InputFromTape.config mark cfg outerInput outerPosition)
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [runConfigFrom, hs]
  | some state =>
    simp only [runConfigFrom, InputFromTape.config_state, hs,
      InputFromTape.config_workTapeSymbols, InputFromTape.config_inputSymbol,
      InputFromTape.config_flagSymbol, InputFromTape.config_answerSymbols, inputFromTape_tr,
      hchoose, bind_map_left, map_bind]
    congr 1
    funext a
    cases a <;> simp only [InputFromTape.instruction, InputFromTape.step_config,
      InputFromTape.receive_config, InputFromTape.config_channels, map_pure, map_bind]

/-- The virtual-input compiler emits exactly the source output program. -/
theorem runFrom_inputFromTape (mark : Symbol) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) (outerInput : List Symbol)
    (outerPosition : Fin (outerInput.length + 2)) :
    machine.inputFromTape.runFrom choose query fuel
        (InputFromTape.config mark cfg outerInput outerPosition) =
      machine.runFrom choose query fuel cfg := by
  simp [runFrom, runConfigFrom_inputFromTape machine choose hchoose query]

omit hchoose in
/-- Effect-free deterministic input redirection is exactly upstream's compiler. -/
theorem toTM_inputFromTape (machine : MultiTapeMachine k Symbol State Empty Id) :
    machine.inputFromTape.toTM = machine.toTM.inputFromTape := by
  simp only [toTM, MultiTapeTM.inputFromTape, MultiTapeTM.adapt, inputFromTape]
  congr 1
  funext state symbol work
  simp only [MultiTapeTM.adaptedTr, MultiTapeTM.tr_ofTr, Function.comp_def]
  cases machine.tr state (work (Fin.natAdd k 0)) (fun i => work (i.castAdd 2)) Empty.elim with
  | step a symbol move => rfl
  | query oracle next => exact oracle.elim

end Turing.MultiTapeMachine
