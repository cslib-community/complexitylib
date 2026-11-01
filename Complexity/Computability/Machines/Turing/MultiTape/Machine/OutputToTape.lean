/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape

/-!
# Buffering an effectful machine's output

The output is redirected to a fresh last work tape, whose head remains at the write frontier.
The real output stays empty. All choices and oracle interactions are preserved as a typed
program, so this construction also retains state shared by coin and query interpreters.

The configuration map reuses upstream's `outCfg`. No budget or already computed output is
supplied to the machine: an initially blank buffer is filled one source instruction at a time.

## Main definitions

* `Turing.MultiTapeMachine.outputToTape`: buffer the source output without adding instructions.
* `Turing.MultiTapeMachine.OutputToTape.config`: retain source data and communication channels.

## Main results

* `Turing.MultiTapeMachine.runConfigFrom_outputToTape`: preserve the whole clocked program.
* `Turing.MultiTapeMachine.toTM_outputToTape`: agree exactly with upstream's deterministic compiler.

## References

Adapted from MultiTape/Oracle/OutputToTape.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine and upstream output redirection
by Christian Reitwiessner and Samuel Schlesinger.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} {input : List Symbol}

namespace OutputToTape

/-- Redirect an emitted symbol to the fresh work tape and advance its write frontier. -/
def action (a : Turing.Action k Symbol State) : Turing.Action (k + 1) Symbol State where
  inputTape := a.inputTape
  workTapes := Fin.lastCases
    (match a.output with
      | none => (none, 0)
      | some symbol => (some (some symbol), 1)) a.workTapes
  output := none
  state := a.state

/-- Redirect ordinary output writes while retaining communication instructions. -/
def instruction : Action k Symbol State Oracle → Action (k + 1) Symbol State Oracle
  | .step a symbol move => .step (action a) symbol move
  | .query oracle next => .query oracle next

/-- Upstream's output-buffered configuration, with every communication channel retained. -/
def config (cfg : Config k Symbol State Oracle input) : Config (k + 1) Symbol State Oracle input :=
  { cfg with tapes := MultiTapeTM.outCfg cfg.tapes }

@[simp] theorem config_state (cfg : Config k Symbol State Oracle input) :
    (config cfg).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_inputSymbol (cfg : Config k Symbol State Oracle input) :
    (config cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols (cfg : Config k Symbol State Oracle input) (i : Fin k) :
    (config cfg).tapes.workTapeSymbols i.castSucc = cfg.tapes.workTapeSymbols i :=
  MultiTapeTM.outCfg_workTapeSymbols_castSucc cfg.tapes i

@[simp] theorem config_channels (cfg : Config k Symbol State Oracle input) :
    (config cfg).channels = cfg.channels := rfl

@[simp] theorem config_answerSymbols (cfg : Config k Symbol State Oracle input) :
    (config cfg).answerSymbols = cfg.answerSymbols := rfl

/-- A source output write appends exactly one cell at the buffer's write frontier. -/
theorem step_config (cfg : Config k Symbol State Oracle input) (a : Turing.Action k Symbol State)
    (symbol : Oracle → Option Symbol) (move : Oracle → SignType) :
    (config cfg).step (action a) symbol move = config (cfg.step a symbol move) := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | cast i => simp [config, action, Config.step, Turing.Action.apply, MultiTapeTM.outCfg]
  | last =>
    cases h : a.output <;>
      simp [config, action, Config.step, Turing.Action.apply, MultiTapeTM.outCfg, h,
        tapeOfList_append_single, SignType.cast]

theorem receive_config [DecidableEq Oracle] (cfg : Config k Symbol State Oracle input)
    (oracle : Oracle) (next : State) (answer : List Symbol) :
    (config cfg).receive oracle next answer = config (cfg.receive oracle next answer) := rfl

end OutputToTape

/-- Buffer output on a fresh work tape, retaining the source's oracle interactions. -/
@[simps! initial] def outputToTape [Functor Choose]
    (machine : MultiTapeMachine k Symbol State Oracle Choose) :
    MultiTapeMachine (k + 1) Symbol State Oracle Choose where
  initial := machine.initial
  tr state symbol work answer :=
    OutputToTape.instruction <$> machine.tr state symbol (fun i => work i.castSucc) answer

/-- Unfold a single redirected transition without unfolding its machine in continuations. -/
theorem outputToTape_tr [Functor Choose] (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (state : State) (symbol : Option Symbol) (work : Fin (k + 1) → Option Symbol)
    (answer : Oracle → Option Symbol) :
    machine.outputToTape.tr state symbol work answer =
      OutputToTape.instruction <$> machine.tr state symbol (fun i => work i.castSucc) answer := rfl

variable [Functor Choose] [DecidableEq Oracle]
  (machine : MultiTapeMachine k Symbol State Oracle Choose)
  (choose : {α : Type} → Choose α → OracleComp spec α)
  (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
    choose (f <$> choices) = f <$> choose choices)
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

include hchoose

/-- Output buffering preserves the complete program, including the source's communication state. -/
theorem runConfigFrom_outputToTape (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    machine.outputToTape.runConfigFrom choose query fuel (OutputToTape.config cfg) =
      OutputToTape.config <$> machine.runConfigFrom choose query fuel cfg := by
  apply runConfigFrom_map machine machine.outputToTape choose choose query query OutputToTape.config
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [runConfigFrom, hs]
  | some state =>
    simp only [runConfigFrom, OutputToTape.config_state, hs, OutputToTape.config_inputSymbol,
      OutputToTape.config_workTapeSymbols, OutputToTape.config_answerSymbols, outputToTape_tr,
      hchoose, bind_map_left, map_bind]
    congr 1
    funext a
    cases a <;> simp [OutputToTape.instruction, OutputToTape.step_config,
      OutputToTape.receive_config]

omit hchoose [DecidableEq Oracle] in
/-- Output buffering starts with a blank work tape, without a precomputed output word. -/
theorem initialConfig_outputToTape (input : List Symbol) :
    machine.outputToTape.initialConfig input =
      OutputToTape.config (machine.initialConfig input) := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [initialConfig, OutputToTape.config, MultiTapeTM.outCfg, Cfg.init]

omit hchoose in
/-- Effect-free deterministic output redirection is exactly upstream's compiler. -/
theorem toTM_outputToTape (machine : MultiTapeMachine k Symbol State Empty Id) :
    machine.outputToTape.toTM = machine.toTM.outputToTape := by
  simp only [toTM, MultiTapeTM.outputToTape, MultiTapeTM.adapt, outputToTape]
  congr 1
  funext state symbol work
  simp only [MultiTapeTM.adaptedTr, MultiTapeTM.tr_ofTr, Function.comp_def]
  cases machine.tr state symbol (fun i => work i.castSucc) Empty.elim with
  | step a symbol move => rfl
  | query oracle next => exact oracle.elim

end Turing.MultiTapeMachine
