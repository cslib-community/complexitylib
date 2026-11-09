/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine
import Mathlib.Data.Fin.Tuple.Basic

/-!
# An auxiliary tape for machine controllers

A controller can retain a source configuration, including its oracle channels, alongside a phase
in finite control and an additional work tape. Clocks use a Boolean phase; saved-coin replay uses
an optional bit. The source's tape actions and oracle replies keep their original effects.

## Main definitions

* `Turing.MultiTapeMachine.AuxiliaryTape.config`: retain source data with a controller phase.
* `Turing.MultiTapeMachine.AuxiliaryTape.move`: change control and move the extra head.
* `Turing.MultiTapeMachine.AuxiliaryTape.liftAction`: retain the extra tape during a source action.
* `Turing.MultiTapeMachine.AuxiliaryTape.stopped`: halt while retaining source data and channels.

## Main results

* `Turing.MultiTapeMachine.AuxiliaryTape.step_liftAction`: retain source tape and channel effects.
* `Turing.MultiTapeMachine.AuxiliaryTape.step_move`: move only the additional head.

## References

Generalizes the shared controller operations from `MultiTape.Machine.Clock`, adapted there from
MultiTape/Oracle/Clock.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapeMachine.AuxiliaryTape

variable {k : ℕ} {State Oracle Phase : Type} {input : List Bool}

/-- Retain source tapes and channels with a phase and one additional work tape. -/
def config (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool) (position : ℤ)
    (phase : Phase) : Config (k + 1) Bool (Phase × Option State) Oracle input where
  tapes := {
    state := some (phase, cfg.tapes.state)
    inputPos := cfg.tapes.inputPos
    workTapes := Fin.lastCases tape cfg.tapes.workTapes
    workTapePos := Fin.lastCases position cfg.tapes.workTapePos
    output := cfg.tapes.output }
  channels := cfg.channels

/-- Change control and move only the auxiliary head. -/
def move (next : Option (Phase × Option State)) (direction : SignType) :
    Turing.Action (k + 1) Bool (Phase × Option State) where
  inputTape := 0
  workTapes := Fin.lastCases (none, direction) (fun _ => (none, 0))
  output := none
  state := next

/-- Perform a source tape action and select the next phase, retaining the auxiliary tape. -/
def liftAction (phase : Phase) (action : Turing.Action k Bool State) :
    Turing.Action (k + 1) Bool (Phase × Option State) where
  inputTape := action.inputTape
  workTapes := Fin.lastCases (none, 0) action.workTapes
  output := action.output
  state := some (phase, action.state)

@[simp] theorem config_state (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (phase : Phase) :
    (config cfg tape position phase).tapes.state = some (phase, cfg.tapes.state) := rfl

@[simp] theorem config_inputSymbol (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (phase : Phase) :
    (config cfg tape position phase).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols_castSucc (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (phase : Phase) (i : Fin k) :
    (config cfg tape position phase).tapes.workTapeSymbols i.castSucc =
      cfg.tapes.workTapeSymbols i := by simp [config, Cfg.workTapeSymbols]

@[simp] theorem config_workTapeSymbols_last (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (phase : Phase) :
    (config cfg tape position phase).tapes.workTapeSymbols (Fin.last k) = tape position := by
  simp [config, Cfg.workTapeSymbols]

@[simp] theorem config_answerSymbols (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (phase : Phase) :
    (config cfg tape position phase).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem config_channels (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (phase : Phase) : (config cfg tape position phase).channels = cfg.channels := rfl

@[simp] theorem config_output (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (phase : Phase) :
    (config cfg tape position phase).tapes.output = cfg.tapes.output :=
  rfl

/-- Lifting a source action preserves its tape and communication effects. -/
theorem step_liftAction (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (before after : Phase) (action : Turing.Action k Bool State)
    (symbol : Oracle → Option Bool) (direction : Oracle → SignType) :
    (config cfg tape position before).step (liftAction after action) symbol direction =
      config (cfg.step action symbol direction) tape position after := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [config, liftAction, Config.step, Turing.Action.apply]

/-- Receiving a reply changes exactly the source channel and control. -/
theorem receive_config [DecidableEq Oracle] (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (before after : Phase)
    (oracle : Oracle) (next : State) (answer : List Bool) :
    (config cfg tape position before).receive oracle (after, some next) answer =
      config (cfg.receive oracle next answer) tape position after := rfl

/-- Moving the auxiliary head leaves source data and communication channels unchanged. -/
theorem step_move (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (before after : Phase) (direction : SignType) :
    (config cfg tape position before).step (move (some (after, cfg.tapes.state)) direction)
        (fun _ => none) (fun _ => 0) =
      config cfg tape (position + direction) after := by
  refine Config.ext ?_ (by simp [Config.step, config])
  refine Cfg.ext rfl (by simp [config, move, Config.step, Turing.Action.apply]) ?_ ?_
    (by simp [config, move, Config.step, Turing.Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [config, move, Config.step, Turing.Action.apply]

/-- Halt the controller without changing its data or channels. -/
def stopped (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool) (position : ℤ) :
    Config (k + 1) Bool (Phase × Option State) Oracle input where
  tapes := {
    state := none
    inputPos := cfg.tapes.inputPos
    workTapes := Fin.lastCases tape cfg.tapes.workTapes
    workTapePos := Fin.lastCases position cfg.tapes.workTapePos
    output := cfg.tapes.output }
  channels := cfg.channels

@[simp] theorem stopped_state (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) : (stopped (Phase := Phase) cfg tape position).tapes.state = none := rfl

@[simp] theorem stopped_output (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) :
    (stopped (Phase := Phase) cfg tape position).tapes.output = cfg.tapes.output := rfl

/-- A stationary head update can stop the controller, preserving all data. -/
theorem step_stop (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (phase : Phase) :
    (config cfg tape position phase).step (move none 0) (fun _ => none) (fun _ => 0) =
      stopped cfg tape position := by
  refine Config.ext ?_ (by simp [Config.step, config, stopped])
  refine Cfg.ext rfl (by simp [config, stopped, move, Config.step, Turing.Action.apply]) ?_ ?_
    (by simp [config, stopped, move, Config.step, Turing.Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [config, stopped, move, Config.step, Turing.Action.apply]

end Turing.MultiTapeMachine.AuxiliaryTape
