/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Retaining an existing output prefix

A machine cannot read its output. Prepending a word to that output therefore preserves its
entire execution program, including stateful choices and oracle interactions. This is a
configuration invariance law; writing the prefix remains separate, charged machine work.

## Main definitions

* `Turing.MultiTapeMachine.Config.prependOutput`: prepend a word to the ordinary output.

## Main results

* `Turing.MultiTapeMachine.runConfigFrom_prependOutput`: retain the prefix throughout execution.

## References

Adapted from Computability/Machines/Turing/MultiTape/Oracle/OutputPrefix.lean on the cslib
`crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using upstream's configuration operation and the
common one-step program simulation rule.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} {input : List Symbol}

/-- Change only the unreadable output, retaining all communication channels. -/
def Config.prependOutput (cfg : Config k Symbol State Oracle input) (pre : List Symbol) :
    Config k Symbol State Oracle input :=
  { cfg with tapes := cfg.tapes.prependOutput pre }

@[simp] theorem Config.prependOutput_state (cfg : Config k Symbol State Oracle input)
    (pre : List Symbol) : (cfg.prependOutput pre).tapes.state = cfg.tapes.state := rfl

@[simp] theorem Config.prependOutput_inputSymbol (cfg : Config k Symbol State Oracle input)
    (pre : List Symbol) : (cfg.prependOutput pre).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem Config.prependOutput_workTapeSymbols (cfg : Config k Symbol State Oracle input)
    (pre : List Symbol) :
    (cfg.prependOutput pre).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem Config.prependOutput_channels (cfg : Config k Symbol State Oracle input)
    (pre : List Symbol) : (cfg.prependOutput pre).channels = cfg.channels := rfl

@[simp] theorem Config.prependOutput_answerSymbols (cfg : Config k Symbol State Oracle input)
    (pre : List Symbol) : (cfg.prependOutput pre).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem Config.prependOutput_output (cfg : Config k Symbol State Oracle input)
    (pre : List Symbol) : (cfg.prependOutput pre).tapes.output = pre ++ cfg.tapes.output := rfl

theorem Config.step_prependOutput (cfg : Config k Symbol State Oracle input) (pre : List Symbol)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    (cfg.prependOutput pre).step action symbol move =
      (cfg.step action symbol move).prependOutput pre := by
  simp [Config.prependOutput, Config.step, Turing.Action.apply, Cfg.prependOutput,
    List.append_assoc]

theorem Config.receive_prependOutput [DecidableEq Oracle]
    (cfg : Config k Symbol State Oracle input) (pre : List Symbol)
    (oracle : Oracle) (next : State) (answer : List Symbol) :
    (cfg.prependOutput pre).receive oracle next answer =
      (cfg.receive oracle next answer).prependOutput pre := rfl

/-- An existing output prefix is retained without affecting any instructions or interactions. -/
theorem runConfigFrom_prependOutput [DecidableEq Oracle]
    (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) (pre : List Symbol) :
    machine.runConfigFrom choose query fuel (cfg.prependOutput pre) =
      (fun final => final.prependOutput pre) <$> machine.runConfigFrom choose query fuel cfg := by
  apply runConfigFrom_map machine machine choose choose query query (·.prependOutput pre)
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [hs]
  | some state =>
    simp only [runConfigFrom, Config.prependOutput_state, hs,
      Config.prependOutput_inputSymbol, Config.prependOutput_workTapeSymbols,
      Config.prependOutput_answerSymbols, map_bind]
    congr 1
    funext action
    cases action <;> simp [Config.step_prependOutput, Config.receive_prependOutput]

end Turing.MultiTapeMachine
