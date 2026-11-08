/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Equivalence
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.OutputPrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

/-! Nonvacuous machine specializations, shared-state oracle runs, and fair-coin semantics. -/

namespace CslibFrontierTests.MachinePrograms

open Cslib Turing
open Turing.MultiTapeMachine

private def emit (bit : Bool) (next : Option (Fin 3)) : Turing.Action 0 Bool (Fin 3) where
  inputTape := 0
  workTapes := Fin.elim0
  output := some bit
  state := next

-- Two distinct successors survive the nondeterministic conversion.
private def branches : MultiTapeMachine 0 Bool (Fin 3) Empty Set where
  initial := 0
  tr _ _ _ _ := {Action.step (emit false none) Empty.elim Empty.elim,
    Action.step (emit true none) Empty.elim Empty.elim}

example (bit : Bool) : branches.toNTM.Step (branches.initialConfig []).tapes
    ((emit bit none).apply (branches.initialConfig []).tapes) := by
  cases bit <;> simp [MultiTapeNTM.Step, MultiTapeMachine.toNTM, branches,
    MultiTapeMachine.initialConfig, Cfg.init, Action.emptyOracleEquiv]

private def stuck : MultiTapeMachine 0 Bool Unit Empty Set where
  initial := ()
  tr _ _ _ _ := ∅

-- Empty choices remain stuck, whereas halted configurations still have their self-loop.
example (next : Cfg 0 Bool Unit []) : ¬stuck.toNTM.Step (stuck.initialConfig []).tapes next := by
  simp [MultiTapeNTM.Step, MultiTapeMachine.toNTM, stuck,
    MultiTapeMachine.initialConfig, Cfg.init]

example (cfg : Config 0 Bool Unit Empty []) (h : cfg.tapes.state = none) :
    stuck.Step cfg cfg ∧ stuck.toNTM.Step cfg.tapes cfg.tapes := by
  simp [MultiTapeMachine.Step, MultiTapeNTM.Step, h]

-- Write one bit to each channel, submit only the true channel, then emit its first reply bit.
private def queryMachine : MultiTapeMachine 0 Bool (Fin 3) Bool Id where
  initial := 0
  tr state _ _ answer :=
    if state = 0 then
      .step { emit false (some 1) with output := none } (fun op => some op) (fun _ => 0)
    else if state = 1 then .query true 2
    else .step { emit false none with output := answer true } (fun _ => none) (fun _ => 0)

private abbrev Requests := List (Bool × List Bool)

private def query (op : Bool) (word : List Bool) :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool) :=
  OracleComp.query (op, word)

private def record (request : Bool × List Bool) : StateT Requests Id (List Bool) :=
  modifyGet fun requests => ([false, true], requests ++ [request])

-- The pending buffers survive clock exhaustion; submitting one clears only that channel.
example :
    (OracleComp.interpret record
      ((fun cfg => ((cfg.channels false).queryBuffer, (cfg.channels true).queryBuffer,
        (cfg.channels true).answer, (cfg.channels true).answerPos)) <$>
          queryMachine.runConfigFrom pure query 2 (queryMachine.initialConfig []))).run [] =
      (([false], [], [false, true], 0), [(true, [true])]) := by rfl

-- The machine reads the installed reply and writes its first bit. Later fuel makes no calls.
example : (OracleComp.interpret record (queryMachine.run pure query 7 [])).run [] =
    ([false], [(true, [true])]) := by rfl

-- An existing prefix does not affect the submitted query, its reply, or the private request log.
example : (OracleComp.interpret record ((fun cfg => cfg.tapes.output) <$>
    queryMachine.runConfigFrom pure query 7
      ((queryMachine.initialConfig []).prependOutput [true, false]))).run [(false, [])] =
    ([true, false, false], [(false, []), (true, [true])]) := by
  rw [MultiTapeMachine.runConfigFrom_prependOutput]
  rfl

-- Pause before the query and resume in the same hidden state, retaining the pending payload.
example :
    (OracleComp.interpret record (do
      let cfg ← queryMachine.runConfigFrom pure query 1 (queryMachine.initialConfig [])
      queryMachine.runFrom pure query 6 cfg)).run [] = ([false], [(true, [true])]) := by
  rw [← MultiTapeMachine.runFrom_add]
  rfl

-- Pausing after a query retains both its changed private state and an earlier request history.
example :
    (OracleComp.interpret record (do
      let cfg ← queryMachine.runConfigFrom pure query 2 (queryMachine.initialConfig [])
      queryMachine.runFrom pure query 5 cfg)).run [(false, [])] =
      ([false], [(false, []), (true, [true])]) := by rfl

private def randomBit : MultiTapePTM 0 Bool (Fin 3) where
  initial := 0
  tr _ _ _ _ bit := .step (emit bit none) Empty.elim Empty.elim

example : ProbComp.eval (randomBit.runClosed 1 []) =
    (Probability.PMF.uniformOfFintype Bool).map (fun bit => [bit]) := by
  simp [MultiTapePTM.runClosed, MultiTapePTM.run, MultiTapePTM.runFrom,
    MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, randomBit,
    MultiTapeMachine.initialConfig, Cfg.init, Config.step, Turing.Action.apply, emit]

-- Equal branches still consume one coin, and halt prevents a second coin from being consumed.
private def ignoreCoin : MultiTapePTM 0 Bool (Fin 3) where
  initial := 0
  tr _ _ _ _ _ := .step (emit true none) Empty.elim Empty.elim

private def countCoin (_ : Unit) : StateT ℕ Id Bool :=
  modifyGet fun count => (false, count + 1)

example :
    (OracleComp.interpret countCoin
      (ignoreCoin.run (OracleComp.query ()) (fun oracle => oracle.elim) 5 [])).run 0 =
      ([true], 1) := by rfl

-- The general conversion theorem applies to every deterministic machine and every clock.
example (machine : MultiTapeTM 2 Bool Unit) (fuel : ℕ) (input : List Bool) :
    Config.tapes <$>
        machine.toMachine.runConfigFrom (spec := unifSpec) pure (fun oracle => oracle.elim)
          fuel (machine.toMachine.initialConfig input) =
      pure (machine.runFrom (machine.initCfg input) fuel) := by
  have h := machine.toMachine.runConfigFrom_toTM (spec := unifSpec) fuel
    (machine.toMachine.initialConfig input)
  rw [MultiTapeTM.toMachine_toTM] at h
  exact h

end CslibFrontierTests.MachinePrograms
