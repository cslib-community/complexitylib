/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.WithOracle

/-! Native replay retains saved random branches, query channels, replies, and handler state. -/

namespace ComplexityTests.OracleSavedCoins

open Cslib Turing MultiTapeMachine MultiTapePTM

private inductive Control
  | branch
  | ask (op : Bool)
  | emit (op : Bool)
  deriving DecidableEq, Fintype

private def machine : MultiTapePTM 0 Bool Control Bool where
  initial := .branch
  tr state _ _ answer bit := match state with
    | .branch => .step
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := some (.ask bit) }
        (fun _ => none) (fun _ => 0)
    | .ask op => .query op (.emit op)
    | .emit op => .step
        { inputTape := 0, workTapes := Fin.elim0, output := answer op, state := none }
        (fun _ => none) (fun _ => 0)

private def query (op : Bool) (word : List Bool) :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool) :=
  OracleComp.query (op, word)

private def record : (q : Bool × List Bool) → StateT ℕ Id (List Bool) :=
  fun _ => modifyGet fun count => ([count % 2 == 0], count + 1)

private def initial : Config 0 Bool Control Bool [] :=
  { machine.initialConfig [] with
    channels := fun op => { queryBuffer := if op then [true, false] else [false] } }

private def observe (cfg : Config 1 Bool (ReplayWithOracle.Control Control) Bool []) :=
  (cfg.tapes.output, (cfg.channels true).queryBuffer, (cfg.channels false).queryBuffer,
    (cfg.channels true).answer, cfg.tapes.state, cfg.tapes.workTapePos 0)

-- The saved true branch selects the true query although all fresh controller coins are false.
-- The query's saved false coin is consumed once; the reply, other buffer, and state survive.
example : (OracleComp.interpret record (observe <$> machine.replayWithOracle.runConfigFrom
    (pure false) query 7
      (AuxiliaryTape.config initial (tapeOfList [true, false, true]) 0 none))).run 4 =
    (([true], [], [false], [true], none, 3), 5) := by rfl

-- The first blank cell stops before any query, even when extra fuel remains.
example : (OracleComp.interpret record (observe <$> machine.replayWithOracle.runConfigFrom
    (pure true) query 9 (AuxiliaryTape.config initial (tapeOfList []) 0 none))).run 4 =
    (([], [true, false], [false], [], none, 0), 4) := by rfl

-- A halted source consumes padding coins without modifying its data or making another call.
example : (OracleComp.interpret record (observe <$> machine.replayWithOracle.runConfigFrom
    (pure true) query 5 (AuxiliaryTape.config
      { initial with tapes := { initial.tapes with state := none, output := [false] } }
      (tapeOfList [true, false]) 0 none))).run 4 =
    (([false], [true, false], [false], [], none, 2), 4) := by rfl

-- The program law applies to an arbitrary supplied tape, with every request still present.
example (coins : List Bool) :
    machine.replayWithOracle.runConfigFrom (pure false) query (2 * coins.length + 1)
        (AuxiliaryTape.config initial (tapeOfList coins) 0 none) =
      (fun final => AuxiliaryTape.stopped final (tapeOfList coins) coins.length) <$>
        machine.runConfigFromCoins query coins initial := by
  simpa only [zero_add] using ReplayWithOracle.run_coins machine query initial
    coins (tapeOfList coins) 0 (fun i _ => by simp [tapeOfList_ofNat])
    (by simp [tapeOfList_ofNat])

private noncomputable def stateful : (q : Bool × List Bool) → StateT ℕ PMF (List Bool) :=
  fun _ s => PMF.pure ([s % 2 == 0], s + 1)

-- The independence hypothesis holds with a concrete, nontrivial stateful external handler.
example (fuel s : ℕ) :
    (OracleComp.interpret stateful (machine.replayWithOracle.runConfigFrom
      (pure true) query fuel (AuxiliaryTape.config initial (tapeOfList [true]) 0 none))).run s =
    (OracleComp.interpret stateful (machine.replayWithOracle.runConfigFrom
      (pure false) query fuel (AuxiliaryTape.config initial (tapeOfList [true]) 0 none))).run s :=
  ReplayWithOracle.run_interpret_coin_independent machine (pure true) query stateful (PMF.pure true)
    (fun _ => by simp) fuel _ s

end ComplexityTests.OracleSavedCoins
