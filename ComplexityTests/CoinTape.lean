/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sampling
import Complexity.Tactic.PolyTime

/-! Saved-coin replay with shared state, early halting, cutoff and nontrivial work tapes. -/

namespace ComplexityTests.CoinTape

open Cslib Cslib.Probability Turing MultiTapeMachine

private def queryMachine : MultiTapePTM 0 Bool (Fin 4) Bool where
  initial := 0
  tr state _ _ answer bit :=
    if state = 0 then
      .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some 1 }
        (fun op => some (if op then bit else !bit)) (fun _ => 0)
    else if state = 1 then .query bit (if bit then 3 else 2)
    else .step
      { inputTape := 0, workTapes := Fin.elim0, output := answer (state == 3), state := none }
      (fun _ => none) (fun _ => 0)

private abbrev Request := Bool × List Bool
private abbrev Query := Unit ⊕ Request

private def spec : OracleSpec Query
  | .inl _ => Bool
  | .inr _ => List Bool

private def coin : OracleComp spec Bool := OracleComp.query (spec := spec) (.inl ())

private def query (op : Bool) (word : List Bool) : OracleComp spec (List Bool) :=
  OracleComp.query (spec := spec) (.inr (op, word))

private def record : (q : Query) → StateT (List Request) Id (spec q)
  | .inl _ => pure false
  | .inr request => modifyGet fun history => (request.1 :: request.2, history ++ [request])

private def observe (cfg : Config 0 Bool (Fin 4) Bool []) :=
  (cfg.tapes.output, (cfg.channels false).queryBuffer, (cfg.channels true).queryBuffer,
    (cfg.channels false).answer, cfg.tapes.state)

-- The first bit is written, the next bit selects the queried channel, and surplus coins are inert.
example : (OracleComp.interpret record (observe <$>
    queryMachine.runConfigFromCoins query [true, false, true, false]
      (queryMachine.initialConfig []))).run [(true, [])] =
    (([false], [], [true], [false, false], none), [(true, []), (false, [false])]) := by rfl

-- Pausing before the query retains the pending buffers and the earlier private history.
example : (OracleComp.interpret record (do
    let cfg ← queryMachine.runConfigFromCoins query [true] (queryMachine.initialConfig [])
    observe <$> queryMachine.runConfigFromCoins query [false, true, false] cfg)).run [(true, [])] =
    (([false], [], [true], [false, false], none), [(true, []), (false, [false])]) := by
  rfl

private noncomputable def randomOracle : (q : Query) → StateT ℕ PMF (spec q)
  | .inl _ => fun s => (PMF.uniformOfFintype Bool).map (fun bit => (bit, s))
  | .inr (op, _) => fun s => (PMF.uniformOfFintype Bool).map
      (fun bit => ([bit ^^ op ^^ (s % 2 == 0)], s + 1))

-- The averaging law applies to randomized replies, coin-dependent queries, and shared state.
example (fuel s : ℕ) :
    (OracleComp.interpret randomOracle
      (queryMachine.runConfigFrom coin query fuel (queryMachine.initialConfig []))).run s =
      (BitString.uniformList fuel).bind (fun coins =>
        (OracleComp.interpret randomOracle
          (queryMachine.runConfigFromCoins query coins
            (queryMachine.initialConfig []))).run s) := by
  exact MultiTapePTM.run_interpret_runConfigFrom_eq_coins queryMachine coin query randomOracle
    (fun s => congrArg (fun p => p.run s) (OracleComp.interpret_query randomOracle (.inl ()))) _ _ _

-- Fixed-coin replay draws no coins, even if the installed coin handler would mutate state.
private def countCoins : (q : Query) → StateT ℕ Id (spec q)
  | .inl _ => modifyGet fun s => (false, s + 1)
  | .inr _ => pure []

example : ((OracleComp.interpret countCoins (queryMachine.runConfigFromCoins query
    [false, false, false] (queryMachine.initialConfig []))).run 0).2 = 0 := by rfl

-- A state-changing coin handler does not satisfy the open averaging claim without its hypothesis.
example : (OracleComp.interpret countCoins (queryMachine.runConfigFrom coin query 1
      (queryMachine.initialConfig []))).run 0 ≠
    (OracleComp.interpret countCoins (queryMachine.runConfigFromCoins query [false]
      (queryMachine.initialConfig []))).run 0 := by
  intro h
  have : (1 : ℕ) = 0 := congrArg Prod.snd h
  contradiction

private def writeForever : MultiTapePTM 1 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := fun _ => (some bit, -1), output := some bit, state := some () }
    Empty.elim Empty.elim

-- The supplied tape bounds a source that never halts, including its negative work-head movement.
example :
    let final := writeForever.replay.runFrom
      (MultiTapePTM.Replay.config (writeForever.initialConfig [])
        (tapeOfList [true, false]) 0) 3
    (final.output, final.state, final.workTapePos 0, final.workTapePos 1,
      final.workTapes 0 0, final.workTapes 0 (-1)) =
      ([true, false], none, -2, 2, some true, some false) := by
  dsimp only
  have h := MultiTapePTM.runFrom_replay writeForever [true, false] []
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at h
  rw [h]
  rfl

-- An empty tape halts the controller before executing any instruction of a live source.
example :
    let final := writeForever.replay.runFrom
      (MultiTapePTM.Replay.config (writeForever.initialConfig []) (tapeOfList []) 0) 1
    (final.output, final.state, final.workTapePos 0, final.workTapePos 1) = ([], none, 0, 0) := by
  dsimp only
  have h := MultiTapePTM.runFrom_replay writeForever [] []
  simp only [List.length_nil, Nat.reduceAdd] at h
  rw [h]
  rfl

-- A source that halts early ignores the unused bits while the controller finishes its scan.
example :
    let final := MultiTapePTM.uniformListMachine.replay.runFrom
      (MultiTapePTM.Replay.config (MultiTapePTM.uniformListMachine.initialConfig [false])
        (tapeOfList [true, false, false, true]) 0) 5
    (final.output, final.state, final.workTapePos 0) = ([true], none, 4) := by
  dsimp only
  have h := MultiTapePTM.runFrom_replay MultiTapePTM.uniformListMachine
    [true, false, false, true] [false]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at h
  rw [h]
  rfl

private def halted : Config 1 Bool Unit Empty [] :=
  { writeForever.initialConfig [] with
    tapes := { (writeForever.initialConfig []).tapes with state := none, output := [true] } }

-- An already-halted source retains its output; stored false bits are not tape boundaries.
example :
    let final := writeForever.replay.runFrom
      (MultiTapePTM.Replay.config halted (tapeOfList [false, true]) 0) 3
    (final.output, final.state, final.workTapePos 0, final.workTapePos 1) =
      ([true], none, 0, 2) := by
  have h := MultiTapePTM.Replay.runFrom_coins writeForever halted [false, true]
    (tapeOfList [false, true]) 0 (by intros; simp) (by rfl)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, zero_add] at h
  dsimp only
  rw [h]
  rfl

-- A concrete 3-coin tape produces `[false]` in the support of
-- `uniformListMachine.runClosed 3 [true]`.
example :
    [false] ∈ (ProbComp.eval (MultiTapePTM.uniformListMachine.runClosed 3 [true])).support := by
  have h : MultiTapePTM.uniformListMachine.runClosedCoins [false, true, false] [true] = [false] :=
    rfl
  exact h ▸ MultiTapePTM.runClosedCoins_mem_support
    MultiTapePTM.uniformListMachine [false, true, false] [true]

-- A functional client can rearrange arguments and preprocess the supplied tape by automation, and
-- both runtime inputs matter because the scanner stops at the end of its virtual input.
example :
    MultiTapeTM.ComputableInPolyTime
      (fun p : List Bool × List Bool => writeForever.runClosedCoins (false :: p.2) p.1)
      (MultiTapeTM.encPair MultiTapeTM.encBits MultiTapeTM.encBits) MultiTapeTM.encBits ∧
    MultiTapeTM.ComputableInPolyTime
      (fun p : List Bool × List Bool => MultiTapePTM.uniformListMachine.runClosedCoins p.1 p.2)
      (MultiTapeTM.encPair MultiTapeTM.encBits MultiTapeTM.encBits) MultiTapeTM.encBits :=
  ⟨by fun_prop, by fun_prop⟩

example :
    MultiTapePTM.uniformListMachine.runClosedCoins [false, true, false] [true] = [false] ∧
    MultiTapePTM.uniformListMachine.runClosedCoins [false, true, false] [] = [] ∧
    MultiTapePTM.uniformListMachine.runClosedCoins [] [true, false] = [] :=
  ⟨rfl, rfl, rfl⟩

end ComplexityTests.CoinTape
