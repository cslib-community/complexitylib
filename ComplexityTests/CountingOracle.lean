/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.Oracle.Replay

/-! Actual buffered queries, duplicate occurrences, branch-local state and canonical replay. -/

namespace ComplexityTests.CountingOracle

open Cslib Turing MultiTapeMachine

inductive Phase where
  | start | ask | copy | askAgain | finish
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.start, .ask, .copy, .askAgain, .finish}, by intro phase; cases phase <;> simp⟩

private def action (output : Option Bool) (next : Option Phase) : Turing.Action 0 Bool Phase where
  inputTape := 0
  workTapes := Fin.elim0
  output := output
  state := next

-- One early halt and two equal occurrences; both long paths submit two real buffered queries.
private def machine : MultiTapeMachine 0 Bool Phase Unit List where
  initial := .start
  tr state _ _ answer := match state with
    | .start => [.step (action none none) (fun _ => none) (fun _ => 0),
        .step (action none (some .ask)) (fun _ => some true) (fun _ => 0),
        .step (action none (some .ask)) (fun _ => some true) (fun _ => 0)]
    | .ask => [.query () .copy]
    | .copy => [.step (action (answer ()) (some .askAgain)) (fun _ => answer ()) (fun _ => 0)]
    | .askAgain => [.query () .finish]
    | .finish => [.step (action (answer ()) none) (fun _ => none) (fun _ => 0)]

private theorem bounded (state : Phase) (symbol : Option Bool) (work : Fin 0 → Option Bool)
    (answers : Unit → Option Bool) : (machine.tr state symbol work answers).length ≤ 3 := by
  cases state <;> simp [machine]

private theorem nonblocking (state : Phase) (symbol : Option Bool) (work : Fin 0 → Option Bool)
    (answers : Unit → Option Bool) : machine.tr state symbol work answers ≠ [] := by
  cases state <;> simp [machine]

private abbrev History := ℕ × List (List Bool)

-- The unused suffix can be arbitrarily long; native execution only reads the first reply cell.
private def record (suffix : List Bool) (request : Unit × List Bool) :
    History → List Bool × History := fun (count, history) =>
  ((count % 2 == 1) :: suffix, (count + 1, history ++ [request.2]))

private def early (input : List Bool) : Config 0 Bool Phase Unit input where
  tapes := { Cfg.init Phase.start input with state := none }

private def finished (input suffix : List Bool) : Config 0 Bool Phase Unit input where
  tapes := { Cfg.init Phase.start input with state := none, output := [false, true] }
  channels := fun _ => ⟨[], true :: suffix, 0⟩

private def cutoff (input suffix : List Bool) : Config 0 Bool Phase Unit input where
  tapes := { Cfg.init Phase.start input with state := some .copy }
  channels := fun _ => ⟨[], false :: suffix, 0⟩

-- The full final configuration retains the reply suffix. Siblings independently end at counter 2,
-- with the same two requests; a globally threaded sibling state would end the last path at 4.
private theorem run_padded (input suffix : List Bool) (padding : ℕ) :
    machine.runOccurrenceTrace (5 + padding) (machine.initialConfig input) (record suffix) (0, []) =
      [(([0], early input), (0, [])),
        (([1, 0, 0, 0, 0], finished input suffix), (2, [[true], [false]])),
        (([2, 0, 0, 0, 0], finished input suffix), (2, [[true], [false]]))] := by
  rw [Nat.add_comm]
  simp [runOccurrenceTrace, interpret_runOccurrenceProgram_succ,
    runOccurrenceProgram_halted, machine, initialConfig, action, record, early,
    finished, Config.step, Config.receive, Config.answerSymbols,
    Channel.answerSymbol, Turing.Action.apply, Cfg.init, List.ofFn_succ,
    Fin.getElem_fin, funext_iff]


-- Fuel 2 observes the query reply but has not yet read it into the next request or halted.
private theorem run_two (input suffix : List Bool) :
    machine.runOccurrenceTrace 2 (machine.initialConfig input) (record suffix) (0, []) =
      [(([0], early input), (0, [])),
        (([1, 0], cutoff input suffix), (1, [[true]])),
        (([2, 0], cutoff input suffix), (1, [[true]]))] := by
  simp [runOccurrenceTrace, interpret_runOccurrenceProgram_succ,
    runOccurrenceProgram_halted, machine, initialConfig, action, record, early,
    cutoff, Config.step, Config.receive, Config.answerSymbols,
    Channel.answerSymbol, Turing.Action.apply, Cfg.init, List.ofFn_succ,
    Fin.getElem_fin, funext_iff]



-- Chronological enumeration varies the first transition in the outer loop, with no duplicates.
example :
    indexWords 2 2 = [[0, 0], [0, 1], [1, 0], [1, 1]] ∧
    (indexWords 3 2).Nodup ∧
    (indexWords 3 2).length = 9 :=
  by decide

-- Exactly three certificates survive, even though the two querying paths have equal endpoints.
example (input suffix : List Bool) (padding : ℕ) :
    (indexWords 3 (5 + padding)).filterMap
        (fun word => machine.replayResult (machine.initialConfig input) word
          (record suffix) (0, [])) =
      [(([0], early input), (0, [])),
        (([1, 0, 0, 0, 0], finished input suffix), (2, [[true], [false]])),
        (([2, 0, 0, 0, 0], finished input suffix), (2, [[true], [false]]))] := by
  rw [filterMap_replayResult machine 3 (by decide) bounded, run_padded]

-- Erasing full stored replies leaves observations independent of their arbitrarily long suffixes.
example (input suffix : List Bool) :
    (machine.runOccurrenceTrace 5 (machine.initialConfig input) (record suffix) (0, [])).map
        (fun ((trace, cfg), state) => ((trace, cfg.tapes.output), state)) =
      [(([0], []), (0, [])),
        (([1, 0, 0, 0, 0], [false, true]), (2, [[true], [false]])),
        (([2, 0, 0, 0, 0], [false, true]), (2, [[true], [false]]))] := by
  rw [show 5 = 5 + 0 from rfl, run_padded]
  rfl

-- Both verdict counts require a terminal success; a live cutoff is neither verdict.
example (input suffix : List Bool) :
    (indexWords 3 5).countP (fun word =>
      (machine.replayResult (machine.initialConfig input) word (record suffix) (0, [])).any
        fun result => result.1.2.tapes.state.isNone &&
          result.1.2.tapes.output == [false, true]) = 2 := by
  rw [countP_replayResult_terminal machine 3 (by decide) bounded 5 _ _ _
    (fun output => output == [false, true]), show 5 = 5 + 0 from rfl, run_padded]
  rfl

example (input suffix : List Bool) :
    (indexWords 3 2).countP (fun word =>
      (machine.replayResult (machine.initialConfig input) word (record suffix) (0, [])).any
        fun result => result.1.2.tapes.state.isNone &&
          result.1.2.tapes.output == [false, true]) = 0 := by
  rw [countP_replayResult_terminal machine 3 (by decide) bounded 2 _ _ _
    (fun output => output == [false, true]), run_two]
  rfl

example (input suffix : List Bool) :
    (indexWords 3 2).countP (fun word =>
      (machine.replayResult (machine.initialConfig input) word (record suffix) (0, [])).any
        fun result => result.1.2.tapes.state.isNone &&
          !(result.1.2.tapes.output == [false, true])) =
      1 := by
  rw [countP_replayResult_terminal machine 3 (by decide) bounded 2 _ _ _
    (fun output => !(output == [false, true])), run_two]
  rfl

-- The raw cutoff is present, and its actual query has already advanced only its own oracle state.
example (input suffix : List Bool) :
    machine.replayResult (machine.initialConfig input) [1, 0] (record suffix) (0, []) =
      some (([1, 0], cutoff input suffix), (1, [[true]])) := by
  have hrecord : StateT.run (m := Id) (record suffix ((), [true])) (0, []) =
      pure (false :: suffix, (1, [[true]])) := rfl
  simp [replayResult, replayIndices, replayIndicesFrom, machine, initialConfig,
    StateT.run_map, action, hrecord, cutoff, Config.step,
    Config.receive, Turing.Action.apply, Cfg.init, funext_iff]

-- Invalid local indices and nonzero post-halt padding are excluded, not counted as rejections.
example (input suffix : List Bool) :
    machine.replayResult (machine.initialConfig input) [3] (record suffix) (0, []) = none ∧
    machine.replayResult (machine.initialConfig input) [1, 1] (record suffix) (0, []) = none ∧
    machine.replayResult (machine.initialConfig input) [0, 1] (record suffix) (0, []) = none :=
  ⟨rfl, rfl, rfl⟩

example (input suffix : List Bool) :
    machine.replayResult (machine.initialConfig input) [0, 0, 0] (record suffix) (0, []) =
      some (([0], early input), (0, [])) := by
  simp [replayResult, replayIndices, replayIndicesFrom, machine, initialConfig,
    action, early, Config.step, Turing.Action.apply, Cfg.init, funext_iff]

private def stuck : MultiTapeMachine 0 Bool Unit Unit List where
  initial := ()
  tr _ _ _ _ := []

-- No halting claim follows from an empty result list. Fuel zero still retains the live input.
example (input : List Bool) :
    stuck.runOccurrenceTrace 0 (stuck.initialConfig input) (record []) (0, []) =
      [(([], stuck.initialConfig input), (0, []))] ∧
    stuck.runOccurrenceTrace 1 (stuck.initialConfig input) (record []) (0, []) = [] ∧
    stuck.replayResult (stuck.initialConfig input) [] (record []) (0, []) =
      some (([], stuck.initialConfig input), (0, [])) ∧
    stuck.replayResult (stuck.initialConfig input) [0] (record []) (0, []) = none :=
  ⟨rfl, rfl, rfl, rfl⟩


example (input suffix : List Bool) :
    (machine.runOccurrenceTrace 2 (machine.initialConfig input) (record suffix) (0, [])).filter
        (fun result => result.1.2.tapes.state.isNone) = [(([0], early input), (0, []))] := by
  rw [run_two]
  rfl

example (input suffix : List Bool) :
    Id.run ((OracleComp.interpret (m := StateT History Id) (record suffix)
      (machine.replayTerminal (machine.initialConfig input) [1, 0])).run (0, [])) =
      (none, (1, [[true]])) := by
  have hrecord : StateT.run (m := Id) (record suffix ((), [true])) (0, []) =
      pure (false :: suffix, (1, [[true]])) := rfl
  simp [replayTerminal, replayIndices, replayIndicesFrom, machine, initialConfig,
    StateT.run_map, hrecord, action, Config.step, Config.receive, Turing.Action.apply]

-- A bad index after a real reply still cannot enter either verdict class.
example (input suffix : List Bool) :
    machine.replayResult (machine.initialConfig input) [1, 0, 1]
      (record suffix) (0, []) = none := by
  have hrecord : StateT.run (m := Id) (record suffix ((), [true])) (0, []) =
      pure (false :: suffix, (1, [[true]])) := rfl
  simp [replayResult, replayIndices, replayIndicesFrom, machine, initialConfig,
    StateT.run_map, hrecord, action, Config.step, Config.receive, Turing.Action.apply,
    Cfg.init]

private def closedStuck : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := []

-- Closed raw projection keeps a live cutoff; closed terminal replay rejects that same endpoint.
example (input : List Bool) :
    (closedStuck.runOccurrenceTrace 0 (closedStuck.initialConfig input)
        (fun q : Empty × List Bool => q.1.elim) ()).map
        (fun ((_, final), state) => (final.tapes, state)) =
      [(Cfg.init () input, ())] := by
  exact closedStuck.runOccurrenceTrace_empty 0 (Cfg.init () input) ()

example (input : List Bool) :
    Id.run (OracleComp.interpret (m := Id) (fun q : Empty × List Bool => q.1.elim)
      (closedStuck.replayTerminal (closedStuck.initialConfig input) [])) = none := rfl

-- Without an occurrence handler at Fin 0 there is no total PMF interpretation; this task uses List.
example {S : Type} (handler : (n : ℕ) → StateT S PMF (MultiTapeCTM.occurrenceSpec n)) (s : S) :
    False := by
  obtain ⟨result, _⟩ := (handler 0 s).support_nonempty
  exact result.1.elim0

end ComplexityTests.CountingOracle
