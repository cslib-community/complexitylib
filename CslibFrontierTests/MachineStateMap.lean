/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Deterministic

/-! Noninjective control-state maps retain choice and query effects over a non-Boolean alphabet. -/

namespace ComplexityTests.MachineStateMap

open Cslib Turing Turing.MultiTapeMachine

-- The former public import still supports the original positional and named arguments.
example {k : ℕ} {Symbol State State' Oracle : Type} (e : State → State')
    (action : Action k Symbol State Oracle) :
    @Action.mapState k Symbol State State' Oracle e action =
      Action.mapState (e := e) action := rfl

example {k : ℕ} {Symbol State State' Oracle : Type} {input : List Symbol}
    (e : State → State') (cfg : Config k Symbol State Oracle input) :
    @Config.mapState k Symbol State State' Oracle input e cfg =
      Config.mapState (e := e) cfg := rfl

private abbrev Branches := ReaderT Bool Id

private def source : MultiTapeMachine 0 ℕ Bool Unit Branches where
  initial := false
  tr state _ _ _ coin := .query () (state ^^ coin)

private def target : MultiTapeMachine 0 ℕ Unit Unit Branches where
  initial := ()
  tr _ _ _ _ _ := .query () ()

private abbrev Request := Unit ⊕ (Unit × List ℕ)

private def spec : OracleSpec Request
  | .inl _ => Bool
  | .inr _ => List ℕ

private def choose {α : Type} (branches : Branches α) : OracleComp spec α :=
  branches <$> OracleComp.query (spec := spec) (.inl ())

private def query (op : Unit) (word : List ℕ) : OracleComp spec (List ℕ) :=
  OracleComp.query (spec := spec) (.inr (op, word))

-- The commuting tables are actual machines; no injectivity assumption hides the merged states.
private theorem map_run {input : List ℕ} (fuel : ℕ) (cfg : Config 0 ℕ Bool Unit input) :
    target.runConfigFrom choose query fuel (cfg.mapState (fun _ : Bool => ())) =
      Config.mapState (fun _ : Bool => ()) <$> source.runConfigFrom choose query fuel cfg := by
  apply runConfigFrom_mapState source target choose ?_ query (fun _ : Bool => ()) ?_ fuel cfg
  · intro α β f branches
    exact (Functor.map_map branches f (OracleComp.query (spec := spec) (.inl ()))).symm
  · intro state inp work answer
    funext coin
    rfl

private def record (request : Request) : StateT (List Request) Id (spec request) :=
  fun seen => match request with
  | .inl _ => (true, seen ++ [request])
  | .inr (_, word) => (word ++ [word.length], seen ++ [request])

private def initial : Config 0 ℕ Bool Unit [5] :=
  { source.initialConfig [5] with
    tapes := { (source.initialConfig [5]).tapes with output := [42] }
    channels := fun _ =>
      { queryBuffer := [3, 7], answer := [99], answerPos := -2 } }

-- Both choice calls remain, even though all target choices select the same action.
example :
    (OracleComp.interpret record
      ((fun cfg => (cfg.tapes.state, cfg.tapes.output,
        (cfg.channels ()).queryBuffer, (cfg.channels ()).answer,
        (cfg.channels ()).answerPos)) <$>
          target.runConfigFrom choose query 2 (initial.mapState (fun _ : Bool => ())))).run [] =
      ((some (), [42], [], [0], 0),
        [.inl (), .inr ((), [3, 7]), .inl (), .inr ((), [])]) := by
  rw [map_run]
  rfl

private def halted : Config 0 ℕ Bool Unit [5] :=
  { initial with tapes := { initial.tapes with state := none } }

-- Any fuel retains halted data and existing private history, without another request.
example (fuel : ℕ) :
    (OracleComp.interpret record
      (target.runConfigFrom choose query fuel (halted.mapState (fun _ : Bool => ())))).run
        [.inr ((), [88])] =
      (halted.mapState (fun _ : Bool => ()), [.inr ((), [88])]) := by
  rw [map_run, MultiTapeMachine.runConfigFrom_halted source choose query fuel halted rfl]
  rfl

end ComplexityTests.MachineStateMap
