/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential

/-! Sequencing with random stopping times, shared channels, and stateful coin/query handlers. -/

namespace CslibFrontierTests.MachineSequential

open Cslib Turing MultiTapeMachine MultiTapeMachine.Sequential

private def action (output : Option Bool) (next : Option Bool) : Turing.Action 0 Bool Bool where
  inputTape := 0
  workTapes := Fin.elim0
  output := output
  state := next

-- Both channels receive the sampled bit. False takes an extra instruction before handoff.
private def prepare : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr state _ _ _ bit := if state then
    .step (action none none) (fun _ => none) (fun _ => 0)
    else .step (action none (if bit then none else some true)) (fun _ => some bit) (fun _ => 0)

-- Query only the true channel and emit its reply, preserving the other channel's buffer.
private def respond : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr state _ _ answer _ := if state then
    .step (action (answer true) none) (fun _ => none) (fun _ => 0)
    else .query true true

private abbrev Query := Unit ⊕ (Bool × List Bool)

private def spec : OracleSpec Query
  | .inl _ => Bool
  | .inr _ => List Bool

private def coin : OracleComp spec Bool := OracleComp.query (spec := spec) (.inl ())

private def query (op : Bool) (word : List Bool) : OracleComp spec (List Bool) :=
  OracleComp.query (spec := spec) (.inr (op, word))

private abbrev History := ℕ × List (Bool × List Bool)

-- Query replies depend on the number of coins already consumed, including the query instruction.
private def record (bit : Bool) : (q : Query) → StateT History Id (spec q)
  | .inl _ => modifyGet fun (count, requests) => (bit, (count + 1, requests))
  | .inr request => modifyGet fun (count, requests) =>
    ([count % 2 == 0], (count, requests ++ [request]))

private def observe (cfg : Config 0 Bool (Bool ⊕ Bool) Bool []) :=
  (cfg.tapes.output, (cfg.channels false).queryBuffer, (cfg.channels true).queryBuffer,
    (cfg.channels true).answer, cfg.tapes.state)

-- A one-instruction first phase hands off immediately. No dummy coin is drawn for spare fuel.
example : (OracleComp.interpret (record true) (observe <$>
    (prepare.seq respond).runConfigFrom coin query 4
      ((prepare.seq respond).initialConfig []))).run (7, [(false, [])]) =
    (([false], [true], [], [false], none), (10, [(false, []), (true, [true])])) := by rfl

-- The other branch takes two instructions and passes the same private state to the continuation.
example : (OracleComp.interpret (record false) (observe <$>
    (prepare.seq respond).runConfigFrom coin query 4
      ((prepare.seq respond).initialConfig []))).run (7, [(false, [])]) =
    (([true], [false], [], [true], none), (11, [(false, []), (true, [false])])) := by rfl

private theorem prepare_halts {S : Type} (oracle : (q : Query) → StateT S PMF (spec q))
    (input : List Bool) (s : S) : ∀ result ∈ ((OracleComp.interpret oracle
      (prepare.runConfigFrom coin query 2 (prepare.initialConfig input))).run s).support,
      result.1.tapes.state = none := by
  rintro ⟨final, s'⟩ hfinal
  simp only [MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, prepare,
    MultiTapeMachine.initialConfig, Cfg.init, Bool.false_eq_true, ↓reduceIte, bind_map_left,
    OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hfinal
  obtain ⟨⟨bit, s₁⟩, _, hfinal⟩ := hfinal
  cases bit <;> aesop (add simp [Config.step, Turing.Action.apply, action])

private theorem respond_halts {S : Type} (oracle : (q : Query) → StateT S PMF (spec q))
    {input : List Bool} (cfg : Config 0 Bool Bool Bool input) (s : S) :
    ∀ result ∈ ((OracleComp.interpret oracle
      (respond.runConfigFrom coin query 2 (start respond cfg))).run s).support,
      result.1.tapes.state = none := by
  rintro ⟨final, s'⟩ hfinal
  simp only [MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, start,
    Cfg.withState, respond, Bool.false_eq_true, ↓reduceIte, bind_map_left,
    OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hfinal
  obtain ⟨⟨_, s₁⟩, _, ⟨⟨answer, s₂⟩, _, hfinal⟩⟩ := hfinal
  aesop (add simp [Config.receive, Config.step, Turing.Action.apply, action])

-- Both halting hypotheses hold for every stateful probabilistic interpreter, not just a test coin.
example : prepare.HaltsWithin (fun choices => choices <$> coin) query 5 [] := by
  apply HaltsWithin.mono (fuel := 2) _ (by decide)
  intro S oracle s final s' hfinal
  exact prepare_halts oracle [] s (final, s') hfinal

example {S : Type} (oracle : (q : Query) → StateT S PMF (spec q)) (input : List Bool) (s : S) :
    (OracleComp.interpret oracle ((prepare.seq respond).runConfigFrom coin query 4
      ((prepare.seq respond).initialConfig input))).run s =
      ((OracleComp.interpret oracle
        (prepare.runConfigFrom coin query 2 (prepare.initialConfig input))).run s).bind
        (fun result => ((OracleComp.interpret oracle
          (respond.runConfigFrom coin query 2 (start respond result.1))).run result.2).map
          (fun (final, s') => (right final, s'))) := by
  exact MultiTapePTM.run_interpret_runConfigFrom_seq prepare respond coin query oracle
    (prepare.initialConfig input) 2 2 s (prepare_halts oracle input s)
    (fun result _ => respond_halts oracle result.1 result.2)

private def emitForever : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr _ _ _ _ _ := .step (action (some true) (some false)) (fun _ => none) (fun _ => 0)

-- A clock alone does not justify composition: leftover first-phase time lets this continuation
-- emit three bits, whereas running it separately for its two-instruction clock emits only two.
example : (OracleComp.interpret (record true)
      ((prepare.seq emitForever).run (pure true) query 4 [])).run (0, []) ≠
    (OracleComp.interpret (record true) (do
      let cfg ← prepare.runConfigFrom (pure true) query 2 (prepare.initialConfig [])
      emitForever.runFrom (pure true) query 2 (start emitForever cfg))).run (0, []) := by
  change (([true, true, true], (0, [])) : List Bool × History) ≠ ([true, true], (0, []))
  decide

end CslibFrontierTests.MachineSequential
