/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Clock
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.PrepareClock

/-! Clock consumption, stateless coin hypotheses, and tactic-certified budget preparation. -/

namespace ComplexityTests.MachineClock

open Cslib Turing MultiTapeMachine

private def echoForever : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr state _ _ answer _ := if state then
    .step { inputTape := 0, workTapes := Fin.elim0, output := answer true, state := some false }
      (fun _ => none) (fun _ => 0)
    else .query true true

private abbrev Query := Unit ⊕ (Bool × List Bool)

private def spec : OracleSpec Query
  | .inl _ => Bool
  | .inr _ => List Bool

private def coin : OracleComp spec Bool := OracleComp.query (spec := spec) (.inl ())

private def query (op : Bool) (word : List Bool) : OracleComp spec (List Bool) :=
  OracleComp.query (spec := spec) (.inr (op, word))

private def record : (q : Query) → StateT ℕ Id (spec q)
  | .inl _ => pure false
  | .inr _ => modifyGet fun count => ([count % 2 == 0], count + 1)

private noncomputable def oracle (law : PMF Bool) : (q : Query) → StateT ℕ PMF (spec q)
  | .inl _ => fun s => law.map (fun bit => (bit, s))
  | .inr _ => fun s => PMF.pure ([s % 2 == 0], s + 1)

private def initial : Config 0 Bool Bool Bool [] :=
  { echoForever.initialConfig [] with
    channels := fun op => { queryBuffer := if op then [true, false] else [false] } }

private def tape (budget : ℕ) : ℤ → Option Bool :=
  tapeOfList (List.replicate budget true)

private def observe (cfg : Config 1 Bool (Clock.Control Bool) Bool []) :=
  (cfg.tapes.output, (cfg.channels false).queryBuffer, (cfg.channels true).queryBuffer,
    (cfg.channels true).answer, cfg.tapes.state, cfg.tapes.workTapePos 0)

-- Three source instructions submit two queries; extra fuel causes no further query after cutoff.
example : (OracleComp.interpret record (observe <$> echoForever.withClock.runConfigFrom
    coin query 12 (Clock.config initial (tape 3) 0 false))).run 7 =
    (([false], [false], [], [true], none, 3), 9) := by rfl

-- A zero budget stops before even the first source query and retains both pending buffers.
example : (OracleComp.interpret record (observe <$> echoForever.withClock.runConfigFrom
    coin query 4 (Clock.config initial (tape 0) 0 false))).run 7 =
    (([], [false], [true, false], [], none, 0), 7) := by rfl

-- A halted source is padded, a false cell stops the clock, and its head may start below zero.
example : (OracleComp.interpret record (observe <$> echoForever.withClock.runConfigFrom
    coin query 8 (Clock.config
      { initial with tapes := { initial.tapes with state := none, output := [true] } }
      (fun z => some (z == -1)) (-1) false))).run 7 =
    (([true], [false], [true, false], [], none, 0), 7) := by rfl

-- The distribution theorem has a concrete stateful query interpreter and arbitrary coin law.
example (law : PMF Bool) (budget padding s : ℕ) :
    (OracleComp.interpret (oracle law)
      (echoForever.withClock.runConfigFrom coin query (2 * budget + 1 + padding)
        (Clock.config initial (tape budget) 0 false))).run s =
      ((OracleComp.interpret (oracle law)
        (echoForever.runConfigFrom coin query budget initial)).run s).map
        (fun (final, s') => (Clock.stopped final (tape budget) budget, s')) := by
  simpa only [zero_add] using
    MultiTapePTM.run_interpret_runConfigFrom_withClock_add echoForever coin query (oracle law) law
      (fun s => congrArg (fun p => p.run s) (OracleComp.interpret_query (oracle law) (.inl ())))
      initial (tape budget) 0 budget padding s
      (fun i hi => by simp [tape, tapeOfList_ofNat, hi])
      (by simp [tape, tapeOfList_ofNat])

private def countCoins : (q : Query) → StateT ℕ Id (spec q)
  | .inl _ => modifyGet fun count => (false, count + 1)
  | .inr _ => pure []

-- Statelessness is essential: even a zero budget consumes the controller's stopping coin.
example : (OracleComp.interpret countCoins
      (echoForever.withClock.runFrom coin query 1 (Clock.config initial (tape 0) 0 false))).run 0 ≠
    (OracleComp.interpret countCoins (echoForever.runFrom coin query 0 initial)).run 0 := by
  change (([], 1) : List Bool × ℕ) ≠ ([], 0)
  decide

-- Budget generation is a reusable functional certificate, including zero coefficient and degree.
example : MultiTapeTM.ComputableInPolyTime (MultiTapeTM.PolynomialClock.budget 0 7)
    MultiTapeTM.encBits MultiTapeTM.encBits := by fun_prop

example : MultiTapeTM.ComputableInPolyTime (MultiTapeTM.PolynomialClock.budget 5 0)
    MultiTapeTM.encBits MultiTapeTM.encBits := by fun_prop

end ComplexityTests.MachineClock
