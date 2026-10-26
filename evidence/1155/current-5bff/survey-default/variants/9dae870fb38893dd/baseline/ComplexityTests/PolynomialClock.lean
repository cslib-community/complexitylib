/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.PPT.Clock
import Complexity.Computability.Probabilistic.Sampling

/-! End-to-end clock compilation from blank tapes, with genuinely nonhalting sources. -/

namespace ComplexityTests.PolynomialClock

open Cslib Turing MultiTapeMachine MultiTapePTM.PolynomialClock

private def emitForever : MultiTapePTM 1 Bool Unit where
  initial := ()
  tr _ _ _ _ coin := .step
    { inputTape := 0, workTapes := fun _ => (some coin, 1), output := some coin, state := some () }
    Empty.elim Empty.elim

private noncomputable def prepareOne : MultiTapeTM 1 Bool Unit := MultiTapeTM.ofTr ()
  fun _ _ _ =>
    { inputTape := 0
      workTapes := fun _ => (some true, 0)
      output := none
      state := none }

private theorem prepareOne_ready (input : List Bool) :
    prepareOne.runFrom (prepareOne.initCfg input) 1 =
      wordsCfg input none (Function.update (fun _ => []) (Fin.last 0) [true]) [] := by
  simp only [MultiTapeTM.runFrom, Function.iterate_one]
  rw [MultiTapeTM.step_of_state (by rfl)]
  simp only [prepareOne, MultiTapeTM.tr_ofTr]
  refine Cfg.ext rfl (by simp [Turing.Action.apply, Cfg.init, wordsCfg]) ?_ ?_
    (by simp [Turing.Action.apply, Cfg.init, wordsCfg])
  · funext i z
    fin_cases i
    simp only [Turing.Action.apply, wordsCfg,
      tapeOfList, Function.update_apply]
    cases z with
    | ofNat n =>
      cases n with
      | zero => simp
      | succ n => simp [show (n : ℤ) + 1 ≠ 0 by lia]
    | negSucc n => simp
  · funext i
    rfl

-- The source never halts: even after a hundred emitted bits its control state is still active.
example : ((OracleComp.interpret (fun _ : Unit => (pure () : Id Unit))
    (emitForever.runConfigFrom (spec := fun _ : Unit => Unit) (pure true) Empty.elim 100
      (emitForever.initialConfig []))).tapes.state) = some () := by rfl

-- A single-cell budget is prepared from blank tapes; every larger clock gives the same halted run.
example (input : List Bool) (padding : ℕ) :
    (OracleComp.interpret (fun _ : Unit => (pure () : StateT ℕ PMF Unit))
      ((compile emitForever prepareOne).runConfigFrom
        (spec := fun _ : Unit => Unit) (pure true) Empty.elim (4 + padding)
        ((compile emitForever prepareOne).initialConfig input))).run 9 =
      PMF.pure (finish (r := 0) (PrepareState := Unit)
        ((emitForever.initialConfig input).step
          { inputTape := 0, workTapes := fun _ => (some true, 1),
            output := some true, state := some () } Empty.elim Empty.elim) 1, 9) := by
  have h := run_interpret_compile emitForever prepareOne (pure true) Empty.elim
    (fun _ : Unit => (pure () : StateT ℕ PMF Unit)) (PMF.pure true) (fun _ => by simp)
    input 1 1 padding 9 (prepareOne_ready input)
  simpa [← Nat.add_assoc, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom,
    emitForever, initialConfig, Cfg.init] using h

-- The uniform finite compiler applies to a nonhalting source and a quadratic input-size budget.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
    (c d : ℕ), ∀ input,
    ProbComp.eval (machine.runClosed (c * (input.length + 1) ^ d) input) =
      ProbComp.eval (emitForever.runClosed (3 * (input.length + 1) ^ 2) input) ∧
    ∀ final ∈ (ProbComp.eval (machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim
      (c * (input.length + 1) ^ d) (machine.initialConfig input))).support,
      final.tapes.state = none := emitForever.exists_halting_clock 3 2

-- A functional random program obtains a witness that also halts on malformed encoded inputs.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
    (c d : ℕ),
    (∀ bit : Bool, (ProbComp.eval (ProbComp.uniform Bool)).map MultiTapeTM.encBool =
      ProbComp.eval (machine.runClosed (c * ((MultiTapeTM.encBool bit).length + 1) ^ d)
        (MultiTapeTM.encBool bit))) ∧
    ∀ input,
    ∀ final ∈ (ProbComp.eval (machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim
      (c * (input.length + 1) ^ d) (machine.initialConfig input))).support,
      final.tapes.state = none :=
  (show Probability.IsPPTOn MultiTapeTM.encBool MultiTapeTM.encBool
    (fun _ => ProbComp.uniform Bool) by fun_prop).exists_halting_machine

end ComplexityTests.PolynomialClock
