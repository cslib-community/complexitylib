/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.OutputPrefix

/-! Fresh-input composition with random stopping times, dirty scratch, and empty output. -/

namespace ComplexityTests.ProbabilisticComposition

open Cslib Turing MultiTapeMachine

-- A true coin emits a bit and halts immediately. False emits nothing and halts one step later.
-- Both paths dirty the source scratch tape and move the real input head.
private def chooseWord : MultiTapePTM 1 Bool Bool where
  initial := false
  tr state _ _ _ bit := .step
    { inputTape := 1, workTapes := fun _ => (some (some false), -1)
      output := if !state && bit then some true else none
      state := if state || bit then none else some true }
    Empty.elim Empty.elim

-- The consumer must see its own blank scratch and the generated input, not the real input.
private def readFirst : MultiTapePTM 1 Bool Unit where
  initial := ()
  tr _ symbol work _ _ := .step
    { inputTape := 0, workTapes := fun _ => (none, 0)
      output := if work 0 = none then symbol else some false, state := none }
    Empty.elim Empty.elim

private theorem chooseWord_halts (input : List Bool) : ∀ final ∈ (ProbComp.eval
    (chooseWord.runClosedConfigFrom 2 (chooseWord.initialConfig input))).support,
    final.tapes.state = none := by
  intro final hfinal
  simp only [MultiTapePTM.runClosedConfigFrom, MultiTapePTM.runConfigFrom,
    MultiTapeMachine.runConfigFrom, initialConfig, Cfg.init, chooseWord,
    Bool.not_false, Bool.true_and, Bool.false_or, bind_map_left,
    ProbComp.eval_bind, PMF.mem_support_bind_iff] at hfinal
  obtain ⟨bit, _, hbit⟩ := hfinal
  cases bit <;> aesop (add simp [Config.step, Turing.Action.apply])

private theorem readFirst_halts (word : List Bool) : ∀ final ∈ (ProbComp.eval
    (readFirst.runClosedConfigFrom 1 (readFirst.initialConfig word))).support,
    final.tapes.state = none := by
  intro final hfinal
  simp only [MultiTapePTM.runClosedConfigFrom, MultiTapePTM.runConfigFrom,
    MultiTapeMachine.runConfigFrom, initialConfig, Cfg.init, readFirst, bind_map_left,
    ProbComp.eval_bind, PMF.mem_support_bind_iff] at hfinal
  obtain ⟨bit, _, hbit⟩ := hfinal
  aesop (add simp [Config.step, Turing.Action.apply])

private theorem chooseWord_output (input : List Bool) :
    ProbComp.eval (chooseWord.runClosed 2 input) =
      (ProbComp.eval (ProbComp.uniform Bool)).map (fun bit => if bit then [true] else []) := by
  simp only [MultiTapePTM.runClosed, MultiTapePTM.run, MultiTapePTM.runFrom,
    MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, initialConfig, Cfg.init,
    chooseWord, Bool.not_false, Bool.true_and, Bool.false_or, bind_map_left,
    ProbComp.eval_map, ProbComp.eval_bind, PMF.map_bind]
  rw [PMF.map]
  apply Probability.PMF.bind_congr_on_support
  intro bit _
  cases bit <;> simp [Config.step, Turing.Action.apply, PMF.map]

-- The real input is [false]. Correct virtual-input routing instead gives [true] or [],
-- and every final configuration in the support is halted.
example :
    ProbComp.eval ((readFirst.comp chooseWord true).runClosed 9 [false]) =
      (ProbComp.eval (ProbComp.uniform Bool)).map (fun bit => if bit then [true] else []) ∧
    ∀ final ∈ (ProbComp.eval ((readFirst.comp chooseWord true).runClosedConfigFrom
      9 ((readFirst.comp chooseWord true).initialConfig [false]))).support,
      final.tapes.state = none := by
  refine ⟨?_, MultiTapePTM.comp_halted chooseWord readFirst true [false] 2 1 (chooseWord_halts _)
    (fun word _ => readFirst_halts word)⟩
  rw [MultiTapePTM.eval_comp chooseWord readFirst true [false] 2 1 (chooseWord_halts _)
    (fun word _ => readFirst_halts word), Probability.PMF.monad_bind_eq_bind,
    chooseWord_output, PMF.bind_map]
  rw [PMF.map]
  apply Probability.PMF.bind_congr_on_support
  intro bit _
  cases bit <;> simp [MultiTapePTM.runClosed, MultiTapePTM.run, MultiTapePTM.runFrom,
    MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, initialConfig, Cfg.init,
    readFirst, Config.step, Turing.Action.apply, Cfg.inputSymbol, Cfg.workTapeSymbols,
    PMF.map, Function.comp_def]

-- Writing a prefix leaves the original input available to the following computation.
private def writePrefix : MultiTapeTM 1 Bool Unit := MultiTapeTM.ofTr ()
  fun _ _ _ =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := some true, state := none }

private theorem writePrefix_restores (input : List Bool) :
    writePrefix.runFrom (writePrefix.initCfg input) 1 =
      wordsCfg input none (fun _ => []) [true] := by
  simp only [MultiTapeTM.runFrom, Function.iterate_one]
  rw [MultiTapeTM.step_of_state (by rfl)]
  simp [writePrefix, MultiTapeTM.tr_ofTr, Turing.Action.apply, Cfg.init, wordsCfg]

-- Prefix [true] is followed by the actual input [false], with every preparation step charged.
example : ProbComp.eval (((MultiTapePTM.ofDeterministic writePrefix).seq readFirst).runClosed
    2 [false]) = PMF.pure [true, false] := by
  rw [MultiTapePTM.eval_seq_prependOutput writePrefix readFirst [false] [true] 1 1
    (writePrefix_restores _) (readFirst_halts _)]
  simp [MultiTapePTM.runClosed, MultiTapePTM.run, MultiTapePTM.runFrom,
    MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, initialConfig, Cfg.init,
    readFirst, Config.step, Turing.Action.apply, Cfg.inputSymbol, Cfg.workTapeSymbols,
    PMF.map, Function.comp_def]

end ComplexityTests.ProbabilisticComposition
