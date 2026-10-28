/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.Composition
import Mathlib.Tactic.FinCases

/-! Buffered counting clients with unequal stopping times, duplicate branches, dirty source
scratch, a moved real input head, blank consumer scratch and ordered nonempty/empty words. -/

namespace ComplexityTests.CountingComposition

open Cslib Turing MultiTapeCTM MultiTapeMachine

private def write (bit : Option Bool) (next : Option Bool) :
    MultiTapeMachine.Action 1 Bool Bool Empty :=
  .step
    { inputTape := 1, workTapes := fun _ => (some (some false), -1)
      output := bit, state := next }
    Empty.elim Empty.elim

-- One occurrence emits nothing and halts early. Two identical occurrences write [true, false].
-- Every actual instruction dirties source scratch and moves the real input head.
private def chooseWord : MultiTapeCTM 1 Bool Bool where
  initial := false
  tr state _ _ _ := if state then [write (some false) none]
    else [write none none, write (some true) (some true), write (some true) (some true)]

-- Read two symbols in order, checking that the consumer's own scratch is blank.
-- The final instruction occurs twice, so each source branch has two terminal continuations.
private def readWord : MultiTapeCTM 1 Bool Bool where
  initial := false
  tr state symbol work _ := List.replicate (if state then 2 else 1)
    (.step
      { inputTape := 1, workTapes := fun _ => (none, 0)
        output := if work 0 = none then symbol else some false
        state := if state then none else some true }
      Empty.elim Empty.elim)

private theorem chooseWord_nonblocking : chooseWord.Nonblocking := by
  intro state symbol work
  cases state <;> simp [chooseWord]

private theorem readWord_nonblocking : readWord.Nonblocking := by
  intro state symbol work
  cases state <;> simp [readWord]

private theorem chooseWord_halts (input : List Bool) :
    chooseWord.HaltsWithin 2 (Cfg.init chooseWord.initial input) := by
  apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index
  · exact HaltsWithin.halt rfl
  all_goals
    apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
    intro index
    fin_cases index
    exact HaltsWithin.halt rfl

private theorem readWord_halts (input : List Bool) :
    readWord.HaltsWithin 2 (Cfg.init readWord.initial input) := by
  apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index
  apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index <;> exact HaltsWithin.halt rfl

private noncomputable def compiled := readWord.comp chooseWord true

-- Source 2 + buffer preparation (2 + 4) + consumer 2 = 10, with no additional handoff step.
private theorem compiled_halts (input : List Bool) :
    compiled.HaltsWithin 10 (compiled.initialConfig input).tapes :=
  HaltsWithin.comp chooseWord readWord chooseWord_nonblocking readWord_nonblocking
    true input 2 2 (chooseWord_halts input) (fun result _ => readWord_halts result.output)

-- Both table contracts are preserved by composition.
example : compiled.Nonblocking :=
  chooseWord_nonblocking.comp readWord_nonblocking true

-- Order matters: the real input is [false, true], while the generated nonempty word is reversed.
example : (compiled.runList 10 (compiled.initialConfig [false, true]).tapes).map Cfg.output =
    [[], [], [true, false], [true, false], [true, false], [true, false]] := by
  unfold compiled
  rw [runList_comp chooseWord readWord chooseWord_nonblocking readWord_nonblocking
    true [false, true] 2 2 (chooseWord_halts _) (fun result _ => readWord_halts result.output)]
  decide

-- The native counts are 4 for the two-symbol word and 2 for the empty word.
example :
    compiled.branchCount (· == [true, false]) 10
      (compiled.initialConfig [false, true]).tapes = 4 ∧
    compiled.branchCount List.isEmpty 10
      (compiled.initialConfig [false, true]).tapes = 2 := by
  unfold compiled
  constructor
  · rw [branchCount_comp chooseWord readWord chooseWord_nonblocking readWord_nonblocking
      true [false, true] 2 2 (chooseWord_halts _) (fun result _ => readWord_halts result.output)]
    decide
  · rw [branchCount_comp chooseWord readWord chooseWord_nonblocking readWord_nonblocking
      true [false, true] 2 2 (chooseWord_halts _) (fun result _ => readWord_halts result.output)]
    decide

-- Padding past every first halt contributes no additional preparation or consumer choices.
example (padding : ℕ) : compiled.branchCount (fun _ => true) (10 + padding)
    (compiled.initialConfig [false, true]).tapes = 6 := by
  rw [← countP_runList, compiled.runList_add_of_halted 10 padding _
    (fun _ hmem => (compiled_halts _).halted_of_mem_runList hmem),
    countP_runList compiled (fun _ => true)]
  unfold compiled
  rw [branchCount_comp chooseWord readWord chooseWord_nonblocking readWord_nonblocking
    true [false, true] 2 2 (chooseWord_halts _) (fun result _ => readWord_halts result.output)]
  decide

-- Tape 0 belongs to the consumer and stays blank; tape 1 retains source scratch and its head.
-- The real input head remains where the source left it, even while virtual input is consumed.
example : (compiled.runList 10 (compiled.initialConfig [false, true]).tapes).map
    (fun cfg => (cfg.inputPos.val, cfg.workTapePos 1, cfg.workTapes 1 0,
      cfg.workTapePos 0, cfg.workTapes 0 0)) =
    [(2, -1, some false, 0, none), (2, -1, some false, 0, none),
      (3, -2, some false, 0, none), (3, -2, some false, 0, none),
      (3, -2, some false, 0, none), (3, -2, some false, 0, none)] := by
  unfold compiled
  rw [runList_comp chooseWord readWord chooseWord_nonblocking readWord_nonblocking
    true [false, true] 2 2 (chooseWord_halts _) (fun result _ => readWord_halts result.output)]
  decide

-- Empty-buffer preparation still pays four native steps and contributes one path, not 2^4.
private def emptyResult : Config 1 Bool Bool Empty [false, true] :=
  Config.emptyOracleEquiv.symm (Cfg.init false [false, true])

example : (ofDeterministic (MultiTapeTM.prepareInput 2 true)).runList 4
    ((MultiTapeMachine.Composition.buffer 1 emptyResult).tapes.withState
      (some (MultiTapeTM.prepareInput 2 true).q₀)) =
    [(MultiTapeMachine.Composition.ready true 1 emptyResult).tapes] := by
  rw [runList_ofDeterministic]
  exact congrArg List.singleton (MultiTapeMachine.Composition.runFrom_prepare true 1 emptyResult)

example : (ofDeterministic (MultiTapeTM.prepareInput 2 true)).branchCount (fun _ => true) 4
    ((MultiTapeMachine.Composition.buffer 1 emptyResult).tapes.withState
      (some (MultiTapeTM.prepareInput 2 true).q₀)) = 1 := by
  have h := MultiTapeMachine.Composition.runFrom_prepare true 1 emptyResult
  change (MultiTapeTM.prepareInput 2 true).runFrom _ 4 = _ at h
  rw [branchCount_ofDeterministic _ _ _ _ (by rw [h]; rfl)]
  rfl

-- An initial output prefix is retained in the general growth bound, rather than silently free.
example :
    (∀ final ∈ chooseWord.runList 2
      { Cfg.init chooseWord.initial [false, true] with output := [true] },
      final.output.length ≤ 3) ∧
    (∃ final ∈ chooseWord.runList 2
      { Cfg.init chooseWord.initial [false, true] with output := [true] },
      final.output.length = 3) ∧
    ∃ final ∈ chooseWord.runList 0
      { Cfg.init chooseWord.initial [false, true] with output := [true] },
      ¬final.output.length ≤ 0 :=
  ⟨fun final hmem => chooseWord.length_output_of_mem_runList 2 _ final hmem, by decide, by simp⟩

end ComplexityTests.CountingComposition
