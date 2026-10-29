/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.Counting.Guess
import Complexity.Computability.Machines.Turing.MultiTape.Counting.Sequential
import Mathlib.Tactic.FinCases

/-! Native counting execution clients: duplicate endpoints, unequal stopping times, singleton
deterministic lifting, additive sequencing clocks and the explicit exclusion of stuck choices. -/

namespace ComplexityTests.CountingExecution

open Cslib Turing MultiTapeCTM

private def stop (bit : Bool) : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def advance : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }
    Empty.elim Empty.elim

private def mixed : MultiTapeCTM 0 Bool Bool where
  initial := false
  tr state _ _ _ := if state then [stop false, stop true, stop true] else [stop true, advance]

private theorem mixed_nonblocking : mixed.Nonblocking := by
  intro state symbol work
  cases state <;> simp [mixed]

private theorem mixed_halts (input : List Bool) :
    mixed.HaltsWithin 2 (Cfg.init mixed.initial input) := by
  apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index
  · exact HaltsWithin.halt rfl
  · apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
    intro index
    fin_cases index <;> exact HaltsWithin.halt rfl

-- Equal actions and final configurations remain distinct List occurrences and native branches;
-- a still-running endpoint at a short clock is not a rejecting terminal occurrence.
example (padding : ℕ) :
    (mixed.runList 2 (Cfg.init mixed.initial [])).map Cfg.output =
      [[true], [false], [true], [true]] ∧
    (mixed.runList 2 (Cfg.init mixed.initial [])).countP
      (fun final => final.state.isNone && final.output == [true]) = 3 ∧
    mixed.runList (2 + padding) (Cfg.init mixed.initial []) =
      mixed.runList 2 (Cfg.init mixed.initial []) ∧
    mixed.rejectCount 1 (Cfg.init mixed.initial []) = 0 ∧
    (mixed.runList 0 (Cfg.init mixed.initial [])).length = 1 ∧
    mixed.branchCount (fun _ => true) 0 (Cfg.init mixed.initial []) = 0 :=
  ⟨by decide,
    by rw [countP_runList mixed (· == [true])]; decide,
    mixed.runList_add_of_halted 2 padding _
      (fun _ hmem => (mixed_halts []).halted_of_mem_runList hmem),
    by decide, rfl, rfl⟩

private def doubleHalt : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := List.replicate 2
    (.step { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
      Empty.elim Empty.elim)

private theorem doubleHalt_nonblocking : doubleHalt.Nonblocking := by
  intro state symbol work
  simp [doubleHalt]

private theorem doubleHalt_halts {input : List Bool} (cfg : Cfg 0 Bool Bool input) :
    doubleHalt.HaltsWithin 1 (cfg.withState (some doubleHalt.initial)) := by
  apply HaltsWithin.step (by simp [actions, doubleHalt, Cfg.withState])
  intro index
  fin_cases index <;> exact HaltsWithin.halt rfl

private def composed : MultiTapeCTM 0 Bool (Bool ⊕ Unit) := mixed.seq doubleHalt

-- The early branch halts in two steps, the others in three; all multiplicities multiply by two.
example (input : List Bool) :
    composed.HaltsWithin 3 (Cfg.init composed.initial input) ∧
    composed.acceptCount 3 (Cfg.init composed.initial []) = 6 ∧
    composed.rejectCount 3 (Cfg.init composed.initial []) = 2 ∧
    composed.runList 3 (Cfg.init composed.initial input) =
      (mixed.runList 2 (Cfg.init mixed.initial input)).flatMap (fun result =>
        (doubleHalt.runList 1 (result.withState (some ()))).map
          (fun final => final.mapState (Option.map Sum.inr))) :=
  ⟨HaltsWithin.seq mixed_nonblocking doubleHalt_nonblocking
      (mixed.initialConfig input) 2 1 (mixed_halts input)
      (fun result _ => doubleHalt_halts result),
    by decide, by decide,
    runList_seq mixed doubleHalt (mixed.initialConfig input) 2 1 (mixed_halts input)
      (fun result _ => doubleHalt_halts result)⟩

private noncomputable def deterministic : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () (fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none })

private theorem deterministic_halts (input : List Bool) :
    (deterministic.runFrom (deterministic.initCfg input) 1).Halted := by
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state rfl]
  simp [deterministic, MultiTapeTM.tr_ofTr, Action.apply, Cfg.Halted]

-- The actual scanner and singleton deterministic lift satisfy the nonblocking contracts, and clock
-- padding never introduces additional copies of the single halting instruction.
example (input : List Bool) (padding : ℕ) :
    guessMachine.Nonblocking ∧
    (ofDeterministic deterministic).Nonblocking ∧
    (ofDeterministic deterministic).HaltsWithin 1 (deterministic.initCfg input) ∧
    (ofDeterministic deterministic).branchCount (fun _ => true) (1 + padding)
      (deterministic.initCfg input) = 1 := by
  refine ⟨GuessMachine.nonblocking,
    nonblocking_ofDeterministic deterministic,
    (haltsWithin_ofDeterministic_iff deterministic 1 (deterministic.initCfg input)).mpr
      (deterministic_halts input), ?_⟩
  apply (branchCount_ofDeterministic deterministic (fun _ => true) _ _ _).trans rfl
  rw [MultiTapeTM.runFrom_eq_of_halt deterministic _ (by lia) (deterministic_halts input)]
  exact deterministic_halts input

private def stuck : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := []

example :
    stuck.runList 1 (Cfg.init stuck.initial []) = [] ∧
    (∀ final ∈ stuck.runList 1 (Cfg.init stuck.initial []), final.Halted) ∧
    ¬stuck.Nonblocking ∧
    ¬stuck.HaltsWithin 1 (Cfg.init stuck.initial []) ∧
    stuck.acceptCount 1 (Cfg.init stuck.initial []) = 0 ∧
    stuck.rejectCount 1 (Cfg.init stuck.initial []) = 0 :=
  ⟨rfl,
    by change ∀ final ∈ ([] : List (Cfg 0 Bool Unit [])), final.Halted; simp,
    by simp [Nonblocking, stuck],
    fun h => by
      cases h with
      | halt hh => cases hh
      | step hnonempty _ => exact hnonempty rfl,
    rfl, rfl⟩

end ComplexityTests.CountingExecution
