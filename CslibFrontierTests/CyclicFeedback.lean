/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Cyclic.Feedback
import CslibFrontier.Computability.Circuit.Monotone.Formula
import CslibFrontier.Computability.Circuit.Monotone.Set

/-!
# Native functional updates with feedback

Compile an ordinary union formula and close its state input. The least result is the external
seed. Repeated feedback outputs retain sharing and unused weighted operations; the empty state
needs no gates. Pure input aliases do not meet the internal-output contract.
-/

namespace CslibFrontierTests.CyclicFeedback

open Cslib.Circuits

private abbrev update : Circuit Monotone.signature (1 + 1) 1 :=
  (Monotone.or (.input 0) (.input 1)).toCircuit

private theorem update_outputs (i : Fin 1) : ∃ j, update.outputs i = .gate j :=
  ⟨⟨0, by decide⟩, rfl⟩

private theorem update_eval {U : Type*} (A : Set U) (state : Fin 1 → Set U) :
    update.eval (Monotone.setInterpretation U) (Fin.append ![A] state) =
      fun _ => A ∪ state 0 := by
  funext i
  simp [update, Formula.eval_toCircuit, Monotone.or, Fin.append, Fin.addCases]

private def seededStep {U : Type*} (A : Set U) : (Fin 1 → Set U) →o (Fin 1 → Set U) where
  toFun state _ := A ∪ state 0
  monotone' _ _ h _ := Set.union_subset_union Set.Subset.rfl (h 0)

example {U : Type*} (A : Set U) : (update.feedback update_outputs).eval
    (Monotone.setInterpretation U) Monotone.setInterpretation_mono ![A] = (seededStep A).lfp :=
  update.eval_feedback_eq_lfp update_outputs (Monotone.setInterpretation U)
    Monotone.setInterpretation_mono ![A] (seededStep A) (update_eval A)

example {U : Type*} (A : Set U) : (update.feedback update_outputs).eval
    (Monotone.setInterpretation U) Monotone.setInterpretation_mono ![A] = fun _ => A := by
  apply le_antisymm
  · apply update.eval_feedback_le
    rw [update_eval]
    exact fun _ => Set.union_subset Set.Subset.rfl Set.Subset.rfl
  · have h := update.eval_feedback_fixed update_outputs (Monotone.setInterpretation U)
      Monotone.setInterpretation_mono ![A]
    rw [update_eval] at h
    exact fun i => (Set.subset_union_left (t := _)).trans_eq (congrFun h i)

-- The operation is computable; its proof of internal outputs carries no chosen gate data.
example (weight : Monotone.Op → ℕ) :
    (update.feedback update_outputs).cost weight = weight .or := by
  simp [update, Formula.cost_toCircuit, Monotone.or, Fin.sum_univ_two]

private abbrev withUnused : Circuit Monotone.signature (1 + 2) 2 :=
  (Monotone.or (.input 0) (.input 1)).toCircuit.append
    (Monotone.and (.input 2) (.input 2)).toCircuit

private abbrev repeatedOutput : Fin 2 → Fin withUnused.size := fun _ => ⟨0, by decide⟩

-- Both state inputs feed the first gate; the unused conjunction is still charged.
example : (withUnused.program.feedback repeatedOutput).cost Monotone.andCost = 1 := by decide

example : (withUnused.program.feedback repeatedOutput).outputs 0 =
    (withUnused.program.feedback repeatedOutput).outputs 1 := rfl

example : ((Circuit.wiring Monotone.signature (Fin.elim0 : Fin 0 → Fin (2 + 0))).feedback
    (fun i => i.elim0)).size = 0 := rfl

example : ¬ ∀ i, ∃ j, (Circuit.wiring Monotone.signature ![(1 : Fin 2)]).outputs i =
    .gate j := by
  intro h
  obtain ⟨j, hj⟩ := h 0
  cases hj

end CslibFrontierTests.CyclicFeedback
