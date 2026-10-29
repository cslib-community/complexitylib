/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Cert.Step
public import Complexity.Computability.Machines.ReadMachine.Tidy

/-!
# The Tree Evaluation read machine within its space budget

The halting test, the address and the step of `Cslib.TreeEval.Reader.machine` are computable
within the space budget `Cslib.TreeEval.Reader.stateBudget` of its states, and the step machine
simulating it has a plain resource certificate.

## Main definitions

* `Cslib.TreeEval.Reader.stateBudget`: the space budget of a state.

## Main results

* `Cslib.TreeEval.Reader.machine_resourceCertificate`: the simulating step machine has a resource
  certificate.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, which the machine runs.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableInSpace Iter

/-- The tuple with the bit `false`, as an input of a step. -/
theorem pairFalse_inSpace :
    ComputableInSpace (fun x : Tuple => (x, false)) encTuple encStepInT
      fun x => stepBudget (x, false) :=
  (budget_prod (of_inO (ComputableInO.of_eq (f := id) fun _ => rfl))
    (budget_const (encB := encBool) false (.refl _))).weaken
    (.of_le fun x => by
      simp only [stepBudget, encStepInT, length_encPair, encBool_apply, List.length_singleton]
      omega)

/-- A function of the tuple with the bit `false` within the budget of the step. -/
private theorem onTuple {β : Type} {encB : β ↪ List Bool} {f : Tuple × Bool → β}
    (h : ComputableInSpace f encStepInT encB stepBudget) :
    ComputableInSpace (fun x : Tuple => f (x, false)) encTuple encB
      fun x => stepBudget (x, false) :=
  budget_comp h pairFalse_inSpace (.refl _)

/-- **The halting test** on tuples. -/
private theorem haltT_inSpace :
    ComputableInSpace haltT encTuple encBool fun x => stepBudget (x, false) :=
  onTuple (budget_finite (encC := encBool) (fun t : Fin 7 => decide (t = 6)) tag_inSpace)

/-- The offset of the node at the path of a stack. -/
private theorem offsetT_inSpace {st : Tuple × Bool → List Frame}
    (hst : ComputableInSpace st encStepInT (encList encFrame) stepBudget) :
    ComputableInSpace (fun y => offsetT y.1 (st y)) encStepInT encNat stepBudget := by
  have hdirs := budget_comp dirs_inSpace hst (.const_mul 64 ((length_le hst).add (.const 1 _)))
  have harg := budget_prod (budget_prod ell_inSpace height_inSpace) hdirs
  have hpo := budget_comp pathOffset_inSpace harg (.const_mul (2 ^ 30)
    (((ell_le_stepBudget.add height_le_stepBudget).add (length_le harg)).add (.const 1 _)))
  have h₂ := succ_inSpace (succ_inSpace (budget_natAdd ell_inSpace height_inSpace))
  refine (budget_natAdd h₂ hpo).of_enc_eq fun y => ?_
  simp only [offsetT, path_eq_reverse, foldl_cons_dir, List.append_nil]

/-- **The address** on tuples. -/
private theorem addrT_inSpace :
    ComputableInSpace addrT encTuple (encOption encNat) fun x => stepBudget (x, false) := by
  have ht (k : Fin 7) :=
    budget_finite (encC := encBool) (fun t : Fin 7 => decide (t = k)) tag_inSpace
  have h := budget_ite (ht 0) (budget_optionSome n₁_inSpace)
    (budget_ite (ht 1) (budget_optionSome (budget_natAdd (succ_inSpace ell_inSpace) n₁_inSpace))
    (budget_ite (ht 4)
      (budget_optionSome (budget_natAdd (offsetT_inSpace stack_inSpace) n₁_inSpace))
      (budget_ite (ht 5)
        (budget_optionSome (budget_natAdd (offsetT_inSpace rest_inSpace) n₁_inSpace))
        (budget_const (encB := encOption encNat) none len_le_stepBudget))))
  refine (onTuple h).of_enc_eq fun x => ?_
  simp only [addrT, decide_eq_true_eq]

/-! ### On states -/

/-- **The space budget of a state.** -/
def stateBudget (s : State) : ℕ := stepBudget (s.toTuple, false)

private theorem stepBudget_bool (x : Tuple) (b : Bool) : stepBudget (x, b) = stepBudget
    (x, false) := by
  simp [stepBudget, encBool_apply]

private theorem halt_inSpace : ComputableInSpace machine.halt encState encBool stateBudget :=
  (haltT_inSpace.of_encIn_eq State.toTuple fun _ => rfl).of_enc_eq fun s => by
    rw [haltT_toTuple]

private theorem addr_inSpace : ComputableInSpace machine.addr encState (encOption encNat)
    stateBudget :=
  (addrT_inSpace.of_encIn_eq State.toTuple fun _ => rfl).of_enc_eq fun s => by
    rw [addrT_toTuple]; rfl

private theorem step_inSpace :
    ComputableInSpace (fun p : State × Bool => machine.step p.1 p.2)
      (encPair encState encBool) (encPair encState encBits) fun p => stateBudget p.1 := by
  have h := stepT_inSpace.of_encIn_eq (fun p : State × Bool => (p.1.toTuple, p.2)) fun p => by
    rw [encPair_apply, encPair_apply, encState_apply]
  refine (h.mono_le fun p => ?_).of_enc_eq fun p => ?_
  · simp only [stateBudget, stepBudget_bool]; exact le_rfl
  · rw [stepT_toTuple, encPair_apply, encPair_apply, encState_apply]

/-- **The simulating step machine has a resource certificate**, within the space of its states
together with the position of its head. -/
theorem machine_resourceCertificate :
    ∃ T, machine.toStepMachine.ResourceCertificate (encPair encState encNat)
    (ReadMachine.stateT encState T stateBudget) (ReadMachine.stateS encState stateBudget) := by
  obtain ⟨T₁, h₁⟩ := halt_inSpace.exists_inO
  obtain ⟨T₂, h₂⟩ := addr_inSpace.exists_inO
  obtain ⟨T₃, h₃⟩ := step_inSpace.exists_inO
  let T : State → ℕ := fun s => T₁ s + T₂ s + T₃ (s, false) + T₃ (s, true)
  exact ⟨T, ReadMachine.toStepMachine_resourceCertificate
    (h₁.mono_le (fun s => by simp only [T]; omega)
    fun _ => le_rfl) (h₂.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₃.mono_le (fun p => by rcases p with ⟨s, _ | _⟩ <;> simp only [T] <;> omega)
      fun _ => le_rfl)⟩

end Reader

end Cslib.TreeEval
