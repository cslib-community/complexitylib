/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Cert.Step
public import Complexity.Computability.Machines.ReadMachine.Tidy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain

/-!
# The Tree Evaluation read machine within its space budget

The halting test, the address and the step of `Cslib.TreeEval.Reader.machine` are computable
within the space budget `Cslib.TreeEval.Reader.stateBudget` of its states, and the step machine
simulating it is tidy.

## Main definitions

* `Cslib.TreeEval.Reader.stateBudget`: the space budget of a state.

## Main results

* `Cslib.TreeEval.Reader.tidy_machine`: the step machine simulating the read machine is tidy.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, which the machine runs.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableTidilyInSpace Iter

/-- The tuple with the bit `false`, as an input of a step. -/
theorem pairFalse_inSpace :
    ComputableInSpace (fun x : Tuple => (x, false)) encTuple encStepInT
      fun x => stepBudget (x, false) := by
  have this : ComputableTidilyInSpace (fun x : Tuple => (x, false)) encTuple encStepInT fun x =>
      stepBudget (x, false) :=
    ReadMachine.pairFalse_inSpace fun x => by simp only [stepBudget, encStepInT]; omega
  simpa only [computableInSpace_iff_computableTidilyInSpace] using this

/-- A function of the tuple with the bit `false` within the budget of the step. -/
private theorem onTuple {β : Type} {encB : β ↪ List Bool} {f : Tuple × Bool → β}
    (h : ComputableTidilyInSpace f encStepInT encB stepBudget) :
    ComputableTidilyInSpace (fun x : Tuple => f (x, false)) encTuple encB
      fun x => stepBudget (x, false) :=
  ReadMachine.comp_pairFalse_inSpace (fun x => by simp only [stepBudget, encStepInT]; omega) h

/-- **The halting test** on tuples. -/
private theorem haltT_inSpace :
    ComputableTidilyInSpace haltT encTuple encBool fun x => stepBudget (x, false) :=
  onTuple (budget_finite (encC := encBool) (fun t : Fin 7 => decide (t = 6)) tag_inSpace.tidy)

/-- The offset of the node at the path of a stack. -/
private theorem offsetT_inSpace {st : Tuple × Bool → List Frame}
    (hst : ComputableTidilyInSpace st encStepInT (encList encFrame) stepBudget) :
    ComputableTidilyInSpace (fun y => offsetT y.1 (st y)) encStepInT encNat stepBudget := by
  have hdirs := budget_comp dirs_inSpace.tidy hst (.const_mul 64 ((length_le hst).add (.const 1 _)))
  have harg := budget_prod (budget_prod ell_inSpace.tidy height_inSpace.tidy) hdirs
  have hpo := budget_comp pathOffset_inSpace.tidy harg (.const_mul (2 ^ 30)
    (((ell_le_stepBudget.add height_le_stepBudget).add (length_le harg)).add (.const 1 _)))
  have h₂ :=
    (succ_inSpace (succ_inSpace (.of_tidy (budget_comp_lin natAdd linear_succ
      (budget_prod ell_inSpace.tidy height_inSpace.tidy))))).tidy
  refine (budget_comp_lin natAdd linear_succ (budget_prod h₂ hpo)).of_enc_eq fun y => ?_
  simp only [offsetT, path_eq_reverse, foldl_cons_dir, List.append_nil]

/-- **The address** on tuples. -/
private theorem addrT_inSpace :
    ComputableTidilyInSpace addrT encTuple (encOption encNat) fun x => stepBudget (x, false) := by
  have hsome {n : Tuple × Bool → ℕ} (hn : ComputableTidilyInSpace n encStepInT encNat stepBudget) :
      ComputableTidilyInSpace (fun y => some (n y)) encStepInT (encOption encNat) stepBudget :=
    budget_comp_linear (of_inO (ComputableTidilyInDegree.optionSome (enc₁ := encNat)).inO_one) hn
  have ht (k : Fin 7) :=
    budget_finite (encC := encBool) (fun t : Fin 7 => decide (t = k)) tag_inSpace.tidy
  have hadd {a b : Tuple × Bool → ℕ} (ha : ComputableTidilyInSpace a encStepInT encNat stepBudget)
      (hb : ComputableTidilyInSpace b encStepInT encNat stepBudget) :
      ComputableTidilyInSpace (fun y => a y + b y) encStepInT encNat stepBudget :=
    budget_comp_lin natAdd linear_succ (budget_prod ha hb)
  have h := budget_ite (ht 0) (hsome n₁_inSpace.tidy)
    (budget_ite (ht 1) (hsome (hadd (succ_inSpace ell_inSpace).tidy n₁_inSpace.tidy))
    (budget_ite (ht 4) (hsome (hadd (offsetT_inSpace stack_inSpace.tidy) n₁_inSpace.tidy))
      (budget_ite (ht 5) (hsome (hadd (offsetT_inSpace rest_inSpace.tidy) n₁_inSpace.tidy))
        (budget_const (encB := encOption encNat) none len_le_stepBudget))))
  refine (onTuple h).of_enc_eq fun x => ?_
  simp only [addrT, decide_eq_true_eq]

/-! ### On states -/

/-- **The space budget of a state.** -/
def stateBudget (s : State) : ℕ := stepBudget (s.toTuple, false)

private theorem stepBudget_bool (x : Tuple) (b : Bool) : stepBudget (x, b) = stepBudget
    (x, false) := by
  simp [stepBudget, encBool_apply]

private theorem halt_inSpace : ComputableTidilyInSpace machine.halt encState encBool stateBudget :=
  (haltT_inSpace.of_encIn_eq State.toTuple fun _ => rfl).of_enc_eq fun s => by
    rw [haltT_toTuple]

private theorem addr_inSpace : ComputableTidilyInSpace machine.addr encState (encOption encNat)
    stateBudget :=
  (addrT_inSpace.of_encIn_eq State.toTuple fun _ => rfl).of_enc_eq fun s => by
    rw [addrT_toTuple]; rfl

private theorem step_inSpace :
    ComputableTidilyInSpace (fun p : State × Bool => machine.step p.1 p.2)
      (encPair encState encBool) (encPair encState encBits) fun p => stateBudget p.1 := by
  have h := stepT_inSpace.tidy.of_encIn_eq (fun p : State × Bool => (p.1.toTuple, p.2)) fun p => by
    rw [encPair_apply, encPair_apply, encState_apply]
  refine (h.mono_le fun p => ?_).of_enc_eq fun p => ?_
  · simp only [stateBudget, stepBudget_bool]; exact le_rfl
  · rw [stepT_toTuple, encPair_apply, encPair_apply, encState_apply]

/-- **The step machine simulating the read machine is tidy**, within the space of its states
together with the position of its head. -/
theorem tidy_machine : ∃ T, machine.toStepMachine.Tidy (encPair encState encNat)
    (ReadMachine.stateT encState T stateBudget) (ReadMachine.stateS encState stateBudget) := by
  obtain ⟨T₁, h₁⟩ := halt_inSpace
  obtain ⟨T₂, h₂⟩ := addr_inSpace
  obtain ⟨T₃, h₃⟩ := step_inSpace
  let T : State → ℕ := fun s => T₁ s + T₂ s + T₃ (s, false) + T₃ (s, true)
  exact ⟨T, ReadMachine.tidy_toStepMachine (h₁.mono_le (fun s => by simp only [T]; omega)
    fun _ => le_rfl) (h₂.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₃.mono_le (fun p => by rcases p with ⟨s, _ | _⟩ <;> simp only [T] <;> omega)
      fun _ => le_rfl)⟩

end Reader

end Cslib.TreeEval
