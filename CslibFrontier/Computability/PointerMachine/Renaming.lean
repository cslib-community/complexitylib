/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Abstract
public import Mathlib.Logic.Equiv.Defs

/-!
# Renaming pointer-machine data

A permutation of the data which commutes with the primitives of the model commutes with
execution. Pointers, control and cost are unchanged.
-/

@[expose] public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- A permutation of the data which the primitives of the model cannot observe. -/
structure Model.Renaming (M : Model) where
  /-- The permutation. -/
  value : M.Value ≃ M.Value
  /-- The undefined value is fixed. -/
  undefined : value M.undefined = M.undefined
  /-- Operations commute with the permutation. -/
  op : ∀ o a b, M.evalOp o (value a) (value b) = value (M.evalOp o a b)
  /-- Predicates are invariant under the permutation. -/
  test : ∀ p a b, M.evalTest p (value a) (value b) = M.evalTest p a b

/-- Rename the data fields of a record. -/
def Record.rename (ρ : M.Renaming) (n : Record M L) : Record M L :=
  { n with data := ρ.value ∘ n.data }

/-- Rename all data of a state. -/
def State.rename (ρ : M.Renaming) (x : State M L) : State M L :=
  { x with data := ρ.value ∘ x.data, heap := x.heap.map (Record.rename ρ) }

/-- Instructions commute with renaming. -/
theorem Instr.effect_rename (ρ : M.Renaming) (i : Instr M L) (x : State M L) :
    i.effect (x.rename ρ) = (i.effect x).rename ρ := by
  have deref (r : Fin L.ptrRegs) : (x.rename ρ).deref r = (x.deref r).map (Record.rename ρ) := by
    simp only [State.deref, State.rename]
    cases x.ptr r <;> simp
  have modify (r : Fin L.ptrRegs) (g g' : Record M L → Record M L)
      (hg : ∀ n, g' (n.rename ρ) = (g n).rename ρ) :
      (x.rename ρ).modify r g' = (x.modify r g).rename ρ := by
    simp only [State.modify, State.rename]
    cases x.ptr r with
    | none => rfl
    | some a =>
      simp only [State.mk.injEq, true_and]
      apply List.ext_getElem? fun k => ?_
      simp only [List.getElem?_modify, List.getElem?_map]
      by_cases hk : a = k <;> cases x.heap[k]? <;> simp [hk, hg]
  cases i <;> simp only [Instr.effect]
  case loadPtr r f base => rw [deref]; cases x.deref base <;> rfl
  case loadData s f base =>
    rw [deref]
    cases x.deref base with
    | none => rfl
    | some n => simp [State.rename, State.setData, Record.rename, Function.comp_update]
  case storePtr f base r => exact modify base _ _ fun n => rfl
  case storeData f base s =>
    exact modify base _ _ fun n => by
      simp [State.rename, Record.rename, Function.comp_update]
  case op o s s₁ s₂ =>
    simp [State.rename, State.setData, Function.comp_update, ρ.op]
  case moveData s s' => simp [State.rename, State.setData, Function.comp_update]
  case create r =>
    simp [State.rename, State.setPtr, Record.rename, Record.blank, Function.comp_def, ρ.undefined]
  all_goals rfl

/-- Renaming does not change control flow. -/
theorem Instr.next_rename (ρ : M.Renaming) (i : Instr M L) (x : State M L) :
    i.next (x.rename ρ) = i.next x := by
  cases i <;> first | rfl | simp [Instr.next, State.rename, ρ.test]

/-- Every program step commutes with renaming. -/
theorem step_rename (ρ : M.Renaming) (code : List (Instr M L)) (x : State M L) :
    step code (x.rename ρ) = (step code x).map (State.rename ρ) := by
  have hpc : (x.rename ρ).pc = x.pc := rfl
  unfold step
  rw [hpc]
  cases code[x.pc]? with
  | none => rfl
  | some i => cases i <;> simp [Instr.effect_rename, Instr.next_rename] <;> rfl

/-- Renaming changes neither a run's control flow nor its instruction count. -/
theorem Runs.rename (ρ : M.Renaming) {code : List (Instr M L)}
    {x y : State M L} {n : ℕ} (h : Runs code x y n) :
    Runs code (x.rename ρ) (y.rename ρ) n := by
  induction h with
  | refl => exact .refl _
  | tail _ _ _ _ hxy ih =>
    apply Relation.RelatesInSteps.tail _ _ _ _ ih
    rw [step_rename, hxy]
    rfl

/-- Successful executions are invariant under renaming, with the same cost. -/
theorem Executes.rename (ρ : M.Renaming) {code : List (Instr M L)}
    {x y : State M L} {n : ℕ} (h : Executes code x y n) :
    Executes code (x.rename ρ) (y.rename ρ) n := by
  obtain ⟨m, hr, hh, hn⟩ := h
  exact ⟨m, hr.rename ρ, hh, hn⟩

end Cslib.PointerMachine
