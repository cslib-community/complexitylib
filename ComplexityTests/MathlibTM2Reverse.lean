/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Machines.Turing.TM2.Reverse.Transfer

/-! Public clients for the reverse stack-machine compiler. -/

namespace ComplexityTests.MathlibTM2Reverse

open Turing Turing.MultiTapeTM

private def stopAction : Action 0 Bool Unit := ⟨.pos, Fin.elim0, some true, none⟩

private def stop : MultiTapeTM 0 Bool Unit := .ofTr () (fun _ _ _ => stopAction)

private theorem stop_run (input : List Bool) :
    stop.runFrom (stop.initCfg input) 1 = stopAction.apply (stop.initCfg input) := by
  rw [runFrom_one, step_of_state (by rfl)]
  simp only [stop, tr_ofTr]

private theorem stop_computes (input : List Bool) : stop.Computes input [true] :=
  ⟨1, by rw [stop_run]; rfl, by rw [stop_run]; rfl⟩

private theorem stop_computable :
    ComputableInTimeAndSpace (fun _ : List Bool => true) encBits encBool
      (fun _ => 1) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, stop, fun input => ⟨stop_computes input, ?_, ?_⟩⟩
  · apply runsInTime_iff_halted.mpr
    rw [stop_run]
    rfl
  · exact MultiTapeNTM.runsInSpace_zero_tapes _ _ _

-- An actual finite-state zero-work-tape machine yields a certificate over its original encodings.
example : ∃ h : TM2ComputableInPolyTime encBits encBool (fun _ : List Bool => true),
    ∀ stack, Finite (h.tm.Γ stack) :=
  stop_computable.exists_tm2ComputableInPolyTime (.const 1)

-- Initialization, cleanup and arbitrarily long padding all count the stored input and answer.
example (input : List Bool) (i : ℕ) :
    ToTM2.totalStackLength ((TM2.stepTotal (ToTM2.machine stop.q₀ stop.tr).m)^[i]
      (initList (ToTM2.machine stop.q₀ stop.tr) input)) ≤ input.length + 1 := by
  simpa using ToTM2.reachable_stack_bound stop (stop_computes input)
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ 0) i

private def workStep₁ : Action 1 Bool Bool :=
  ⟨.zero, fun _ => (some (some true), .zero), none, some true⟩

private def workStep₂ (w : Fin 1 → Option Bool) : Action 1 Bool Bool :=
  ⟨.zero, fun _ => (none, .pos), w 0, none⟩

private def workRoundtrip : MultiTapeTM 1 Bool Bool :=
  .ofTr false fun q _ w => match q with
    | false => workStep₁
    | true => workStep₂ w

private theorem workRoundtrip_run_one (input : List Bool) :
    workRoundtrip.runFrom (workRoundtrip.initCfg input) 1 =
      workStep₁.apply (workRoundtrip.initCfg input) := by
  rw [runFrom_one, step_of_state (by rfl)]
  simp only [workRoundtrip, tr_ofTr, q₀_ofTr]

private theorem workRoundtrip_run_two (input : List Bool) :
    workRoundtrip.runFrom (workRoundtrip.initCfg input) 2 =
      (workStep₂ (workStep₁.apply (workRoundtrip.initCfg input)).workTapeSymbols).apply
        (workStep₁.apply (workRoundtrip.initCfg input)) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, runFrom_succ, workRoundtrip_run_one,
    step_of_state (q := true) (by rfl)]
  simp only [workRoundtrip, tr_ofTr]

private theorem workRoundtrip_halted (input : List Bool) :
    (workRoundtrip.runFrom (workRoundtrip.initCfg input) 2).Halted := by
  rw [workRoundtrip_run_two]
  rfl

private theorem workRoundtrip_computes (input : List Bool) :
    workRoundtrip.Computes input [true] := by
  refine ⟨2, workRoundtrip_halted input, ?_⟩
  rw [workRoundtrip_run_two]
  simp [workStep₁, workStep₂, Action.apply, Cfg.workTapeSymbols]

private theorem workRoundtrip_runsInSpace (input : List Bool) :
    workRoundtrip.RunsInSpace input 3 :=
  workRoundtrip.runsInSpace_of_halted (workRoundtrip_halted input)
    (MultiTapeNTM.RunPath.space_le_mul_time_add_one _)

private theorem workRoundtrip_computable :
    ComputableInTimeAndSpace (fun _ : List Bool => true) encBits encBool
      (fun _ => 2) (fun _ => 3) := by
  refine ⟨1, Bool, inferInstance, workRoundtrip, fun input =>
    ⟨workRoundtrip_computes input, ?_, workRoundtrip_runsInSpace input⟩⟩
  exact runsInTime_iff_halted.mpr (workRoundtrip_halted input)

-- A 1-work-tape machine that writes, reads back and moves on its work tape transfers to TM2.
example : ∃ h : TM2ComputableInPolyTime encBits encBool (fun _ : List Bool => true),
    ∀ stack, Finite (h.tm.Γ stack) :=
  workRoundtrip_computable.exists_tm2ComputableInPolyTime (.const 2)

example : ∃ h : TM2Computable encBits encBool (fun _ : List Bool => true),
    (∀ stack, Finite (h.tm.Γ stack)) ∧
      ∃ space : List Bool → ℕ, PolyBounded List.length space ∧ h.StacksBounded space :=
  workRoundtrip_computable.exists_tm2Computable_bool (.const 3)

example (input : List Bool) (i : ℕ) :
    ToTM2.totalStackLength ((TM2.stepTotal (ToTM2.machine workRoundtrip.q₀ workRoundtrip.tr).m)^[i]
      (initList (ToTM2.machine workRoundtrip.q₀ workRoundtrip.tr) input)) ≤ input.length + 4 := by
  simpa [Nat.add_assoc] using ToTM2.reachable_stack_bound workRoundtrip
    (workRoundtrip_computes input) (workRoundtrip_runsInSpace input) i

example {α β : Type} {f : α → List Bool} {g : β → List Bool} {φ : α → β}
    (h : TM2Computable f g φ) (space : α → ℕ) :
    h.StacksBounded space ↔
      ∀ a i k,
        (((TM2.stepTotal h.tm.m)^[i]
          (initList h.tm (List.map h.inputAlphabet.symm (f a)))).stk k).length ≤ space a :=
  Iff.rfl

-- Existing polynomial-space functions and PSPACE languages transfer through the equivalences.
example : ∃ h : TM2Computable encBits encBits List.reverse,
    (∀ stack, Finite (h.tm.Γ stack)) ∧
      ∃ space : List Bool → ℕ, PolyBounded List.length space ∧ h.StacksBounded space :=
  computableInPolySpace_iff_tm2.mp (.of_polyTime .bitsReverse)

example : ∃ (f : List Bool → Bool) (h : TM2Computable (encList (encFinEnum Bool)) encBool f),
    (∀ stack, Finite (h.tm.Γ stack)) ∧
      (∃ space : List Bool → ℕ,
        PolyBounded (fun xs => (encList (encFinEnum Bool) xs).length) space ∧
          h.StacksBounded space) ∧
      (∀ xs, xs ∈ {xs : List Bool | xs.isEmpty = true} ↔ f xs = true) :=
  Cslib.Complexity.mem_PSPACE_iff_tm2.mp
    (Cslib.Complexity.mem_PSPACE_of_computableInPolySpace
      (.of_tidy (.of_polyTime (.listIsEmpty' (encFinEnum Bool)))) (fun _ => Iff.rfl))

end ComplexityTests.MathlibTM2Reverse
