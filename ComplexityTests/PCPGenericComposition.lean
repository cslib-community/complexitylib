/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Composition

/-! Independent direct-tester and compatibility clients for generic composition. -/

namespace ComplexityTests.GenericComposition

open Cslib Cslib.PCP

-- An independent tester reads the two input symbols directly; no auxiliary proof is needed.
-- Its symbol alphabet need not be finite, and all binary constraints are supported.
private def directTester (α : Type) : AssignmentTester α Unit Empty Unit (Fin 2) α where
  test C := {
    query _ i := .inl (i, ())
    Accepts _ a := C (a 0) (a 1) }
  encode a _ := a
  auxiliary _ _ p := p.elim

private theorem direct_complete (α : Type) : (directTester α).IsComplete :=
  fun h _ => h

private theorem direct_sound (α : Type) :
    (directTester α).Sound (fun table => table ()) 1 := by
  intro C π h
  simp [directTester, LocalTest.acceptProb, LocalTest.Passes, h]

private def rejecting : ConstraintGraph Unit Unit Bool :=
  ⟨fun _ => (), fun _ => (), fun _ _ _ => False⟩

private def emptyGraph : ConstraintGraph Unit Empty Bool :=
  ⟨Empty.elim, Empty.elim, fun e _ _ => e.elim⟩

example : ¬ rejecting.Satisfiable := by
  rintro ⟨σ, hσ⟩
  exact hσ ()

example :
    ((directTester Bool).compose rejecting).unsatVal ≤ rejecting.unsatVal ∧
      (((directTester Bool).compose rejecting).Satisfiable ↔ rejecting.Satisfiable) :=
  ⟨AssignmentTester.unsatVal_compose_le (direct_complete Bool) rejecting,
    AssignmentTester.satisfiable_compose_iff (direct_complete Bool) (direct_sound Bool)
      (by norm_num) rejecting⟩

example : 1 / 2 ≤ ((directTester Bool).compose rejecting).unsatVal := by
  have h := AssignmentTester.le_unsatVal_compose (direct_sound Bool) (by norm_num) rejecting
  have hreject : rejecting.unsatVal = 1 := by
    apply le_antisymm rejecting.unsatVal_le_one
    apply rejecting.le_unsatVal_iff.mpr
    intro σ
    simp [ConstraintGraph.unsatFrac, ConstraintGraph.unsatEdges, ConstraintGraph.Satisfies,
      rejecting]
  simpa [hreject] using h

example :
    ((directTester Bool).compose emptyGraph).unsatVal = 0 :=
  ConstraintGraph.unsatVal_of_isEmpty _

-- The old concrete graph definitions remain definitionally identical to the generic construction.
example :
    HadamardTester.assignmentTester.compose rejecting = rejecting.compose ∧
      HadamardTester.assignmentTester.composeProof rejecting (fun _ => false) =
        rejecting.composeProof (fun _ => false) ∧
      AssignmentTester.decodeLabelling ConstraintGraph.decodeLabel
        (fun _ : ConstraintGraph.ComposePos Unit Unit Bool => false) =
        ConstraintGraph.decodeLabelling (V := Unit) (E := Unit) (α := Bool) (fun _ => false) :=
  ⟨rfl, rfl, rfl⟩

-- A zero rejection bound remains a valid weighted statement, but not a positive-gap contract.
example (A : AssignmentTester.ComposePos Unit Unit Unit Empty ⊕ Unit × Unit →
      Bool × (Fin 2 → Bool))
    (hsound : (directTester Bool).Sound (fun table => table ()) 0) :
    0 ≤ (2 : ℝ) * ((directTester Bool).compose rejecting).unsatFrac A := by
  simpa using AssignmentTester.mul_unsatFrac_decodeLabelling_le hsound rejecting A

-- An honest auxiliary proof may depend on the constraint, not just its two labels.
open Classical in
private noncomputable def constraintAware : AssignmentTester Bool Unit Unit Unit (Fin 3) Bool where
  test C := {
    query _ := ![.inl (0, ()), .inl (1, ()), .inr ()]
    Accepts _ a := C (a 0) (a 1) ∧ a 2 = true }
  encode a _ := a
  auxiliary C σ _ := decide (C (σ 0) (σ 1))

example : constraintAware.IsComplete := by
  intro C σ h r
  simp [constraintAware, AssignmentTester.honestProof, LocalTest.Passes, h]

example : constraintAware.Sound (fun table => table ()) 1 := by
  intro C π h
  simp [constraintAware, LocalTest.acceptProb, LocalTest.Passes, h]

example : constraintAware.auxiliary (fun _ _ => True) (fun _ => false) () = true := by
  simp [constraintAware]

example : constraintAware.auxiliary (fun _ _ => False) (fun _ => false) () = false := by
  simp [constraintAware]

-- Input labels and proof symbols can be different alphabets.
private def optionalTester : AssignmentTester Bool Unit Empty Unit (Fin 2) (Option Bool) where
  test C := {
    query _ i := .inl (i, ())
    Accepts _ a := C ((a 0).getD false) ((a 1).getD false) }
  encode a _ := some a
  auxiliary _ _ p := p.elim

example : optionalTester.IsComplete := fun h _ => h

example : optionalTester.Sound (fun table => (table ()).getD false) 1 := by
  intro C π h
  simp [optionalTester, LocalTest.acceptProb, LocalTest.Passes, h]

end ComplexityTests.GenericComposition
