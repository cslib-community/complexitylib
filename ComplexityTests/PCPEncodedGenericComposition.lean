/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.GenericComposition
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime

/-! A non-Boolean assignment tester client for the shared executable composition engine. -/

namespace ComplexityTests.PCPEncodedGenericComposition

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

private def toyTester : AssignmentTester (Fin 2) Unit (Fin 0) Unit (Fin 2) (Fin 2) where
  test C := {
    query _ i := .inl (i, ())
    Accepts _ answers := C (answers 0) (answers 1)
  }
  encode a _ := a
  auxiliary _ _ p := Fin.elim0 p

private def toyImplementation : AssignmentTester.Implementation
    (Fin 2) Unit (Fin 0) Unit (Fin 2) (Fin 2) where
  query _ _ i := .inl (i, ())
  accepts constraint _ answers := constraint (answers 0) (answers 1)

private theorem toyRealizes : toyImplementation.Realizes toyTester := by
  constructor
  · intro constraint coins i
    rfl
  · intro constraint coins answers
    rfl

private def slotToFin : AssignmentTester.ComposeSlot Unit (Fin 0) Unit → Fin 2
  | .inl _ => 0
  | .inr (.inl p) => Fin.elim0 p
  | .inr (.inr _) => 1

private def finToSlot (i : Fin 2) : AssignmentTester.ComposeSlot Unit (Fin 0) Unit :=
  if i.val = 0 then .inl () else .inr (.inr ())

private def slotNumber : AssignmentTester.ComposeSlot Unit (Fin 0) Unit ≃ Fin 2 where
  toFun := slotToFin
  invFun := finToSlot
  left_inv := by
    intro x
    cases x with
    | inl u => simp [finToSlot, slotToFin]
    | inr x =>
      cases x with
      | inl p => exact Fin.elim0 p
      | inr u => simp [finToSlot, slotToFin]
  right_inv := by
    intro i
    fin_cases i <;> simp [finToSlot, slotToFin]

private def duplicateEdge : Edge (Fin 2 → Fin 2 → Bool) :=
  ⟨0, 1, fun _ _ => true⟩

private def duplicateGraph : Graph (Fin 2 → Fin 2 → Bool) :=
  ⟨2, [duplicateEdge, duplicateEdge]⟩

private def queries : List (Fin 2) := [0, 1]

example : toyImplementation.query (fun _ _ : Fin 2 => false) () 1 = .inl (1, ()) := rfl

example : toyImplementation.accepts (fun _ _ : Fin 2 => true) () (fun _ => 0) = true := by decide

example : toyImplementation.accepts (fun _ _ : Fin 2 => false) () (fun _ => 0) = false := by decide

-- Both stored edge occurrences survive composition, each with both query occurrences.
example : (toyImplementation.compose slotNumber [()] queries duplicateGraph).edges.length = 4 := by
  rw [AssignmentTester.Implementation.length_edges_compose]
  decide

example : (toyImplementation.compose slotNumber [] queries duplicateGraph).edges.length = 0 := by
  rw [AssignmentTester.Implementation.length_edges_compose]
  decide

-- Complete enumeration preserves the tester's value after table materialization.
example :
    (((toyImplementation.composeTabulated slotNumber [()] queries duplicateGraph).toGraph id)
      ).unsatVal = (toyTester.compose (duplicateGraph.toGraph id)).unsatVal := by
  apply AssignmentTester.Implementation.unsatVal_composeTabulated_eq
    (impl := toyImplementation) (T := toyTester) toyRealizes slotNumber [()] queries duplicateGraph
  · decide
  · decide
  · intro r
    simp
  · intro i
    fin_cases i <;> simp [queries]

example : ComputableInPolyTime
    (fun g : Graph (Fin 2 → Fin 2 → Bool) =>
      toyImplementation.composeTabulated slotNumber [()] queries g)
    (Graph.encoding (encPi (encPi encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by
  fun_prop

end ComplexityTests.PCPEncodedGenericComposition
