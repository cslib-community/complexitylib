/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.MonotoneCircuitValue.Completeness

/-! Clients of monotone circuit value: both answers occur, dual rails preserve negation,
empty inputs are supported, and the generic writer has a concrete zero-chunk instance. -/

namespace ComplexityTests.MonotoneCircuitValue

open Cslib Cslib.Complexity Cslib.Circuits Turing Turing.MultiTapeTM

/-- A yes-instance with no gates. -/
example : ⟨1, Circuit.id Monotone.signature 1, fun _ => true⟩ ∈ MonotoneCircuitValue := rfl

/-- A no-instance with no gates. -/
example : ⟨1, Circuit.id Monotone.signature 1, fun _ => false⟩ ∉ MonotoneCircuitValue := by
  change false ≠ true
  decide

private def notGate : Circuit Boolean.signature 1 1 := Circuit.oneGate .not (fun _ => 0)

/-- The negative input rail implements negation without a monotone NOT gate. -/
example (b : Bool) :
    (Monotone.dualRail notGate).eval Monotone.interpretation
      (Monotone.railBitString fun _ => b) 0 = !b := by
  rw [Monotone.eval_dualRail]
  rfl

/-- The dual-rail translation has exactly two gates per original gate. -/
example (c : Circuit Boolean.signature 3 2) : (Monotone.dualRail c).size = 2 * c.size :=
  Monotone.size_dualRail c

/-- Empty original inputs still produce the true rail input. -/
example : Monotone.railBits [] = [true] := rfl

/-- A writer with no chunks or prefix copies the input unchanged. -/
private def copySpec : CircuitValue.WriterSpec where
  countUnit := []
  countEnd := []
  numChunks _ := 0
  chunk _ _ := []
  trailer _ := []
  copyBit b := [b]

example (w : List Bool) : copySpec.machine.run (frame w) (copySpec.rounds w.length) =
    ⟨(3, w.length, 0), w⟩ := by
  simpa [CircuitValue.WriterSpec.output, copySpec] using copySpec.run_machine w

/-- The generic writer's space hypotheses are realized by this concrete instance. -/
example : ComputableInLogSpace id (encFramed encBits) encBits := by
  have hin : (fun p => (CircuitValue.WriterSpec.encStepIn p).length) ≼
      fun p => CircuitValue.wBudget p.1 := .of_le_linear 2 0 fun p => by
    simp only [length_encPair, encBool_apply, CircuitValue.wBudget]
    simp only [encNat_apply, List.length_cons, List.length_nil, zero_add, add_zero,
      Order.add_one_le_iff]
    omega
  refine copySpec.computableInLogSpace (fun w => by
    simp [CircuitValue.WriterSpec.output, copySpec])
    (.of_tidy (ComputableTidilyInSpace.budget_const (encB := encNat) 0 hin))
    (.of_tidy (ComputableTidilyInSpace.budget_const (encB := encBits) [] hin))
    (.of_tidy (ComputableTidilyInSpace.budget_const (encB := encBits) [] hin)) ?_
  change PolynomiallyBounded fun _ : ℕ => 0
  fun_prop

example : LogSpaceReducible encCircuitValue encMonotoneCircuitValue
    CircuitValue MonotoneCircuitValue := MonotoneCircuitValue.circuitValue_logSpaceReducible

example : LogSpaceReducible encMonotoneCircuitValue encCircuitValue
    MonotoneCircuitValue CircuitValue := MonotoneCircuitValue.logSpaceReducible_circuitValue

example : PolyTimeComplete @P encMonotoneCircuitValue MonotoneCircuitValue :=
  MonotoneCircuitValue.logSpaceComplete.polyTimeComplete

example (h : MonotoneCircuitValue ∈ L encMonotoneCircuitValue) : P encBits = L encBits :=
  MonotoneCircuitValue.mem_L_iff_forall_P_eq_L.1 h encBits

/-! ### Axiom guards -/

/-- info: 'Cslib.Circuits.Monotone.eval_dualRail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.eval_dualRail

/-- info: 'Cslib.Circuits.Monotone.size_dualRail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.size_dualRail

/-- info: 'Cslib.Complexity.CircuitValue.WriterSpec.run_machine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CircuitValue.WriterSpec.run_machine

/-- info: 'Cslib.Complexity.CircuitValue.WriterSpec.computableInLogSpace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CircuitValue.WriterSpec.computableInLogSpace

/-- info: 'Cslib.Complexity.MonotoneCircuitValue.encMonotoneCircuitValue_dualTableauInstance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MonotoneCircuitValue.encMonotoneCircuitValue_dualTableauInstance

/-- info: 'Cslib.Complexity.MonotoneCircuitValue.computableInLogSpace_dualTableauInstance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MonotoneCircuitValue.computableInLogSpace_dualTableauInstance

/-- info: 'Cslib.Complexity.MonotoneCircuitValue.logSpaceReducible_of_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MonotoneCircuitValue.logSpaceReducible_of_mem_P

/-- info: 'Cslib.Complexity.MonotoneCircuitValue.logSpaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MonotoneCircuitValue.logSpaceComplete

/-- info: 'Cslib.Complexity.MonotoneCircuitValue.mem_L_iff_forall_P_eq_L' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MonotoneCircuitValue.mem_L_iff_forall_P_eq_L

end ComplexityTests.MonotoneCircuitValue
