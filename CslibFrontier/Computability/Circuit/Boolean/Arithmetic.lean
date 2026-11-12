/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Computability.Circuit.Arithmetic.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.Synthesis

/-!
# Boolean circuits and arithmetic over the two-element field

Mathlib's `BooleanRing Bool` has addition XOR and multiplication AND. On that carrier,
arithmetic circuits and De Morgan Boolean circuits simulate each other with uniform gate
budgets three and four. The simulations preserve every output on every input, including
zero-input and zero-output circuits. Size counts operation nodes, including constants;
input and output wires are free. These are nonuniform existence and gate-size claims,
not runtime bounds for a compiler or formal polynomial identities.

This proves the two-element-field case of [Arora–Barak, web draft 2007-01-08,
Chapter 14, Exercise 1, printed p. 265/PDF p. 281][AroraBarak07]. The exercise for arbitrary
fixed finite fields additionally needs a representation of field elements by bits and is not
claimed here. Existing generic gate replacement supplies the circuit-level simulation.

## Main results

* `Cslib.Circuits.Boolean.arithmetic_simulates_boolean`: at most three arithmetic gates per
  Boolean gate.
* `Cslib.Circuits.Boolean.boolean_simulates_arithmetic`: at most four Boolean gates per
  arithmetic gate.
* `Cslib.Circuits.Boolean.exists_arithmetic_simulation`: all-output simulation with size factor
  three.
* `Cslib.Circuits.Boolean.exists_boolean_simulation`: all-output simulation with size factor
  four.
-/

public section

namespace Cslib.Circuits.Boolean

open Synthesis

private theorem arith_gate_synthesis (op : Op) :
    Synthesis (arithInterpretation Bool) (inputs (signature.Arity op)) {interpretation op} 3 := by
  cases op with
  | const c =>
    exact (Synthesis.arith_const (constant := id) c).mono
      (Set.Subset.refl _) (Set.Subset.refl _) (by decide)
  | not =>
    have hx : Synthesis (arithInterpretation Bool) (inputs 1) {fun x => x 0} 0 :=
      Synthesis.of_mem ⟨0, rfl⟩
    have hc : Synthesis (arithInterpretation Bool) (inputs 1) {fun _ => true} 1 :=
      Synthesis.arith_const (constant := id) true
    have h := hx.binary hc ArithOp.add
    have he : (fun x : Fin 1 → Bool => x 0 + true) = interpretation Op.not := by
      funext x
      simp [interpretation, Bool.add_eq_xor]
    simp only [arithInterpretation, arithInterpretationWith, Fin.val_zero, ↓reduceIte,
      Fin.val_one, Nat.one_ne_zero] at h
    rw [he] at h
    exact h.mono (Set.Subset.refl _) (Set.Subset.refl _) (by decide)
  | and =>
    have h : Synthesis (arithInterpretation Bool) (inputs 2) {fun x => x 0 * x 1} 1 :=
      Synthesis.arith_mul (constant := id) ⟨0, rfl⟩ ⟨1, rfl⟩
    exact h.mono (Set.Subset.refl _) (Set.Subset.refl _) (by decide)
  | or =>
    have hs : Synthesis (arithInterpretation Bool) (inputs 2) {fun x => x 0 + x 1} 1 :=
      Synthesis.arith_add (constant := id) ⟨0, rfl⟩ ⟨1, rfl⟩
    have hm : Synthesis (arithInterpretation Bool) (inputs 2) {fun x => x 0 * x 1} 1 :=
      Synthesis.arith_mul (constant := id) ⟨0, rfl⟩ ⟨1, rfl⟩
    have h := hs.binary hm ArithOp.add
    have he : (fun x : Fin 2 → Bool => (x 0 + x 1) + x 0 * x 1) = interpretation Op.or := by
      funext x
      change (x 0 + x 1) + x 0 * x 1 = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    simp only [arithInterpretation, arithInterpretationWith, Fin.val_zero, ↓reduceIte,
      Fin.val_one, Nat.one_ne_zero] at h
    rw [he] at h
    exact h

private theorem boolean_gate_synthesis (op : ArithOp Bool) :
    Synthesis interpretation (inputs ((arithSignature Bool).Arity op))
      {arithInterpretation Bool op} 4 := by
  cases op with
  | const c => exact (Synthesis.const c).mono (Set.Subset.refl _) (Set.Subset.refl _) (by decide)
  | mul =>
    have hx : Synthesis interpretation (inputs 2) {fun x => x 0} 0 :=
      Synthesis.of_mem ⟨0, rfl⟩
    have hy : Synthesis interpretation (inputs 2) {fun x => x 1} 0 :=
      Synthesis.of_mem ⟨1, rfl⟩
    exact (hx.and hy).mono (Set.Subset.refl _) (Set.Subset.refl _) (by decide)
  | add =>
    have hx : Synthesis interpretation (inputs 2) {fun x => x 0} 0 :=
      Synthesis.of_mem ⟨0, rfl⟩
    have hy : Synthesis interpretation (inputs 2) {fun x => x 1} 0 :=
      Synthesis.of_mem ⟨1, rfl⟩
    exact hx.xor hy

/-- Each De Morgan gate is computed by at most three gates over the two-element arithmetic
basis. NOT is `x + 1`; OR is `x + y + x * y`. -/
theorem arithmetic_simulates_boolean :
    (arithInterpretation Bool).SimulatesWithCost interpretation (fun _ => 3) :=
  fun op => (arith_gate_synthesis op).exists_circuit

/-- Each arithmetic gate over the two-element field is computed by at most four De Morgan
gates. Addition uses the existing four-gate XOR synthesis. -/
theorem boolean_simulates_arithmetic :
    interpretation.SimulatesWithCost (arithInterpretation Bool) (fun _ => 4) :=
  fun op => (boolean_gate_synthesis op).exists_circuit

/-- A Boolean circuit has an equivalent two-element arithmetic circuit with at most three
times its number of gates. Every designated output is preserved. -/
theorem exists_arithmetic_simulation {n m : ℕ} (c : Circuit signature n m) :
    ∃ d : Circuit (arithSignature Bool) n m,
      d.eval (arithInterpretation Bool) = c.eval interpretation ∧ d.size ≤ 3 * c.size :=
  c.exists_simulation_le arithmetic_simulates_boolean

/-- A two-element arithmetic circuit has an equivalent Boolean circuit with at most four
times its number of gates. Every designated output is preserved. -/
theorem exists_boolean_simulation {n m : ℕ} (c : Circuit (arithSignature Bool) n m) :
    ∃ d : Circuit signature n m,
      d.eval interpretation = c.eval (arithInterpretation Bool) ∧ d.size ≤ 4 * c.size :=
  c.exists_simulation_le boolean_simulates_arithmetic

end Cslib.Circuits.Boolean
