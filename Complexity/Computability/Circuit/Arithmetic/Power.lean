/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic
public import Complexity.Computability.Circuit.Pi
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Data.Nat.BinaryRec
import Complexity.Computability.Circuit.Simulation
import Mathlib.Data.Nat.Log

/-!
# Binary-power arithmetic circuits

Binary powering computes each intermediate power once and shares it between the two inputs
of a squaring gate. Every further binary digit adds one squaring and, for a one bit, a
multiplication by the retained original input. A positive exponent `e` uses at most
`2 * Nat.log2 e` gates, all multiplications. Exponent zero uses a single named constant gate;
exponent one uses only the input wire.

The constant symbol denoting one is an explicit parameter. Its interpretation is required to
equal one only in the correctness theorem. Arbitrary weighted costs, including constant costs,
are accounted for exactly. These are circuit-size results, not uniform TM-time certificates
for circuit generation or evaluation.

## Main definitions

* `Cslib.Circuits.Circuit.binaryPowerStep`: one binary-powering step on a single-output circuit.
* `Cslib.Circuits.binaryPowerCircuit`: the shared binary-power circuit.
* `Cslib.Circuits.binaryMultiplicationCount`: its exact multiplication count.

## Main results

* `Cslib.Circuits.eval_binaryPowerCircuit`: correctness over a monoid with addition.
* `Cslib.Circuits.cost_program_binaryPowerCircuit`: exact cost for any operation weights.
* `Cslib.Circuits.size_binaryPowerCircuit_le`: logarithmic gate count for positive exponents.

## References

* Ported from Basis/Arithmetic/Power.lean in [S. Schlesinger, *Algebraic circuit
  formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {C : Type v} {R : Type u}

/-- Add a binary digit to a shared power: square, then multiply by the original input for
a one bit. -/
def Circuit.binaryPowerStep (bit : Bool) (c : Circuit (arithSignature C) 1 1) :
    Circuit (arithSignature C) 1 1 :=
  let square := (Circuit.oneGate (σ := arithSignature C) .mul (fun _ => 0)).comp c
  if bit then
    (Circuit.oneGate (σ := arithSignature C) .mul (fun i => i)).comp
      (square.append (Circuit.id (arithSignature C) 1))
  else square

private theorem eval_binaryPowerStep [Add R] [Mul R] (constant : C → R) (bit : Bool)
    (c : Circuit (arithSignature C) 1 1) (x : Fin 1 → R) :
    (Circuit.binaryPowerStep bit c).eval (arithInterpretationWith C constant) x 0 =
      if bit then (c.eval (arithInterpretationWith C constant) x 0 *
        c.eval (arithInterpretationWith C constant) x 0) * x 0
      else c.eval (arithInterpretationWith C constant) x 0 *
        c.eval (arithInterpretationWith C constant) x 0 := by
  cases bit <;> simp [Circuit.binaryPowerStep, Circuit.eval_comp, Circuit.eval_oneGate,
    arithInterpretationWith, Fin.append, Fin.addCases]

private theorem cost_program_binaryPowerStep (bit : Bool) (c : Circuit (arithSignature C) 1 1)
    (cost : ArithOp C → ℕ) : (Circuit.binaryPowerStep bit c).program.cost cost =
      c.program.cost cost + (1 + bit.toNat) * cost .mul := by
  cases bit <;> unfold Circuit.binaryPowerStep
  · rw [ite_eq_right (by decide), Circuit.cost_program_comp, Circuit.cost_program_oneGate]
    simp
  · rw [ite_eq_left rfl, Circuit.cost_program_comp, Circuit.cost_program_append,
      Circuit.cost_program_comp, Circuit.cost_program_oneGate, Circuit.cost_program_oneGate]
    simp [Circuit.id, Nat.two_mul, Nat.add_assoc]

/-- Binary powering with a specified constant symbol for one. -/
def binaryPowerCircuit (one : C) (e : ℕ) : Circuit (arithSignature C) 1 1 :=
  Nat.binaryRecFromOne
    (Circuit.oneGate (σ := arithSignature C) (.const one) Fin.elim0)
    (Circuit.id (arithSignature C) 1) (fun bit _ _ => Circuit.binaryPowerStep bit) e

/-- Exact multiplication count of binary powering: one squaring per nonleading bit and
one further multiplication per nonleading one bit. -/
def binaryMultiplicationCount (e : ℕ) : ℕ :=
  Nat.binaryRecFromOne 0 0 (fun bit _ _ count => count + 1 + bit.toNat) e

/-- For exponent `0`, `binaryPowerCircuit` is a single constant gate outputting `one`. -/
@[simp] theorem binaryPowerCircuit_zero (one : C) : binaryPowerCircuit one 0 =
    Circuit.oneGate (σ := arithSignature C) (.const one) Fin.elim0 := by
  simp [binaryPowerCircuit]

/-- For exponent `1`, `binaryPowerCircuit` is the single-input identity circuit. -/
@[simp] theorem binaryPowerCircuit_one (one : C) :
    binaryPowerCircuit one 1 = Circuit.id (arithSignature C) 1 := by
  simp [binaryPowerCircuit]

private theorem binaryPowerCircuit_bit (one : C) (bit : Bool) (e : ℕ) (he : e ≠ 0) :
    binaryPowerCircuit one (Nat.bit bit e) =
      Circuit.binaryPowerStep bit (binaryPowerCircuit one e) := by
  unfold binaryPowerCircuit
  rw [Nat.binaryRecFromOne_eq bit e he]

/-- Binary powering for exponent `0` uses `0` multiplications. -/
@[simp] theorem binaryMultiplicationCount_zero : binaryMultiplicationCount 0 = 0 := by
  simp [binaryMultiplicationCount]

/-- Binary powering for exponent `1` uses `0` multiplications. -/
@[simp] theorem binaryMultiplicationCount_one : binaryMultiplicationCount 1 = 0 := by
  simp [binaryMultiplicationCount]

private theorem binaryMultiplicationCount_bit (bit : Bool) (e : ℕ) (he : e ≠ 0) :
    binaryMultiplicationCount (Nat.bit bit e) = binaryMultiplicationCount e + 1 + bit.toNat :=
  Nat.binaryRecFromOne_eq bit e he

/-- The circuit computes the natural power, including exponents zero and one. -/
theorem eval_binaryPowerCircuit [Add R] [Monoid R] (one : C) (constant : C → R)
    (hone : constant one = 1) (e : ℕ) (x : Fin 1 → R) :
    (binaryPowerCircuit one e).eval (arithInterpretationWith C constant) x 0 = x 0 ^ e := by
  induction e using Nat.binaryRecFromOne with
  | zero => simp [Circuit.eval_oneGate, arithInterpretationWith, hone]
  | one => simp
  | bit bit e he ih =>
    rw [binaryPowerCircuit_bit one bit e he, eval_binaryPowerStep, ih]
    cases bit <;> simp [Nat.bit, two_mul, pow_add]

/-- Exact weighted cost, charging the constant gate for exponent zero. -/
theorem cost_program_binaryPowerCircuit (one : C) (e : ℕ) (cost : ArithOp C → ℕ) :
    (binaryPowerCircuit one e).program.cost cost =
      if e = 0 then cost (.const one) else binaryMultiplicationCount e * cost .mul := by
  induction e using Nat.binaryRecFromOne with
  | zero => rw [binaryPowerCircuit_zero, Circuit.cost_program_oneGate]; rfl
  | one => rw [binaryPowerCircuit_one, Circuit.id, Circuit.cost_program_wiring]; simp
  | bit bit e he ih =>
    rw [binaryPowerCircuit_bit one bit e he, cost_program_binaryPowerStep, ih,
      binaryMultiplicationCount_bit bit e he]
    cases bit <;> simp [Nat.bit, he, Nat.add_mul, Nat.add_assoc]

/-- Every gate at a positive exponent is a multiplication; exponent zero has one constant. -/
@[simp] theorem size_binaryPowerCircuit (one : C) (e : ℕ) :
    (binaryPowerCircuit one e).size = if e = 0 then 1 else binaryMultiplicationCount e := by
  simpa using cost_program_binaryPowerCircuit one e (fun _ => 1)

/-- The multiplication count includes multiplication by scalars. -/
theorem mulCost_binaryPowerCircuit (one : C) (e : ℕ) :
    (binaryPowerCircuit one e).program.cost ArithOp.mulCost = binaryMultiplicationCount e := by
  rw [cost_program_binaryPowerCircuit]
  split_ifs with he <;> simp [he, ArithOp.mulCost]

/-- Binary powering uses at most twice the base-two logarithm many multiplications. -/
theorem binaryMultiplicationCount_le_two_mul_log2 (e : ℕ) :
    binaryMultiplicationCount e ≤ 2 * Nat.log2 e := by
  induction e using Nat.binaryRecFromOne with
  | zero => simp
  | one => simp
  | bit bit e he ih =>
    rw [binaryMultiplicationCount_bit bit e he, Nat.log2_eq_log_two, Nat.log_two_bit he]
    rw [Nat.log2_eq_log_two] at ih
    cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> lia

/-- A positive exponent needs at most `2 * log₂ e` gates, all multiplications. -/
theorem size_binaryPowerCircuit_le (one : C) {e : ℕ} (he : 0 < e) :
    (binaryPowerCircuit one e).size ≤ 2 * Nat.log2 e := by
  rw [size_binaryPowerCircuit, ite_eq_right (Nat.ne_of_gt he)]
  exact binaryMultiplicationCount_le_two_mul_log2 e

end Cslib.Circuits
