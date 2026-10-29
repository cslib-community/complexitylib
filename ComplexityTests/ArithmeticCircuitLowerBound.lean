/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.CircuitLowerBound

/-!
# Constant-depth circuits and the superpolynomial lower bound over any field

The circuit `(x₀ + x₁) (x₀ - x₁)`, with three gates, is simple, has product-depth one and computes
`x₀ ^ 2 - x₁ ^ 2`; its unfolded formula computes the same polynomial and has at most `6 ^ 3`
nodes. The circuit `x₀ x₀`, one product gate reading the same input twice, is not simple.
Flattening the formula `1 (1 x₀ + 1 x₁) + 1 x₀` merges the two occurrences of `x₀` into one sum
gate of fan-in two. The superpolynomial lower bound is instantiated at `Δ = 3` and `c = 10` over
`ℚ` and over `ZMod 2`.
-/

namespace ComplexityTests.ArithmeticCircuitLowerBound

open Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-- The program of `(x₀ + x₁) (x₀ - x₁)`: two sum gates and a product gate reading both. -/
private def diffSqProgram : Program (sigmaPiSignature ℚ) 2 3 :=
  ((Program.empty.gate ⟨SigmaPiOp.add 2 ![1, 1], ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨SigmaPiOp.add 2 ![1, -1], ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨SigmaPiOp.mul 2, ![Wire.gate 0, Wire.gate 1]⟩

/-- The circuit `(x₀ + x₁) (x₀ - x₁)`. -/
private def diffSq : SPCircuit ℚ 2 :=
  ⟨diffSqProgram, fun _ => Wire.gate 2⟩

example : diffSq.size = 3 :=
  rfl

/-- Its product gate reads two distinct wires. -/
theorem diffSq_isSimple : diffSq.IsSimple := by
  intro k m hk
  fin_cases k
  · have h : (diffSq.program.lines ⟨0, by decide⟩).op = SigmaPiOp.add 2 ![1, 1] := rfl
    cases h.symm.trans hk
  · have h : (diffSq.program.lines ⟨1, by decide⟩).op = SigmaPiOp.add 2 ![1, -1] := rfl
    cases h.symm.trans hk
  · intro a b hab
    revert hab
    fin_cases a <;> fin_cases b <;> decide

example : diffSq.productDepth = 1 := by
  rfl

/-- It computes `x₀ ^ 2 - x₁ ^ 2`. -/
example : diffSq.polynomial = X 0 ^ 2 - X 1 ^ 2 := by
  rw [← SPCircuit.polynomial_toFormula]
  simp only [diffSq, Circuit.toFormula, Program.wireFormula_gate]
  rw [show (2 : Fin 3) = Fin.last 2 from rfl, diffSqProgram, Program.gateFormula_gate_last]
  simp only [SPFormula.polynomial_mul, Fin.prod_univ_two, Matrix.cons_val_zero,
    Program.wireFormula_gate, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, Program.gateFormula_gate_last,
    show (0 : Fin 2) = (Fin.last 0).castSucc from rfl, Program.gateFormula_gate_castSucc,
    Program.gateFormula_gate_last]
  simp [Fin.sum_univ_two]
  ring

example : diffSq.toSPFormula.polynomial = diffSq.polynomial :=
  SPCircuit.polynomial_toSPFormula _

example : diffSq.toSPFormula.nodeCount ≤ (3 + 2 + 1) ^ (2 * diffSq.productDepth + 1) :=
  SPCircuit.nodeCount_toSPFormula_le diffSq_isSimple

/-- The circuit `x₀ x₀`: one product gate reading the same input twice computes `x₀ ^ 2`. -/
private def square : SPCircuit ℚ 1 :=
  ⟨(Program.empty.gate ⟨SigmaPiOp.mul 2, ![Wire.input 0, Wire.input 0]⟩ :
    Program (sigmaPiSignature ℚ) 1 1), fun _ => Wire.gate 0⟩

/-- It is not simple. -/
example : ¬ square.IsSimple := fun h => by
  have h01 := h ⟨0, Nat.one_pos⟩ 2 rfl (a₁ := ⟨0, Nat.two_pos⟩) (a₂ := ⟨1, Nat.one_lt_two⟩) rfl
  exact absurd (Fin.val_eq_of_eq h01) (by decide)

/-! ### Flattening -/

/-- `1 (1 x₀ + 1 x₁) + 1 x₀`, nested sums with a repeated input. -/
private noncomputable def nested : SPFormula ℚ 2 :=
  .add ![1, 1] ![.add ![1, 1] ![.input 0, .input 1], .input 0]

/-- Its combination has coefficient `2` on `x₀`. -/
example : SPFormula.linComb nested = Finsupp.single (.input 0) 2 + Finsupp.single (.input 1) 1 := by
  simp only [nested, SPFormula.linComb_add, SPFormula.linComb_input, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
  rw [add_right_comm, ← Finsupp.single_add]
  norm_num

example : (SPFormula.flatten nested).polynomial = nested.polynomial :=
  SPFormula.polynomial_flatten _

example : (SPFormula.flatten nested).productDepth ≤ nested.productDepth :=
  SPFormula.productDepth_flatten_le _

/-! ### The lower bound -/

example : ∀ᶠ n in Filter.atTop, ∀ [NeZero n] {N : ℕ}
    (e : Fin N ≃ Fin (Nat.log 2 (Nat.log 2 n)) × Fin n × Fin n) (C : SPCircuit ℚ N),
    C.IsSimple → C.productDepth ≤ 3 →
    rename e C.polynomial = imm ℚ n (Nat.log 2 (Nat.log 2 n)) → n ^ 10 < C.size :=
  SPCircuit.eventually_pow_lt_size_of_imm ℚ 3 10

/-- Over a field of characteristic `2`, where the source's characteristic hypothesis fails for
every `d ≥ 2`. -/
example (F : Type*) [Field F] [CharP F 2] : ∀ᶠ n in Filter.atTop, ∀ [NeZero n] {N : ℕ}
    (e : Fin N ≃ Fin (Nat.log 2 (Nat.log 2 n)) × Fin n × Fin n) (C : SPCircuit F N),
    C.IsSimple → C.productDepth ≤ 3 →
    rename e C.polynomial = imm F n (Nat.log 2 (Nat.log 2 n)) → n ^ 10 < C.size :=
  SPCircuit.eventually_pow_lt_size_of_imm F 3 10

end ComplexityTests.ArithmeticCircuitLowerBound
