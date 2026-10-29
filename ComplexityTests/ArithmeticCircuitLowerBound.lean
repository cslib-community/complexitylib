/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.CircuitLowerBound

/-!
# Constant-depth circuits and the superpolynomial lower bound over any field

The circuit `(x₀ + x₁) (x₀ - x₁)`, with three gates, is simple, has product-depth one and computes
`x₀ ^ 2 - x₁ ^ 2`; its unfolded formula has `8` nodes, within the bound `6 ^ 3`. The circuit
`x₀ x₀`, one product gate reading the same input twice, is not simple. Flattening the formula
`1 (1 x₀ + 1 x₁) + 1 x₀` merges the two occurrences of `x₀` into one sum gate of fan-in two, of
three nodes.
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

/-- Its output unfolds to the formula `(x₀ + x₁) (x₀ - x₁)`. -/
private theorem toFormula_diffSq :
    diffSq.toFormula 0 =
      SPFormula.mul ![SPFormula.add ![1, 1] ![.input 0, .input 1],
        SPFormula.add ![1, -1] ![.input 0, .input 1]] := by
  simp only [diffSq, Circuit.toFormula, Program.wireFormula_gate]
  rw [show (2 : Fin 3) = Fin.last 2 from rfl, diffSqProgram, Program.gateFormula_gate_last]
  congr 1
  funext a
  fin_cases a
  · rw [show (0 : Fin 2) = (Fin.last 0).castSucc from rfl]
    simp only [Fin.zero_eta, Matrix.cons_val_zero, Program.wireFormula_gate,
      Program.gateFormula_gate_castSucc, Program.gateFormula_gate_last]
    congr 1
    funext b
    fin_cases b <;> rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Program.wireFormula_gate]
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, Program.gateFormula_gate_last]
    congr 1
    funext b
    fin_cases b <;> rfl

/-- Flattening a sum of two distinct inputs with nonzero edge constants keeps its three nodes. -/
private theorem nodeCount_flatten_add_inputs {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (SPFormula.flatten (SPFormula.add ![a, b] ![.input 0, .input 1] : SPFormula ℚ 2)).nodeCount =
      3 := by
  classical
  have hne : (.input 0 : SPFormula ℚ 2) ≠ .input 1 := by
    simp only [ne_eq, Formula.input.injEq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      not_false_eq_true]
  rw [SPFormula.flatten, SPFormula.nodeCount_ofFinsupp]
  simp only [SPFormula.linComb_add, SPFormula.linComb_input, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  rw [Finsupp.support_single_add_single hne ha hb, Finset.sum_pair hne,
    Formula.nodeCount_input, Formula.nodeCount_input]

/-- Its unfolded formula is `(x₀ + x₁) (x₀ - x₁)` with its two sums flattened, of `8` nodes, well
within the bound `6 ^ 3` of `SPCircuit.nodeCount_toSPFormula_le`. -/
example : diffSq.toSPFormula.nodeCount = 8 := by
  classical
  rw [SPCircuit.toSPFormula, toFormula_diffSq, SPFormula.flatten, SPFormula.linComb_mul,
    SPFormula.nodeCount_ofFinsupp, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, SPFormula.mul, Formula.nodeCount_gate, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [nodeCount_flatten_add_inputs one_ne_zero one_ne_zero,
    nodeCount_flatten_add_inputs one_ne_zero (neg_ne_zero.mpr one_ne_zero)]

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
private theorem linComb_nested :
    SPFormula.linComb nested = Finsupp.single (.input 0) 2 + Finsupp.single (.input 1) 1 := by
  simp only [nested, SPFormula.linComb_add, SPFormula.linComb_input, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
  rw [add_right_comm, ← Finsupp.single_add]
  norm_num

/-- Flattening it gives one sum gate over `x₀` and `x₁`: three nodes instead of five. -/
example : (SPFormula.flatten nested).nodeCount = 3 := by
  classical
  have hne : (.input 0 : SPFormula ℚ 2) ≠ .input 1 := by
    simp only [ne_eq, Formula.input.injEq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      not_false_eq_true]
  rw [SPFormula.flatten, linComb_nested, SPFormula.nodeCount_ofFinsupp,
    Finsupp.support_single_add_single hne two_ne_zero one_ne_zero, Finset.sum_pair hne,
    Formula.nodeCount_input, Formula.nodeCount_input]

end ComplexityTests.ArithmeticCircuitLowerBound
