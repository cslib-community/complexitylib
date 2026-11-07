/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Adjugate
import Complexity.Computability.Circuit.Arithmetic.Gradient

/-!
# Reverse-mode differentiation of arithmetic circuits

Concrete runs of `Cslib.Circuits.Circuit.withGradient`, checked by kernel evaluation over `ℤ` and
the semiring `ℕ`: a shared input wire, a wire read twice by one gate, a non-unit seed, a circuit
with two outputs differentiated along either one, an output that is an input wire, and a constant
output. The exact size formula is checked on these circuits. At the polynomial level, the theorems
are instantiated for `x₀ * x₁ + x₀`, for the power sum `x₀ ^ 2 + x₁ ^ 2` (whose scaled gradient is
the identity power map) and for the generic `2 × 2` adjugate.
-/

namespace ComplexityTests.ArithmeticGradient

open Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-- `x₀ * x₁ + x₀`: the input `x₀` is read by two gates. -/
private def demo (K : Type*) : Circuit (arithSignature K) 2 1 where
  size := 2
  program := ((Program.empty : Program (arithSignature K) 2 0).gate
    ⟨.mul, ![.input 0, .input 1]⟩).gate ⟨.add, ![.gate 0, .input 0]⟩
  outputs := fun _ => .gate 1

/-- At `(3, 5)`: the value `18` and the gradient `(x₁ + 1, x₀) = (6, 3)`. -/
example : ((demo ℤ).withGradient 0 1 0).eval (arithInterpretation ℤ) ![3, 5] = ![18, 6, 3] := by
  decide +kernel

/-- Size `2 + 2 + 2 · 1 + 4 · 1 = 10`, as `Circuit.size_withGradient` predicts. -/
example : ((demo ℤ).withGradient 0 1 0).size = 10 := by decide +kernel

/-- The seed scales the gradient. -/
example : ((demo ℤ).withGradient 0 7 0).eval (arithInterpretation ℤ) ![3, 5] = ![18, 42, 21] := by
  decide +kernel

/-- `x₀ * x₀`: one gate reads the same wire twice and receives two contributions. -/
private def selfProduct : Circuit (arithSignature ℤ) 1 1 where
  size := 1
  program := (Program.empty : Program (arithSignature ℤ) 1 0).gate ⟨.mul, ![.input 0, .input 0]⟩
  outputs := fun _ => .gate 0

example : (selfProduct.withGradient 0 1 0).eval (arithInterpretation ℤ) ![7] = ![49, 14] := by
  decide +kernel

/-- Over the semiring `ℕ`, without subtraction. -/
example : ((Circuit.mk (Program.empty.gate ⟨.mul, ![.input 0, .input 0]⟩) fun _ => .gate 0 :
    Circuit (arithSignature ℕ) 1 1).withGradient 0 1 0).eval (arithInterpretation ℕ) ![7] =
    ![49, 14] := by
  decide +kernel

/-- Two outputs, `x₀ * x₁` and `x₀ * x₁ + x₀`, differentiated along either one. -/
private def twoOutputs : Circuit (arithSignature ℤ) 2 2 where
  size := 2
  program := (demo ℤ).program
  outputs := ![.gate 0, .gate 1]

example : (twoOutputs.withGradient 0 1 0).eval (arithInterpretation ℤ) ![3, 5] =
    ![15, 18, 5, 3] := by
  decide +kernel

example : (twoOutputs.withGradient 1 1 0).eval (arithInterpretation ℤ) ![3, 5] =
    ![15, 18, 6, 3] := by
  decide +kernel

/-- An output that is an input wire: its gradient is a unit vector, with no gates beyond the two
constants. -/
private def projection : Circuit (arithSignature ℤ) 2 1 where
  size := 0
  program := Program.empty
  outputs := fun _ => .input 1

example : (projection.withGradient 0 1 0).eval (arithInterpretation ℤ) ![3, 5] = ![5, 0, 1] := by
  decide +kernel

example : (projection.withGradient 0 1 0).size = 2 := by decide +kernel

/-- A constant output has zero gradient. -/
private def constant : Circuit (arithSignature ℤ) 2 1 where
  size := 1
  program := (Program.empty : Program (arithSignature ℤ) 2 0).gate ⟨.const 4, Fin.elim0⟩
  outputs := fun _ => .gate 0

example : (constant.withGradient 0 1 0).eval (arithInterpretation ℤ) ![3, 5] = ![4, 0, 0] := by
  decide +kernel

example : (constant.withGradient 0 1 0).size = 3 := by decide +kernel

/-! ### Polynomials -/

private theorem polynomial_demo : (demo ℚ).polynomial 0 = X 0 * X 1 + X 0 := rfl

/-- The gradient outputs of `x₀ * x₁ + x₀` are `x₁ + 1` and `x₀`, as formal polynomials. -/
example : ((demo ℚ).withGradient 0 1 0).polynomial (Fin.natAdd 1 0) = X 1 + 1 ∧
    ((demo ℚ).withGradient 0 1 0).polynomial (Fin.natAdd 1 1) = X 0 := by
  rw [Circuit.polynomial_withGradient_natAdd, Circuit.polynomial_withGradient_natAdd,
    polynomial_demo]
  simp [pderiv_X]

/-- `x₀ * x₀ + x₁ * x₁`, the power sum of degree two in two variables. -/
private def sumSquares : Circuit (arithSignature ℚ) 2 1 where
  size := 3
  program := (((Program.empty : Program (arithSignature ℚ) 2 0).gate
    ⟨.mul, ![.input 0, .input 0]⟩).gate ⟨.mul, ![.input 1, .input 1]⟩).gate
    ⟨.add, ![.gate 0, .gate 1]⟩
  outputs := fun _ => .gate 2

private theorem polynomial_sumSquares : sumSquares.polynomial 0 = psum (Fin 2) ℚ 2 := by
  rw [psum, Fin.sum_univ_two, sq, sq]
  rfl

/-- Seeding with `1 / 2` turns the gradient of `x₀ ^ 2 + x₁ ^ 2` into the power map
`(x₀, x₁)`, within `5 · 3 + 2` gates and `3 · 2` multiplications. -/
example : ∃ e : Circuit (arithSignature ℚ) 2 2, e.size ≤ 17 ∧
    e.program.cost ArithOp.mulCost = 6 ∧ ∀ i, e.polynomial i = X i ^ 1 := by
  obtain ⟨e, hsize, hmul, he⟩ := sumSquares.exists_pow_of_psum (d := 1) (u := 1 / 2)
    (by norm_num) 0 polynomial_sumSquares
  exact ⟨e, hsize, hmul.trans (by decide +kernel), he⟩

/-! ### Adjugates -/

/-- The generic `2 × 2` adjugate has a circuit with at most `15 · 2⁴ + 22` gates; its entry
`(0, 0)` is the variable of entry `(1, 1)`. -/
example : ∃ d : Circuit (arithSignature ℚ) (2 * 2) (2 * 2), d.size ≤ 262 ∧
    d.polynomial (finProdFinEquiv (0, 0)) = X (finProdFinEquiv (1, 1)) := by
  obtain ⟨d, hsize, hd⟩ := exists_circuit_adjugate (K := ℚ) 2
  refine ⟨d, hsize, (hd 0 0).trans ?_⟩
  simp [Matrix.adjugate_fin_two, genericMatrix]

end ComplexityTests.ArithmeticGradient
