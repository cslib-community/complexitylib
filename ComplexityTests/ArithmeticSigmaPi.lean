/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.SigmaPi

/-!
# Arithmetic formulas of unbounded fan-in

Product-depths, node counts and polynomials of small formulas, among them a single sum gate of
fan-in four, of product-depth zero and five nodes, and set-multilinearity holding for
`x₀ * (2 x₁ + 3 x₂)` and the formula `0`, and failing for the square `x₀ * x₀`.
-/

namespace ComplexityTests.ArithmeticSigmaPi

open Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-- `x₀ * (2 x₁ + 3 x₂)`. -/
private noncomputable def f : SPFormula ℚ 3 :=
  .mul ![.input 0, .add ![2, 3] ![.input 1, .input 2]]

/-- `(x₀ x₁ + x₂) * 5`, a product of a sum of a product. -/
private noncomputable def g : SPFormula ℚ 3 :=
  .mul ![.add ![1, 1] ![.mul ![.input 0, .input 1], .input 2], .const 5]

/-- The square `x₀ * x₀`. -/
private noncomputable def sq : SPFormula ℚ 1 :=
  .mul ![.input 0, .input 0]

/-- A sum of four inputs is one sum gate. -/
private noncomputable def sum4 : SPFormula ℚ 4 :=
  .add ![1, 1, 1, 1] ![.input 0, .input 1, .input 2, .input 3]

example : f.productDepth = 1 := by
  simp [f, Fin.univ_succ]

example : g.productDepth = 2 := by
  simp [g, Fin.univ_succ]

example : sum4.productDepth = 0 := by
  simp [sum4, Fin.univ_succ]

example : f.nodeCount = 5 := by
  simp [f, Fin.sum_univ_succ]

example : g.nodeCount = 7 := by
  simp [g, Fin.sum_univ_succ]

example : sum4.nodeCount = 5 := by
  simp [sum4, Fin.sum_univ_succ]

example : f.polynomial = X 0 * (C 2 * X 1 + C 3 * X 2) := by
  simp [f, Fin.sum_univ_succ, Fin.prod_univ_succ]

example : g.polynomial = (X 0 * X 1 + X 2) * C 5 := by
  simp [g, Fin.sum_univ_succ, Fin.prod_univ_succ]

example : sum4.polynomial = X 0 + X 1 + X 2 + X 3 := by
  simp [sum4, Fin.sum_univ_succ, add_assoc]

/-- Evaluation agrees with the polynomial. -/
example : f.eval (sigmaPiInterpretation ℚ) ![1, 2, 3] = 13 := by
  rw [← SPFormula.eval_polynomial]
  norm_num [f, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- `x₀ * (2 x₁ + 3 x₂)` is set-multilinear for the blocks `{x₀}`, `{x₁, x₂}`. -/
private def blk : Fin 3 → Fin 2 := ![0, 1, 1]

private theorem f_isSetMultilinear : f.IsSetMultilinear blk Finset.univ := by
  rw [f, SPFormula.isSetMultilinear_mul_iff]
  refine ⟨![{0}, {1}], ?_, fun j => ?_, by decide⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  fin_cases j
  · exact .input 0
  · refine SPFormula.isSetMultilinear_add_iff.2 fun k => ?_
    fin_cases k
    · exact .input 1
    · exact .input 2

example : f.polynomial.IsHomogeneous 2 := by
  simpa using f_isSetMultilinear.isHomogeneous

/-- The square `x₀ * x₀` is not set-multilinear on any set of blocks. -/
example (S : Finset (Fin 1)) : ¬ sq.IsSetMultilinear (fun _ => 0) S := by
  rw [sq, SPFormula.isSetMultilinear_mul_iff]
  rintro ⟨T, hT, hF, -⟩
  have h₀ := SPFormula.isSetMultilinear_input_iff.1 (hF 0)
  have h₁ := SPFormula.isSetMultilinear_input_iff.1 (hF 1)
  have := hT (show (0 : Fin 2) ≠ 1 by decide)
  simp_all [Function.onFun]

/-- The formula `0` is one node of product-depth zero, computes `0`, and is set-multilinear on
both blocks. -/
example : (SPFormula.zero : SPFormula ℚ 3).nodeCount = 1 ∧
    (SPFormula.zero : SPFormula ℚ 3).productDepth = 0 ∧
    (SPFormula.zero : SPFormula ℚ 3).polynomial = 0 ∧
    (SPFormula.zero : SPFormula ℚ 3).IsSetMultilinear blk Finset.univ :=
  ⟨SPFormula.nodeCount_zero, SPFormula.productDepth_zero, SPFormula.polynomial_zero,
    SPFormula.isSetMultilinear_zero _⟩

end ComplexityTests.ArithmeticSigmaPi
