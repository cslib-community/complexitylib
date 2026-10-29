/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.SetMultilinear

/-!
# Set-multilinear formulas compute set-multilinear polynomials

The formula `x₀ x₂ - x₁ x₂`, a sum of two products that is set-multilinear for the blocks
`{x₀, x₁}` and `{x₂}`, computes a set-multilinear polynomial, and the finite-product closure lemma
applies to `x₀ * x₁ * x₂` with one variable per block.
-/

namespace ComplexityTests.ArithmeticSetMultilinear

open Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-- `x₀ x₂ - x₁ x₂`, a sum gate with edge constants `1` and `-1` over two product gates. -/
private noncomputable def f : SPFormula ℚ 3 :=
  .add ![1, -1] ![.mul ![.input 0, .input 2], .mul ![.input 1, .input 2]]

/-- The blocks `{x₀, x₁}` and `{x₂}`. -/
private def blk : Fin 3 → Fin 2 := ![0, 0, 1]

private theorem f_isSetMultilinear : f.IsSetMultilinear blk Finset.univ := by
  refine SPFormula.isSetMultilinear_add_iff.2 fun j => ?_
  fin_cases j
  · refine SPFormula.isSetMultilinear_mul_iff.2 ⟨![{0}, {1}], ?_, fun k => ?_, by decide⟩
    · intro i k hik
      fin_cases i <;> fin_cases k <;> first | exact absurd rfl hik | decide
    fin_cases k
    · exact .input 0
    · exact .input 2
  · refine SPFormula.isSetMultilinear_mul_iff.2 ⟨![{0}, {1}], ?_, fun k => ?_, by decide⟩
    · intro i k hik
      fin_cases i <;> fin_cases k <;> first | exact absurd rfl hik | decide
    fin_cases k
    · exact .input 1
    · exact .input 2

/-- The polynomial `x₀ x₂ - x₁ x₂` is set-multilinear on both blocks. -/
example : (X 0 * X 2 - X 1 * X 2 : MvPolynomial (Fin 3) ℚ).IsSetMultilinear blk
    Finset.univ := by
  have h := f_isSetMultilinear.isSetMultilinear_polynomial
  simpa [f, Fin.sum_univ_succ, Fin.prod_univ_succ, sub_eq_add_neg] using h

/-- `x₀ * x₁ * x₂`, one variable from each of three singleton blocks, is set-multilinear on all
three blocks. -/
example : (∏ i : Fin 3, X i : MvPolynomial (Fin 3) ℚ).IsSetMultilinear id Finset.univ := by
  have h := MvPolynomial.IsSetMultilinear.prod (blk := id) (K := ℚ) Finset.univ
    (f := fun i : Fin 3 => X i) (T := fun i => {i})
    (fun i _ j _ hij => Finset.disjoint_singleton.2 hij)
    fun i _ => isSetMultilinear_X id i
  rwa [Finset.biUnion_singleton_eq_self] at h

end ComplexityTests.ArithmeticSetMultilinear
