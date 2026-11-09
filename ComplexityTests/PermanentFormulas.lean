/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Permanent.Formula
import Complexity.Foundations.Data.Matrix.Permanent
import Mathlib.Algebra.Field.ZMod

/-!
# Permanent projections of concrete arithmetic formulas

The mixed formula `(X₀ + 2) * (X₀ + X₁)` uses addition, multiplication, a repeated input and a
constant, and evaluates to `50` on `(3, 7)`. Its four operation nodes give a permanent projection
of dimension five over `ℕ`. Squaring in characteristic two remains the formal polynomial
`X₀²`. Empty blocks and constant-only formulas check the zero-dimensional boundary cases.
-/

namespace ComplexityTests.PermanentFormulas

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

private def mixed : Formula (arithSignature ℕ) 2 :=
  .gate₂ .mul rfl
    (.gate₂ .add rfl (.input 0) (.gate (.const 2) Fin.elim0))
    (.gate₂ .add rfl (.input 0) (.input 1))

private theorem mixed_size : mixed.size = 4 := by
  simp [mixed]

example : mixed.eval (arithInterpretation ℕ) ![3, 7] = 50 := by
  norm_num [mixed, Formula.eval, Formula.gate₂, arithInterpretation, arithInterpretationWith]

private theorem mixed_projection : IsProjection
    ((X 0 + 2) * (X 0 + X 1) : MvPolynomial (Fin 2) ℕ)
    (genericMatrix ℕ 5).permanent := by
  have h := mixed.isProjection_permanent
  rw [mixed_size] at h
  simpa [mixed, Formula.eval, Formula.gate₂, arithInterpretationWith] using h

-- Multiplicative closure and padding use the same existing projection API.
example : IsProjection
    (((X 0 + 2) * (X 0 + X 1)) * X 0 : MvPolynomial (Fin 2) ℕ)
    (genericMatrix ℕ 8).permanent := by
  have hx : IsProjection (X (0 : Fin 2) : MvPolynomial (Fin 2) ℕ)
      (genericMatrix ℕ 1).permanent :=
    (Formula.input (σ := arithSignature ℕ) (n := 2) 0).isProjection_permanent
  exact isProjection_permanent_mono (by decide : 5 + 1 ≤ 8) (mixed_projection.permanent_mul hx)

example : IsProjection (mixed.toCircuit.polynomial 0) (genericMatrix ℕ 5).permanent := by
  have h := mixed.isProjection_permanent_toCircuit
  rw [mixed_size] at h
  exact h

private def square : Formula (arithSignature (ZMod 2)) 1 :=
  .gate₂ .mul rfl (.input 0) (.input 0)

example : IsProjection (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2))
    (genericMatrix (ZMod 2) 2).permanent := by
  have h := square.isProjection_permanent
  rw [show square.size = 1 by decide] at h
  simpa [square, Formula.eval, Formula.gate₂, arithInterpretationWith, sq] using h

private def constantOnly : Formula (arithSignature ℕ) 0 := .gate (.const 7) Fin.elim0

example : IsProjection (C 7 : MvPolynomial (Fin 0) ℕ) (genericMatrix ℕ 2).permanent := by
  have h := constantOnly.isProjection_permanent
  rw [show constantOnly.size = 1 by decide] at h
  simpa [constantOnly, Formula.eval, arithInterpretationWith] using h

-- The upper-right block can be nonzero: square diagonal blocks still factor.
example : (Matrix.fromBlocks (!![2] : Matrix (Fin 1) (Fin 1) ℕ)
    (!![3, 11] : Matrix (Fin 1) (Fin 2) ℕ) 0 !![2, 3; 5, 7]).permanent = 58 := by
  rw [Matrix.permanent_fromBlocks_zero₂₁, Matrix.permanent_unique,
    Matrix.permanent_succ_row_zero, Fin.sum_univ_two]
  decide

example (A : Matrix (Fin 2) (Fin 2) ℕ) :
    (Matrix.fromBlocks A (0 : Matrix (Fin 2) (Fin 0) ℕ) 0 1).permanent = A.permanent := by
  rw [Matrix.permanent_fromBlocks_zero, Matrix.permanent_one, mul_one]

example : ((!![2, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℕ).submatrix
    (Equiv.swap 0 1) (Equiv.refl _)).permanent = 29 := by
  rw [Matrix.permanent_submatrix_equiv_equiv, Matrix.permanent_succ_row_zero, Fin.sum_univ_two]
  decide

end ComplexityTests.PermanentFormulas
