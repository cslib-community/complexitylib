/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import Complexity.Computability.Circuit.Arithmetic.DepthThree
import Complexity.Foundations.Data.Matrix.Permanent
import Mathlib.Algebra.Field.ZMod

/-!
# Depth-three circuits for the determinant and permanent

The `2 × 2` determinant and permanent are sums of two products of two variables, and the
partial-derivative bound shows that two product gates are necessary, over `ℚ` and over `ZMod 2`.
The two measure bounds together show that the `2 × 2` determinant is not a product of two affine
forms, and the family corollaries rule out single product gates for the `2 × 2` members of the
determinant and permanent families.
-/

namespace ComplexityTests.ArithmeticDepthThree

open Cslib.Circuits MvPolynomial

variable {K : Type*} [Field K]

/-- The product `a * X p * X q` as a product of two affine forms. -/
private def entryProduct (a : K) (p q : Fin 2 × Fin 2) : DepthThree.Term K (Fin 2 × Fin 2) 2 :=
  ⟨![Pi.single p a, Pi.single q 1], ![0, 0]⟩

private theorem polynomial_entryProduct (a : K) (p q : Fin 2 × Fin 2) :
    (entryProduct a p q).polynomial = C a * X p * X q := by
  simp [DepthThree.Term.polynomial, entryProduct, Fin.prod_univ_two, Pi.single_apply,
    Finset.sum_ite_eq', ← smul_eq_C_mul]

/-- The diagonal product plus `a` times the antidiagonal product, with two product gates. -/
private def twoProducts (a : K) :
    Circuit (SumOfTerms.signature (DepthThree.Term K (Fin 2 × Fin 2) 2)) 0 1 where
  size := 3
  program := (((Program.empty : Program (SumOfTerms.signature _) 0 0).gate
    ⟨.term (entryProduct 1 (0, 0) (1, 1)), Fin.elim0⟩).gate
      ⟨.term (entryProduct a (1, 0) (0, 1)), Fin.elim0⟩).gate ⟨.add, ![.gate 0, .gate 1]⟩
  outputs := ![.gate 2]

private theorem eval_twoProducts (a : K) :
    (twoProducts a).eval (SumOfTerms.interpretation DepthThree.Term.polynomial) Fin.elim0 0 =
      X (0, 0) * X (1, 1) + C a * X (1, 0) * X (0, 1) := by
  change (entryProduct 1 (0, 0) (1, 1)).polynomial + (entryProduct a (1, 0) (0, 1)).polynomial = _
  simp [polynomial_entryProduct]

private theorem twoProducts_det :
    (twoProducts (-1 : K)).eval (SumOfTerms.interpretation DepthThree.Term.polynomial)
      Fin.elim0 0 = (Matrix.mvPolynomialX (Fin 2) (Fin 2) K).det := by
  rw [eval_twoProducts, Matrix.det_fin_two]
  simp [Matrix.mvPolynomialX_apply, sub_eq_add_neg, mul_comm]

private theorem twoProducts_permanent :
    (twoProducts (1 : K)).eval (SumOfTerms.interpretation DepthThree.Term.polynomial)
      Fin.elim0 0 = (Matrix.mvPolynomialX (Fin 2) (Fin 2) K).permanent := by
  rw [eval_twoProducts, Matrix.permanent_succ_column_zero, Fin.sum_univ_two]
  simp [Matrix.mvPolynomialX_apply, Matrix.permanent, Fin.succAbove, Matrix.submatrix]

-- Two product gates are necessary for the `2 × 2` determinant and permanent, and they suffice.
example : (twoProducts (-1 : K)).program.cost SumOfTerms.termCost = 2 := rfl

example : 2 ≤ (twoProducts (-1 : ℚ)).program.cost SumOfTerms.termCost := by
  have h := DepthThree.choose_sq_le_mul_cost_det (twoProducts (-1 : ℚ)) 1 0 twoProducts_det
  norm_num at h
  omega

-- Over `ZMod 2` the determinant and permanent coincide; the bound needs no characteristic.
example : 2 ≤ (twoProducts (1 : ZMod 2)).program.cost SumOfTerms.termCost := by
  have h := DepthThree.choose_sq_le_mul_cost_permanent (twoProducts (1 : ZMod 2)) 1 0
    twoProducts_permanent
  norm_num at h
  omega

-- Both measure bounds together: the `2 × 2` determinant is not a product of two affine forms.
example (a : Fin 2 → Fin 2 × Fin 2 → ℚ) (b : Fin 2 → ℚ) :
    ∏ i, (∑ v, a i v • X v + C (b i)) ≠ (Matrix.mvPolynomialX (Fin 2) (Fin 2) ℚ).det := by
  intro h
  have hle := rank_partialDerivatives_prod_le a b 1
  rw [h] at hle
  have h' : Nat.choose 2 1 ^ 2 ≤ Nat.choose 2 1 := by
    exact_mod_cast (Matrix.choose_sq_le_rank_partialDerivatives_det_mvPolynomialX 1).trans hle
  norm_num at h'

/-- A circuit with a single product gate. -/
private def oneProduct (t : DepthThree.Term K (Fin (2 * 2)) 2) :
    Circuit (SumOfTerms.signature (DepthThree.Term K (Fin (2 * 2)) 2)) 0 1 :=
  Circuit.oneGate (.term t) Fin.elim0

-- No single product gate computes the `2 × 2` members of the determinant and permanent families.
example (t : DepthThree.Term ℚ (Fin (2 * 2)) 2) :
    (oneProduct t).eval (SumOfTerms.interpretation DepthThree.Term.polynomial) Fin.elim0 0 ≠
      (Arithmetic.detFamily ℚ).poly 2 := by
  intro h
  have h' := DepthThree.choose_sq_le_mul_cost_detFamily (oneProduct t) 1 0 h
  rw [show (oneProduct t).program.cost SumOfTerms.termCost = 1 from rfl] at h'
  norm_num at h'

example (t : DepthThree.Term (ZMod 2) (Fin (2 * 2)) 2) :
    (oneProduct t).eval (SumOfTerms.interpretation DepthThree.Term.polynomial) Fin.elim0 0 ≠
      (Arithmetic.permFamily (ZMod 2)).poly 2 := by
  intro h
  have h' := DepthThree.choose_sq_le_mul_cost_permFamily (oneProduct t) 1 0 h
  rw [show (oneProduct t).program.cost SumOfTerms.termCost = 1 from rfl] at h'
  norm_num at h'

end ComplexityTests.ArithmeticDepthThree
