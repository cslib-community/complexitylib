/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Determinant
import Complexity.Computability.Circuit.Arithmetic.VNP
import Complexity.Foundations.Data.Matrix.Permanent
import Mathlib.Algebra.Field.ZMod

/-!
# Algebraic complexity: VP, VNP and the determinant

Circuits compute formal polynomials: over `ZMod 2` a squaring circuit computes `X ^ 2`, which agrees
with `X` as a function but not as a polynomial. The product monomial is a projection of the
`2 × 2` determinant, and the products of `n` variables form a p-projection of the determinant
family, so they are in `VP` by closure. Repeated squaring has small circuits but is not in `VP`.
The determinant circuits evaluate concrete determinants, a Boolean sum is computed, and the
determinant family is in `VNP`. The permanent expands along row 0 on both a concrete `2 × 2`
integer matrix and the `2 × 2` generic matrix polynomial.
-/

namespace ComplexityTests.AlgebraicComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-! ### Formal polynomials, not functions -/

private def square : Circuit (arithSignature (ZMod 2)) 1 1 :=
  Circuit.oneGate .mul fun _ => 0

example : square.polynomial 0 = X 0 ^ 2 := by
  simp [square, Circuit.polynomial, Circuit.eval_oneGate, sq]

/-- As a function on `ZMod 2`, the square is the identity. -/
private theorem eval_square (x : Fin 1 → ZMod 2) :
    square.eval (arithInterpretation (ZMod 2)) x 0 = x 0 := by
  simp only [square, Circuit.eval_oneGate, arithInterpretation, arithInterpretationWith_mul]
  generalize x 0 = a
  fin_cases a <;> rfl

-- As polynomials, `X ^ 2` and `X` differ.
example : (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) ≠ X 0 := fun h => by
  simpa [totalDegree_X_pow, totalDegree_X] using congrArg totalDegree h

-- Evaluation of the computed polynomial agrees with the circuit's identity evaluation on `ZMod 2`.
example (x : Fin 1 → ZMod 2) : aeval x (square.polynomial 0) = x 0 :=
  (square.aeval_polynomial x 0).trans (eval_square x)

/-! ### Projections -/

example : (genericMatrix ℚ 2).det = X 0 * X 3 - X 1 * X 2 := by
  rw [Matrix.det_fin_two]
  rfl

/-- The product of two variables is a projection of the `2 × 2` determinant. -/
example : IsProjection (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) (genericMatrix ℚ 2).det := by
  refine ⟨![.inl 0, .inr 0, .inr 0, .inl 1], ?_⟩
  rw [Matrix.det_fin_two]
  simp [genericMatrix, finProdFinEquiv]

/-- The products of `n` variables. -/
noncomputable def productFamily : PolynomialFamily ℚ where
  vars n := n
  poly _ := ∏ i, X i

/-- The product of `n` variables is the determinant of the diagonal matrix of variables, a
projection of the generic determinant. -/
theorem productFamily_isPProjection_detFamily : productFamily.IsPProjection (detFamily ℚ) := by
  refine ⟨fun n => n, PolynomiallyBounded.id, fun n => ?_⟩
  let ρ : Fin (n * n) → Fin n ⊕ ℚ := fun k =>
    if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k).2 then .inl (finProdFinEquiv.symm k).1
    else .inr 0
  refine ⟨ρ, ?_⟩
  change projection ρ (genericMatrix ℚ n).det = ∏ i : Fin n, X i
  rw [AlgHom.map_det, ← Matrix.det_diagonal]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [genericMatrix, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    projection_X, ρ, Equiv.symm_apply_apply, Matrix.diagonal_apply]
  split_ifs with h <;> simp [h]

example : productFamily ∈ VP ℚ :=
  VP.of_isPProjection detFamily_mem_VP productFamily_isPProjection_detFamily
    PolynomiallyBounded.id

/-! ### Degree bounds are part of VP -/

-- Four squaring gates compute `X₀ ^ 16`, evaluating to `2 ^ 16 = 65536` on `2`.
example : ∃ c : Circuit (arithSignature ℚ) 1 1,
    c.size ≤ 4 ∧ c.eval (arithInterpretation ℚ) ![2] 0 = 65536 := by
  obtain ⟨c, hpoly, hsize⟩ := exists_circuit_pow_two_pow (K := ℚ) 4
  refine ⟨c, hsize, ?_⟩
  have heval := (c.aeval_polynomial (![2] : Fin 1 → ℚ) 0).symm
  rw [hpoly] at heval
  simp only [powTwoPowFamily, map_pow, aeval_X, Matrix.cons_val_zero] at heval
  exact heval.trans (by norm_num)

-- Because `powTwoPowFamily` is not in `VP` while `detFamily` is, `powTwoPowFamily` cannot be a
-- p-projection of `detFamily` over `ℚ` or `ZMod 2`.
example : ¬ (powTwoPowFamily ℚ).IsPProjection (detFamily ℚ) := fun hproj =>
  powTwoPowFamily_not_mem_VP
    (VP.of_isPProjection detFamily_mem_VP hproj (PolynomiallyBounded.const 1))

example : ¬ (powTwoPowFamily (ZMod 2)).IsPProjection (detFamily (ZMod 2)) := fun hproj =>
  powTwoPowFamily_not_mem_VP
    (VP.of_isPProjection detFamily_mem_VP hproj (PolynomiallyBounded.const 1))

/-! ### The determinant -/

-- The determinant circuits evaluate determinants over the coefficient ring itself.
example : ∃ c : Circuit (arithSignature ℚ) (2 * 2) 1, c.size ≤ 52 ∧
    c.eval (arithInterpretation ℚ) ![2, 3, 5, 7] 0 = -1 := by
  obtain ⟨c, hsize, hc⟩ := exists_circuit_det_eval (K := ℚ) 2
  have h := hc (R := ℚ) !![2, 3; 5, 7]
  have hx : (fun k : Fin (2 * 2) => (!![2, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℚ)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) = ![2, 3, 5, 7] := by
    funext k
    fin_cases k <;> rfl
  rw [hx, Matrix.det_fin_two_of, Algebra.algebraMap_self, RingHom.coe_id] at h
  exact ⟨c, hsize.trans (by norm_num), h.trans (by norm_num)⟩

-- In characteristic two, `!![1, 1; 1, -1]` (determinant `-2` over `ℤ`) has determinant `0`.
example : ∃ c : Circuit (arithSignature (ZMod 2)) (2 * 2) 1, c.size ≤ 52 ∧
    c.eval (arithInterpretation (ZMod 2)) ![1, 1, 1, -1] 0 = 0 := by
  obtain ⟨c, hsize, hc⟩ := exists_circuit_det_eval (K := ZMod 2) 2
  have h := hc (R := ZMod 2) !![1, 1; 1, -1]
  have hx : (fun k : Fin (2 * 2) => (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod 2))
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) = ![1, 1, 1, -1] := by
    funext k
    fin_cases k <;> rfl
  rw [hx, Matrix.det_fin_two_of, Algebra.algebraMap_self, RingHom.coe_id] at h
  exact ⟨c, hsize.trans (by norm_num), h.trans (by decide)⟩

/-! ### The permanent -/

-- Expanding `!![2, 3; 5, 7]` along row `0` gives permanent `2 * 7 + 3 * 5 = 29` (whereas its
-- determinant above is `-1`).
example : (!![2, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℤ).permanent = 29 := by
  rw [Matrix.permanent_succ_row_zero, Fin.sum_univ_two]
  decide

-- The `2 × 2` generic permanent polynomial is `X₀ X₃ + X₁ X₂` (contrast `(genericMatrix ℚ 2).det`
-- above).
example : (permFamily ℚ).poly 2 =
    (X (0 : Fin (2 * 2)) * X (3 : Fin (2 * 2)) + X (1 : Fin (2 * 2)) * X (2 : Fin (2 * 2))) := by
  change (genericMatrix ℚ 2).permanent = X 0 * X 3 + X 1 * X 2
  rw [Matrix.permanent_succ_row_zero, Fin.sum_univ_two, Matrix.permanent_succ_row_zero,
    Matrix.permanent_succ_row_zero, Fin.sum_univ_one, Fin.sum_univ_one]
  simp [Matrix.permanent, genericMatrix, finProdFinEquiv]

/-! ### VNP -/

/-- Summing `X₀ * e` over `e ∈ {0, 1}` gives `X₀`. -/
example : booleanSum 1 (X 0 * X 1 : MvPolynomial (Fin (1 + 1)) ℚ) = X 0 := by
  rw [booleanSum, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp [booleanAssignment, Fin.append, Fin.addCases]

example : productFamily ∈ VNP ℚ :=
  VNP.of_isPProjection (VP_subset_VNP detFamily_mem_VP) productFamily_isPProjection_detFamily
    PolynomiallyBounded.id

end ComplexityTests.AlgebraicComplexity
