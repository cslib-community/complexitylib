/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.DeterminantalComplexity
import Complexity.Foundations.Data.Matrix.Permanent
import Complexity.Foundations.LinearAlgebra.Matrix.Moore
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete checks for the Mignon–Ressayre bound

The `2 × 2` permanent `X₀ X₃ + X₁ X₂` is the determinant of `!![X₀, -X₁; X₂, X₃]`, so its
determinantal complexity is exactly `2`; the lower bound comes from the Mignon–Ressayre theorem.
At `n = 3` the Mignon–Ressayre point is the all-ones matrix with `-2` at `(0, 0)`; the permanent
vanishes there and the Hessian has full rank `9`. Over `ZMod 2` the `3 × 3` permanent is the
`3 × 3` determinant, so the bound fails at `n = 3`, where `(n - 1)! = 0`: the factorial hypothesis
cannot be dropped.

Grenet's theorem bounds the determinantal complexity of the `n × n` permanent by `2ⁿ - 1` over
every commutative ring, so `5 ≤ dc(perm₃) ≤ 7` over `ℚ`. At `n = 2` it gives `3`, above the exact
value `2`.
-/

namespace ComplexityTests.ArithmeticDeterminantalComplexity

open Cslib.Circuits.Arithmetic MvPolynomial

/-- The empty matrix has determinant `1`: the constant `1` has a representation of size `0`. -/
example : HasDeterminantalRepresentation (1 : MvPolynomial (Fin 2) ℚ) 0 :=
  ⟨!![], fun i => i.elim0, Matrix.det_fin_zero⟩

/-- A size-`0` representation is the constant `1`, so `X₀` has none. -/
example : ¬ HasDeterminantalRepresentation (X 0 : MvPolynomial (Fin 2) ℚ) 0 := by
  rintro ⟨A, -, hA⟩
  rw [Matrix.det_fin_zero] at hA
  have := congrArg (totalDegree (σ := Fin 2) (R := ℚ)) hA
  simp at this

/-- The `2 × 2` generic permanent is the determinant of a sign-twisted generic matrix. -/
theorem hasDeterminantalRepresentation_permanent_two :
    HasDeterminantalRepresentation (genericMatrix ℚ 2).permanent 2 := by
  refine ⟨!![X 0, -X 1; X 2, X 3], fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [totalDegree_neg]
  · rw [Matrix.det_fin_two_of, Matrix.permanent_succ_row_zero, Fin.sum_univ_two,
      Matrix.permanent_succ_row_zero, Matrix.permanent_succ_row_zero, Fin.sum_univ_one,
      Fin.sum_univ_one]
    simp [Matrix.permanent, genericMatrix, finProdFinEquiv]

/-- `dc(perm₂) = 2` over `ℚ`. -/
example : determinantalComplexity (genericMatrix ℚ 2).permanent = 2 := by
  refine le_antisymm (determinantalComplexity_le hasDeterminantalRepresentation_permanent_two) ?_
  refine le_determinantalComplexity_iff.2 fun m hm => ?_
  have := sq_le_two_mul_of_hasDeterminantalRepresentation_permanent (K := ℚ) (by norm_num) hm
  exact_mod_cast (show 2 ≤ m by omega)

example : determinantalComplexity (genericMatrix ℚ 3).det ≤ 3 :=
  determinantalComplexity_det_le 3

/-- Over `ℚ`, the `3 × 3` permanent is not a projection of the `4 × 4` determinant. -/
example : ¬ IsProjection (genericMatrix ℚ 3).permanent (genericMatrix ℚ 4).det := fun h => by
  have := sq_le_two_mul_of_isProjection_permanent_det h
  omega

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The bound also holds over `ZMod 5`, where `2! ≠ 0`. -/
example : (3 : ℕ∞) ^ 2 ≤ 2 * determinantalComplexity (genericMatrix (ZMod 5) 3).permanent :=
  sq_le_two_mul_determinantalComplexity_permanent (by decide)

/-- Over `ZMod 2` the bound holds at `n = 2`, where `1! ≠ 0`. -/
example : (2 : ℕ∞) ^ 2 ≤ 2 * determinantalComplexity (genericMatrix (ZMod 2) 2).permanent :=
  sq_le_two_mul_determinantalComplexity_permanent (by decide)

/-! ### The Mignon–Ressayre point at `n = 3` -/

example : Matrix.mignonRessayrePoint (K := ℚ) (0 : Fin 3) (0, 0) = -2 := by
  norm_num [Matrix.mignonRessayrePoint_apply]

example : Matrix.mignonRessayrePoint (K := ℚ) (0 : Fin 3) (1, 2) = 1 := by
  simp [Matrix.mignonRessayrePoint_apply]

example : eval (Matrix.mignonRessayrePoint (K := ℚ) (0 : Fin 3))
    (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).permanent = 0 :=
  Matrix.eval_permanent_mignonRessayrePoint 0

/-- The Hessian entry at `(1, 1)` and `(2, 2)` is `1! - 3 · 0! = -2`. -/
example : hessian (Matrix.mignonRessayrePoint (K := ℚ) (0 : Fin 3))
    (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).permanent (1, 1) (2, 2) = -2 := by
  rw [Matrix.hessian_permanent_mignonRessayrePoint]
  norm_num

/-- The Hessian entry at `(0, 0)` and `(1, 1)` is `1! = 1`. -/
example : hessian (Matrix.mignonRessayrePoint (K := ℚ) (0 : Fin 3))
    (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).permanent (0, 0) (1, 1) = 1 := by
  rw [Matrix.hessian_permanent_mignonRessayrePoint]
  norm_num

example : (hessian (Matrix.mignonRessayrePoint (K := ℚ) (0 : Fin 3))
    (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).permanent).rank = 9 :=
  Matrix.rank_hessian_permanent_mignonRessayrePoint 0 (by norm_num) (by simp)

/-! ### Characteristic two -/

/-- Over `ZMod 2` the `3 × 3` permanent is the `3 × 3` determinant, which violates `3² ≤ 2 · 3`.
Here `(3 - 1)! = 2 = 0`, so the hypothesis `(n - 1)! ≠ 0` cannot be dropped. -/
example : HasDeterminantalRepresentation (genericMatrix (ZMod 2) 3).permanent 3 ∧
    ¬ 3 ^ 2 ≤ 2 * 3 ∧ (((3 - 1).factorial : ℕ) : ZMod 2) = 0 :=
  ⟨by
    rw [← Matrix.det_eq_permanent_of_charTwo]
    exact hasDeterminantalRepresentation_det 3, by omega, by decide⟩

/-! ### Grenet's upper bound -/

/-- The determinant of Grenet's `3 × 3` matrix of a `2 × 2` integer matrix is its permanent. -/
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ).grenetMatrix.det = 10 := by
  rw [← Matrix.permanent_eq_det_grenetMatrix, Matrix.permanent_succ_row_zero, Fin.sum_univ_two,
    Matrix.permanent_succ_row_zero, Matrix.permanent_succ_row_zero, Fin.sum_univ_one,
    Fin.sum_univ_one]
  simp [Matrix.permanent, Fin.succAbove]

/-- The sandwich `5 ≤ dc(perm₃) ≤ 7` over `ℚ`: Mignon–Ressayre below, Grenet above. -/
example : 5 ≤ determinantalComplexity (genericMatrix ℚ 3).permanent ∧
    determinantalComplexity (genericMatrix ℚ 3).permanent ≤ 7 := by
  refine ⟨le_determinantalComplexity_iff.2 fun m hm => ?_,
    determinantalComplexity_permanent_le 3⟩
  have := sq_le_two_mul_of_hasDeterminantalRepresentation_permanent (K := ℚ) (by norm_num) hm
  exact_mod_cast (show 5 ≤ m by omega)

/-- In characteristic zero, `n² ≤ 2 · dc(perm_n)` and `dc(perm_n) ≤ 2ⁿ - 1`. -/
example (n : ℕ) : (n : ℕ∞) ^ 2 ≤ 2 * determinantalComplexity (genericMatrix ℚ n).permanent ∧
    determinantalComplexity (genericMatrix ℚ n).permanent ≤ (2 ^ n - 1 : ℕ) :=
  ⟨sq_le_two_mul_determinantalComplexity_permanent_of_charZero n,
    determinantalComplexity_permanent_le n⟩

/-- Grenet's projection holds over every commutative ring, for example `ℤ` and `ZMod 2`. -/
example : IsProjection (genericMatrix ℤ 3).permanent (genericMatrix ℤ 7).det :=
  isProjection_permanent_det_two_pow_sub_one 3

example : determinantalComplexity (genericMatrix (ZMod 2) 4).permanent ≤ 15 :=
  determinantalComplexity_permanent_le 4

end ComplexityTests.ArithmeticDeterminantalComplexity
