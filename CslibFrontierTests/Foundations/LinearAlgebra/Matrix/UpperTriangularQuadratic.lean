/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.UpperTriangularQuadratic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Tests for canonical upper-triangular quadratic representatives

Exercises `Matrix.upperQuadratic` over `ZMod 2` (characteristic two) and `ℤ` for nonsymmetric
matrices with nonzero off-diagonal entries above and below the diagonal, checking the quadratic-form
equality, uniqueness, and negative witnesses showing that dropping either the transpose contribution
or lower-triangular zeroing breaks the specification.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.MatrixUpperTriangularQuadratic

open Matrix

/-- Nonsymmetric `3 × 3` matrix over `ZMod 2` with nonzero off-diagonal entries above and below the
diagonal (`(0, 1)`, `(0, 2)`, `(2, 0)`, `(2, 1)`). -/
private def gf2Matrix : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 1; 0, 0, 0; 1, 1, 1]

/-- Candidate upper-triangular representative written explicitly. -/
private def gf2ExpectedUpper : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 0; 0, 0, 1; 0, 0, 1]

/-- Dropping the transpose contribution `M j i` on `i < j` produces an upper-triangular matrix with
the wrong quadratic form. -/
private def gf2WithoutTranspose : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 1; 0, 0, 0; 0, 0, 1]

/-- Dropping lower-triangular zeroing keeps the same quadratic form (`IsAlt` difference) while
violating upper triangularity. -/
private def gf2WithoutZeroing : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 0; 0, 0, 0; 0, 1, 1]

example : gf2Matrixᵀ ≠ gf2Matrix := by
  decide

example : gf2Matrix.upperQuadratic = gf2ExpectedUpper := by
  decide

example :
    gf2Matrix.upperQuadratic.IsUpperTriangular ∧
    gf2Matrix.upperQuadratic 0 1 = 1 ∧
    gf2Matrix.upperQuadratic 0 2 = 0 ∧
    gf2Matrix.upperQuadratic 1 2 = 1 ∧
    gf2Matrix.upperQuadratic 2 1 = 0 := by
  refine ⟨isUpperTriangular_upperQuadratic gf2Matrix, ?_, ?_, ?_, ?_⟩ <;> decide

example :
    gf2Matrix.upperQuadratic.toQuadraticForm' = gf2Matrix.toQuadraticForm' ∧
    gf2Matrix.upperQuadratic.toQuadraticForm' ![1, 1, 1] = 0 ∧
    gf2Matrix.toQuadraticForm' ![1, 1, 1] = 0 ∧
    gf2Matrix.upperQuadratic.toQuadraticForm' ![0, 0, 1] = 1 ∧
    gf2Matrix.toQuadraticForm' ![0, 1, 1] = 0 := by
  refine ⟨toQuadraticForm'_upperQuadratic gf2Matrix, ?_, ?_, ?_, ?_⟩ <;>
    · rw [toQuadraticForm'_apply]
      decide

/-- Uniqueness via `IsAlt`: an explicit upper-triangular matrix whose difference from `gf2Matrix`
induces an alternating bilinear form equals `gf2Matrix.upperQuadratic`. -/
example : gf2ExpectedUpper = gf2Matrix.upperQuadratic := by
  refine eq_upperQuadratic_of_isUpperTriangular_of_isAlt ?_ ?_
  · decide
  · refine isAlt_toLinearMap₂'_iff.mpr ⟨?_, ?_⟩
    · decide
    · decide

/-- Uniqueness via `Matrix.toQuadraticForm'`: an explicit upper-triangular matrix inducing the same
quadratic form as `gf2Matrix` equals `gf2Matrix.upperQuadratic`. -/
example : gf2ExpectedUpper = gf2Matrix.upperQuadratic := by
  refine eq_upperQuadratic_of_isUpperTriangular_of_toQuadraticForm'_eq (by decide) ?_
  ext v
  fin_cases v <;> decide

/-- Negative test for dropping the transpose contribution: `gf2WithoutTranspose` is upper
triangular, yet disagrees with `gf2Matrix` on `![0, 1, 1]`, is not alternating-equivalent to
`gf2Matrix`, and differs from `gf2Matrix.upperQuadratic`. -/
example :
    gf2WithoutTranspose.IsUpperTriangular ∧
    gf2WithoutTranspose.toQuadraticForm' ≠ gf2Matrix.toQuadraticForm' ∧
    ¬ (Matrix.toLinearMap₂' (ZMod 2) (S₁ := ZMod 2) (S₂ := ZMod 2)
        (gf2WithoutTranspose - gf2Matrix)).IsAlt ∧
    gf2WithoutTranspose ≠ gf2Matrix.upperQuadratic := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · intro h
    have hv := DFunLike.congr_fun h ![0, 1, 1]
    simp only [toQuadraticForm'_apply] at hv
    exact absurd hv (by decide)
  · intro hAlt
    exact absurd (eq_upperQuadratic_of_isUpperTriangular_of_isAlt (by decide) hAlt) (by decide)

/-- Negative test for dropping triangular zeroing: `gf2WithoutZeroing` induces the same quadratic
form as `gf2Matrix` (with alternating difference), yet is not upper triangular and differs from
`gf2Matrix.upperQuadratic`. -/
example :
    (Matrix.toLinearMap₂' (ZMod 2) (S₁ := ZMod 2) (S₂ := ZMod 2)
        (gf2WithoutZeroing - gf2Matrix)).IsAlt ∧
    gf2WithoutZeroing.toQuadraticForm' = gf2Matrix.toQuadraticForm' ∧
    ¬ gf2WithoutZeroing.IsUpperTriangular ∧
    gf2WithoutZeroing ≠ gf2Matrix.upperQuadratic := by
  have hAlt : (Matrix.toLinearMap₂' (ZMod 2) (S₁ := ZMod 2) (S₂ := ZMod 2)
      (gf2WithoutZeroing - gf2Matrix)).IsAlt := by
    refine isAlt_toLinearMap₂'_iff.mpr ⟨by decide, by decide⟩
  refine ⟨hAlt, toQuadraticForm'_eq_iff_isAlt_toLinearMap₂'_sub.mpr hAlt, by decide, by decide⟩

/-- Characteristic-zero concrete check over `ℤ`, verifying idempotence and quadratic-form
preservation. -/
example :
    let A : Matrix (Fin 3) (Fin 3) ℤ := !![1, 2, -1; 3, 4, 5; 0, -2, 7]
    A.upperQuadratic = !![1, 5, -1; 0, 4, 3; 0, 0, 7] ∧
    A.upperQuadratic.upperQuadratic = A.upperQuadratic ∧
    A.upperQuadratic.toQuadraticForm' = A.toQuadraticForm' := by
  intro A
  refine ⟨by decide, upperQuadratic_upperQuadratic A, toQuadraticForm'_upperQuadratic A⟩

end CslibFrontierTests.Foundations.MatrixUpperTriangularQuadratic
