/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests for the arithmetic and derivative APIs)

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Foundations.Data.MvPolynomial.PartialDerivatives
import Mathlib.Tactic.FinCases

/-!
# Mixed differentiation through the generic-matrix representation

Ordinary imports expose both representation and renaming equations without the depth-three
circuit module. A mixed derivative of the row-major two-by-two determinant is computed by
transporting the original matrix variables through their bijective row-major encoding.
-/

public section

open MvPolynomial Cslib.Circuits

example : iteratedPDeriv ![0, 3] ((Arithmetic.genericMatrix ℚ 2).det) = 1 := by
  have hdet : (Arithmetic.genericMatrix ℚ 2).det =
      rename finProdFinEquiv (Matrix.mvPolynomialX (Fin 2) (Fin 2) ℚ).det := by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← Arithmetic.genericMatrix_eq_map_rename]
  have hcoords : finProdFinEquiv ∘ (![(0, 0), (1, 1)] : Fin 2 → Fin 2 × Fin 2) =
      (![0, 3] : Fin 2 → Fin 4) := by
    ext i
    fin_cases i <;> rfl
  have h := iteratedPDeriv_rename finProdFinEquiv.injective
    (![(0, 0), (1, 1)] : Fin 2 → Fin 2 × Fin 2)
    (Matrix.mvPolynomialX (Fin 2) (Fin 2) ℚ).det
  rw [hcoords] at h
  rw [hdet, h]
  simp [iteratedPDeriv, Matrix.det_fin_two, Matrix.mvPolynomialX]

-- `genericMatrix_eq_map_rename` and `iteratedPDeriv_rename` work over a commutative semiring
-- (`ℕ`) and across distinct variable universes (`ULift.{1}`).
example : Arithmetic.genericMatrix ℕ 2 =
    (Matrix.mvPolynomialX (Fin 2) (Fin 2) ℕ).map (rename finProdFinEquiv) :=
  Arithmetic.genericMatrix_eq_map_rename

example (p : MvPolynomial (Fin 2) ℕ) :
    iteratedPDeriv (ULift.up.{1} ∘ (![0, 1] : Fin 2 → Fin 2)) (rename ULift.up.{1} p) =
      rename ULift.up.{1} (iteratedPDeriv ![0, 1] p) :=
  iteratedPDeriv_rename ULift.up_injective ![0, 1] p
