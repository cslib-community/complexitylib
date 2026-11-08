/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Arithmetic.Hessian.SourceComplexity

/-!
# Minimum multiplication cost and supplied Hessians

The product of two variables has minimum multiplication cost one when only the variables are
supplied. Supplying the product itself makes both its multiplication cost and residual rank zero.
-/

namespace ComplexityTests.HessianSourceComplexity

open Cslib.Circuits MvPolynomial

private noncomputable def product : MvPolynomial (Fin 2) ℚ := X 0 * X 1

private noncomputable def I : Interpretation (arithSignature ℚ) (MvPolynomial (Fin 2) ℚ) :=
  arithInterpretationWith ℚ MvPolynomial.C

private theorem rank_product : (hessian (fun _ => (0 : ℚ)) product).rank = 2 := by
  have h : hessian (fun _ => (0 : ℚ)) product = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [product, hessian]
  rw [h, Matrix.rank_of_isUnit]
  · rfl
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp [Matrix.det_fin_two]

-- Raw variables have zero Hessians, so the product's residual rank stays two.
example : hessianResidualRank (fun _ => (0 : ℚ)) product X = 2 := by
  simp [hessianResidualRank, hessian_X, rank_product]

private theorem product_lower : (1 : ℕ∞) ≤ ecomplexityFrom I ArithOp.mulCost
    (fun (_ : Unit) (_ : Fin 1) => product) (fun _ => X) := by
  apply le_ecomplexityFrom_of_hessian_rank id (fun _ => 0) product X 1
  intro coefficients
  simp [rank_product]

-- Both the lower bound and an attaining circuit are checked.
example : ecomplexityFrom I ArithOp.mulCost
    (fun (_ : Unit) (_ : Fin 1) => product) (fun _ => X) = 1 := by
  apply le_antisymm _ product_lower
  exact ecomplexityFrom_le_of_computesFrom
    (Circuit.oneGate (σ := arithSignature ℚ) .mul id) (fun _ => rfl)

-- Supplying the nonlinear target for free removes its entire Hessian from the residual.
example (point : Fin 2 → ℚ) : hessianResidualRank point product (fun _ : Fin 1 => product) = 0 := by
  apply nonpos_iff_eq_zero.mp
  simpa using hessianResidualRank_le point product (fun _ : Fin 1 => product) (fun _ => 1)

example : ecomplexityFrom I ArithOp.mulCost
    (fun (_ : Unit) (_ : Fin 1) => product) (fun _ (_ : Fin 1) => product) = 0 :=
  ecomplexityFrom_self _

-- Raw variables together with the nonlinear helper also give zero minimum cost.
example : ecomplexityFrom I ArithOp.mulCost
    (fun (_ : Unit) (_ : Fin 1) => product)
    (fun _ => Fin.append X (fun _ : Fin 1 => product)) = 0 := by
  apply nonpos_iff_eq_zero.mp
  exact ecomplexityFrom_le_of_computesFrom (Circuit.wiring _ (fun _ => 2)) (fun _ => rfl)

-- The minimum-rank theorem and helper variant require no characteristic or universe restriction.
universe u v w
example {C : Type u} {K : Type v} {ι : Type w} [Field K] [Fintype ι]
    (constant : C → K) (point : ι → K) (target : MvPolynomial ι K)
    (sources : Fin 3 → MvPolynomial ι K) :
    hessianResidualRank point target sources ≤ 2 *
      ecomplexityFrom (arithInterpretationWith C (MvPolynomial.C ∘ constant)) ArithOp.mulCost
        (fun (_ : Unit) (_ : Fin 1) => target) (fun _ => sources) :=
  hessianResidualRank_le_two_mul_ecomplexityFrom constant point target sources

example {K : Type*} [Field K] (point : Fin 2 → K) (target : MvPolynomial (Fin 2) K)
    (helpers : Fin 3 → MvPolynomial (Fin 2) K) :
    hessianResidualRank point target helpers ≤ 2 *
      ecomplexityFrom (arithInterpretationWith K MvPolynomial.C) ArithOp.mulCost
        (fun (_ : Unit) (_ : Fin 1) => target) (fun _ => Fin.append X helpers) :=
  hessianResidualRank_le_two_mul_ecomplexityFrom_with_helpers id point target helpers

end ComplexityTests.HessianSourceComplexity
