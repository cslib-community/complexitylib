/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.FormulaInterpolation
public import CslibFrontierTests.Computability.Circuit.Arithmetic.FormulaOps

/-!
# Interpolation of arithmetic formulas of unbounded fan-in

The formula `CslibFrontierTests.FormulaOps.sample` for `x₀ * x₁ + x₀` over `ℚ`, of five nodes, has
coefficient `x₀` of `x₁`, and the sum of its homogeneous components of degree at most one is `x₀`.
-/

public section

namespace CslibFrontierTests.FormulaInterpolation

open Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.SPFormula MvPolynomial
  CslibFrontierTests.FormulaOps

/-- The coefficient of `x₁` in `x₀ * x₁ + x₀` is `x₀`. -/
theorem polynomial_coeffLast_sample : (coeffLast 1 1 sample).polynomial = X 0 := by
  have h := polynomial_coeffLast (F := sample)
    (P := Polynomial.C (X 0) * Polynomial.X + Polynomial.C (X 0)) (r := 1)
    (fun α => by
      have h0 : (Fin.lastCases (C α) X : Fin 2 → MvPolynomial (Fin 1) ℚ) 0 = X 0 :=
        Fin.lastCases_castSucc (n := 1) 0
      have h1 : (Fin.lastCases (C α) X : Fin 2 → MvPolynomial (Fin 1) ℚ) 1 = C α :=
        Fin.lastCases_last (n := 1)
      simp [polynomial_sample, h0, h1])
    (by compute_degree) 1
  simpa using h

/-- The formula of the coefficient has at most `2 * 5 + 1` nodes. -/
theorem nodeCount_coeffLast_sample : (coeffLast 1 1 sample).nodeCount ≤ 2 * 5 + 1 :=
  nodeCount_sample ▸ nodeCount_coeffLast_le 1 1 sample

/-- The components of degree at most one of `x₀ * x₁ + x₀` sum to `x₀`. -/
theorem polynomial_lowPartFormula_sample : (lowPartFormula 1 2 sample).polynomial = X 0 := by
  have hX : (X 0 : MvPolynomial (Fin 2) ℚ).IsHomogeneous 1 := isHomogeneous_X ℚ 0
  have hXX : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ).IsHomogeneous 2 :=
    (isHomogeneous_X ℚ 0).mul (isHomogeneous_X ℚ 1)
  have hdeg : sample.polynomial.totalDegree ≤ 2 := by
    rw [polynomial_sample]
    exact (totalDegree_add _ _).trans
      (max_le hXX.totalDegree_le (hX.totalDegree_le.trans one_le_two))
  rw [polynomial_lowPartFormula hdeg, polynomial_sample]
  simp [Finset.sum_range_succ, homogeneousComponent_of_mem hX, homogeneousComponent_of_mem hXX]

/-- The formula of the low-degree part has at most `3 * (3 * 5) + 1` nodes. -/
theorem nodeCount_lowPartFormula_sample : (lowPartFormula 1 2 sample).nodeCount ≤ 3 * (3 * 5) + 1 :=
  nodeCount_sample ▸ nodeCount_lowPartFormula_le 1 2 sample

end CslibFrontierTests.FormulaInterpolation
