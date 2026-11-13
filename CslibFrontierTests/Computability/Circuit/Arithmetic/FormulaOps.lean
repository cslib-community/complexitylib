/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.FormulaOps

/-!
# Substitution into arithmetic formulas of unbounded fan-in

The operations of `Cslib.Circuits.Arithmetic.SPFormula` on the formula `x₀ * x₁ + x₀` over `ℚ`,
which has five nodes: the polynomial computed and one size bound for each.
-/

@[expose] public section

namespace CslibFrontierTests.FormulaOps

open Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.SPFormula MvPolynomial

/-- The formula `x₀ * x₁ + x₀`. -/
def sample : SPFormula ℚ 2 :=
  add ![1, 1] ![mul ![.input 0, .input 1], .input 0]

/-- The sample formula computes `X 0 * X 1 + X 0`. -/
theorem polynomial_sample : sample.polynomial = X 0 * X 1 + X 0 := by
  simp [sample, Fin.sum_univ_two, Fin.prod_univ_two]

/-- The sample formula has five nodes. -/
theorem nodeCount_sample : sample.nodeCount = 5 := by
  simp [sample, Fin.sum_univ_two]

/-- Substituting `2 x + 1` for every input `x`. -/
theorem polynomial_substFormula_affineInput :
    (substFormula (affineInput id (fun _ => 2) fun _ => 1) sample).polynomial =
      (C 2 * X 0 + 1) * (C 2 * X 1 + 1) + (C 2 * X 0 + 1) := by
  simp [polynomial_substFormula, polynomial_sample]

/-- The affine substitution keeps the product-depth and at most triples the size. -/
theorem substFormula_affineInput_bounds :
    (substFormula (affineInput id (fun _ => 2) fun _ => 1) sample).productDepth ≤
        sample.productDepth + 0 ∧
      (substFormula (affineInput id (fun _ => 2) fun _ => 1) sample).nodeCount ≤ 5 * 3 :=
  ⟨productDepth_substFormula_le (fun i => (productDepth_affineInput _ _ _ i).le) sample,
    nodeCount_sample ▸
      nodeCount_substFormula_le (fun i => (nodeCount_affineInput _ _ _ i).le) (by norm_num) sample⟩

/-- Substituting the constant `3` for the input `1`. -/
theorem polynomial_substFormula_constInput :
    (substFormula (constInput ![.inl 0, .inr 3]) sample).polynomial =
      (X 0 * C 3 + X 0 : MvPolynomial (Fin 1) ℚ) := by
  simp [polynomial_substFormula, polynomial_sample]

/-- The substitution of a constant does not increase the size. -/
theorem nodeCount_substFormula_constInput :
    (substFormula (constInput ![.inl (0 : Fin 1), .inr 3]) sample).nodeCount ≤ 5 * 1 :=
  nodeCount_sample ▸
    nodeCount_substFormula_le (fun i => (nodeCount_constInput _ i).le) le_rfl sample

/-- The sum of monomials of `X 0 * X 1 + X 0` computes it, with product-depth at most one. -/
theorem ofSparse_sample :
    (ofSparse (X 0 * X 1 + X 0 : MvPolynomial (Fin 2) ℚ)).polynomial = X 0 * X 1 + X 0 ∧
      (ofSparse (X 0 * X 1 + X 0 : MvPolynomial (Fin 2) ℚ)).productDepth ≤ 1 :=
  ⟨polynomial_ofSparse _, productDepth_ofSparse_le _⟩

/-- The total degree of the sample polynomial is at most the five nodes of the formula. -/
theorem totalDegree_sample_le : (X 0 * X 1 + X 0 : MvPolynomial (Fin 2) ℚ).totalDegree ≤ 5 := by
  simpa [polynomial_sample, nodeCount_sample] using totalDegree_polynomial_le_nodeCount sample

end CslibFrontierTests.FormulaOps
