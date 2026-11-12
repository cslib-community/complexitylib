/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.RootFormula

/-!
# Roots of formulas of constant product-depth

The formula `y - x₀ * x₁` over `ℚ`, with `y` its last variable, has product-depth one and the
root `x₀ * x₁`, which therefore has a formula of product-depth at most two.
-/

@[expose] public section

namespace CslibFrontierTests.RootFormula

open Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.SPFormula MvPolynomial

/-- The formula `y - x₀ * x₁`, with `y` the last input. -/
def sample : SPFormula ℚ 3 :=
  add ![1, -1] ![.input 2, mul ![.input 0, .input 1]]

/-- The sample formula computes `X 2 - X 0 * X 1`. -/
theorem polynomial_sample : sample.polynomial = X 2 - X 0 * X 1 := by
  simp [sample, Fin.sum_univ_two, Fin.prod_univ_two, sub_eq_add_neg]

/-- The sample formula has product-depth one. -/
theorem productDepth_sample : sample.productDepth ≤ 1 := by
  rw [sample, productDepth_add]
  refine Finset.sup_le fun i _ => ?_
  fin_cases i
  · simp
  · change (mul ![.input 0, .input 1] : SPFormula ℚ 3).productDepth ≤ 1
    rw [productDepth_mul]
    exact Nat.add_le_add_right (Finset.sup_le fun j _ => by fin_cases j <;> simp) 1

/-- The root `x₀ * x₁` of `y - x₀ * x₁` has a formula of product-depth at most two. -/
theorem exists_formula_root_sample :
    ∃ G : SPFormula ℚ 2, G.polynomial = X 0 * X 1 ∧ G.productDepth ≤ 2 ∧
      G.nodeCount ≤ rootCost sample.nodeCount (X 0 * X 1 : MvPolynomial (Fin 2) ℚ).totalDegree := by
  refine exists_formula_of_root productDepth_sample (fun h => ?_) ?_
  · have h1 := congrArg (eval ![0, 0, 1]) h
    simp [polynomial_sample] at h1
  · have h2 : (Fin.lastCases (X 0 * X 1) X : Fin 3 → MvPolynomial (Fin 2) ℚ) 2 = X 0 * X 1 :=
      Fin.lastCases_last (n := 2)
    have h0 : (Fin.lastCases (X 0 * X 1) X : Fin 3 → MvPolynomial (Fin 2) ℚ) 0 = X 0 :=
      Fin.lastCases_castSucc (n := 2) 0
    have h1 : (Fin.lastCases (X 0 * X 1) X : Fin 3 → MvPolynomial (Fin 2) ℚ) 1 = X 1 :=
      Fin.lastCases_castSucc (n := 2) 1
    simp [polynomial_sample, h0, h1, h2]

end CslibFrontierTests.RootFormula
