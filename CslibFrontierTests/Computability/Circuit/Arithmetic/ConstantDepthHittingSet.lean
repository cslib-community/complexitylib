/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConstantDepth

/-!
# Subexponential hitting sets for constant-depth formulas

The formula `x₀ + x₁` over `ℚ`, in `n ≥ 2` variables, has product-depth zero and three nodes (a sum
gate with the edge constants `1, 1` over two inputs), at most `n ^ 2` once `n ≥ 2`. So for all large
`n` the hitting set for exponent `2` and `ε = 1 / 2` contains a point at which `x₀ + x₁` does not
vanish, and it has at most `2 ^ √n` points. The circuit endpoint is instantiated at product-depth
one and `ε = 1 / 2`.
-/

@[expose] public section

namespace CslibFrontierTests.ConstantDepthHittingSet

open Cslib.Circuits Cslib.Circuits.Arithmetic Filter MvPolynomial

/-- The formula `x₀ + x₁` in `n` variables, for `n ≥ 2`. -/
def sumFormula {n : ℕ} (hn : 2 ≤ n) : SPFormula ℚ n :=
  SPFormula.add ![1, 1] ![.input ⟨0, by omega⟩, .input ⟨1, by omega⟩]

theorem polynomial_sumFormula {n : ℕ} (hn : 2 ≤ n) :
    (sumFormula hn).polynomial = X ⟨0, by omega⟩ + X ⟨1, by omega⟩ := by
  simp [sumFormula, SPFormula.polynomial, Fin.sum_univ_two]

theorem polynomial_sumFormula_ne_zero {n : ℕ} (hn : 2 ≤ n) : (sumFormula hn).polynomial ≠ 0 := by
  rw [polynomial_sumFormula]
  intro h
  have h1 := congrArg (eval fun _ => (1 : ℚ)) h
  norm_num at h1

/-- **A checked use of the endpoint.** For all large `n`, the hitting set for formulas of
product-depth zero with at most `n ^ 2` nodes, at `ε = 1 / 2`, has at most `2 ^ √n` points and
contains a point where `x₀ + x₁` is nonzero. -/
theorem eventually_exists_eval_sumFormula_ne_zero :
    ∀ᶠ n in atTop, ∃ hn : 2 ≤ n,
      ((constantDepthHittingSet ℚ 2 ⌈(1 / 2 : ℝ)⁻¹⌉₊ n).card : ℝ) ≤
        2 ^ ((n : ℝ) ^ (1 / 2 : ℝ)) ∧
      ∃ x ∈ constantDepthHittingSet ℚ 2 ⌈(1 / 2 : ℝ)⁻¹⌉₊ n,
        eval x (sumFormula hn).polynomial ≠ 0 := by
  filter_upwards [eventually_isHittingSet_constantDepthHittingSet_rpow ℚ 0 2
    (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop 2] with n hH hn
  refine ⟨hn, hH.2, hH.1 _ ⟨sumFormula hn, rfl, ?_, ?_⟩ (polynomial_sumFormula_ne_zero hn)⟩
  · simp [sumFormula, SPFormula.productDepth_add]
  · have h3 : 3 ≤ n ^ 2 := by nlinarith
    simpa [sumFormula, Formula.nodeCount_gate] using h3

/-- For large `n`, the hitting set at exponent `(1 + 2) (2 + 1) = 9` and `ε = 1 / 2` hits the
simple circuits of product-depth one with at most `n` gates and has at most `2 ^ √n` points. -/
theorem eventually_isHittingSet_circuit :
    ∀ᶠ n in atTop,
      IsHittingSet (constantDepthHittingSet ℚ 9 ⌈(1 / 2 : ℝ)⁻¹⌉₊ n)
        {p | ∃ C : SPCircuit ℚ n, C.IsSimple ∧ C.polynomial = p ∧ C.productDepth ≤ 1 ∧
          C.size ≤ n ^ 1} ∧
      ((constantDepthHittingSet ℚ 9 ⌈(1 / 2 : ℝ)⁻¹⌉₊ n).card : ℝ) ≤ 2 ^ ((n : ℝ) ^ (1 / 2 : ℝ)) :=
  eventually_isHittingSet_constantDepthHittingSet_circuit_rpow ℚ 1 1 (by norm_num)

end CslibFrontierTests.ConstantDepthHittingSet
