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

Over `ℚ`, at product-depth one, exponent one and `t = 1`: for all large `n`, the hitting set
`constantDepthHittingSet ℚ 1 1 n` hits the formulas of product-depth one with at most `n` nodes
and has at most `2 ^ n` points, and `constantDepthHittingSet ℚ 9 1 n` hits the simple circuits of
product-depth one with at most `n` gates.
-/

@[expose] public section

namespace CslibFrontierTests.ConstantDepthHittingSet

open Cslib.Circuits Cslib.Circuits.Arithmetic Filter

/-- The hitting set at exponent one and `t = 1`, a finite set of points of `ℚⁿ`. -/
noncomputable def sample (n : ℕ) : Finset (Fin n → ℚ) :=
  constantDepthHittingSet ℚ 1 1 n

/-- For large `n`, it hits the formulas of product-depth one with at most `n` nodes. -/
theorem eventually_isHittingSet_sample :
    ∀ᶠ n in atTop, IsHittingSet (sample n)
      {p | ∃ C : SPFormula ℚ n, C.polynomial = p ∧ C.productDepth ≤ 1 ∧ C.nodeCount ≤ n ^ 1} :=
  eventually_isHittingSet_constantDepthHittingSet ℚ 1 1 1 le_rfl

/-- For large `n`, it has at most `2 ^ n` points. -/
theorem eventually_card_sample_le :
    ∀ᶠ n in atTop, ((sample n).card : ℝ) ≤ 2 ^ ((n : ℝ) ^ (1 / (1 : ℕ) : ℝ)) :=
  eventually_card_constantDepthHittingSet_le ℚ 1 1 le_rfl

/-- For large `n`, the hitting set at exponent `(1 + 2) (2 + 1) = 9` hits the simple circuits of
product-depth one with at most `n` gates. -/
theorem eventually_isHittingSet_circuit :
    ∀ᶠ n in atTop, IsHittingSet (constantDepthHittingSet ℚ 9 1 n)
      {p | ∃ C : SPCircuit ℚ n, C.IsSimple ∧ C.polynomial = p ∧ C.productDepth ≤ 1 ∧
        C.size ≤ n ^ 1} :=
  eventually_isHittingSet_constantDepthHittingSet_circuit ℚ 1 1 1 le_rfl

end CslibFrontierTests.ConstantDepthHittingSet
