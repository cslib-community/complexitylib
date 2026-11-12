/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.TruncateTotalDegree

/-!
# Total-degree truncation over semirings

The cutoff remains computable and its linear-map interface works across module boundaries.
Over `ℕ`, degree-one polynomials are fixed while a quadratic term is changed.
-/

public section

open MvPolynomial

namespace CslibFrontierTests.MvPolynomialTruncation

private def keepLinear (p : MvPolynomial Unit ℕ) := truncateTotalDegree 1 p

example (p q : MvPolynomial Unit ℕ) :
    keepLinear (p + q) = keepLinear p + keepLinear q := by
  simpa only [truncateTotalDegreeₗ_apply, keepLinear] using
    (truncateTotalDegreeₗ (V := Unit) (R := ℕ) 1).map_add p q

example : keepLinear (X ()) = X () :=
  truncateTotalDegree_eq_self (by simp)

/-- Total-degree truncation at one changes a quadratic monomial. -/
theorem quadratic_not_fixed :
    truncateTotalDegree 1 (X () ^ 2 : MvPolynomial Unit ℕ) ≠ X () ^ 2 := by
  rw [ne_eq, truncateTotalDegree_eq_self_iff]
  simp

end CslibFrontierTests.MvPolynomialTruncation
