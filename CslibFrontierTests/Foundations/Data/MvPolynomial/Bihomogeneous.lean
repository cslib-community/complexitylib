/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.Bihomogeneous

/-!
# Bihomogeneous polynomials

In three variables with the variable `0` distinguished, the slice of bidegree `(1, 2)` has
dimension `3`, with basis `X 0 * X 1 ^ 2`, `X 0 * X 1 * X 2` and `X 0 * X 2 ^ 2`. The operator of
`X 0 * X 1` maps bidegree `(1, 2)` to bidegree `(0, 3)`.
-/

public section

open MvPolynomial

namespace CslibFrontierTests.Bihomogeneous

abbrev s : Fin 3 → Prop := (· = 0)

/-- The slice of bidegree `(1, 2)` in three variables, one of them distinguished. -/
theorem finrank_slice :
    Module.finrank ℚ (weightedHomogeneousSubmodule ℚ (bidegWeight s) (1, 2)) = 3 := by
  rw [finrank_bihomogeneous, Fintype.card_subtype, Fintype.card_subtype]
  simp [s, Finset.filter_eq', Finset.filter_ne', Nat.multichoose_eq]

example (p : MvPolynomial (Fin 3) ℚ)
    (hp : p ∈ weightedHomogeneousSubmodule ℚ (bidegWeight s) (1, 2)) :
    mixedOp s (X 0 * X 1) p ∈ weightedHomogeneousSubmodule ℚ (bidegWeight s) (0, 3) := by
  have hQ := (isWeightedHomogeneous_X (R := ℚ) (bidegWeight s) 0).mul
    (isWeightedHomogeneous_X (R := ℚ) (bidegWeight s) 1)
  exact mixedOp_mem_bihomogeneous (i := 1) (j := 1) (by simpa [bidegWeight, s] using hQ) hp

end CslibFrontierTests.Bihomogeneous
