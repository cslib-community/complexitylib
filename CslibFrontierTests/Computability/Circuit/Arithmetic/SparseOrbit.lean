/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SparseOrbit

/-!
# Hitting sets for sparse affine orbits

The square `(X 0 + X 1) ^ 2` over the rationals has three monomials, but it is the monomial
`X 0 ^ 2` after an invertible linear change of variables. So it lies in the affine orbit of the
polynomials with one monomial and is nonzero at one of the at most `65` points of the hitting set
for this orbit in degree two.
-/

public section

namespace CslibFrontierTests.SparseOrbit

open Cslib.Circuits.Arithmetic MvPolynomial

/-- `(X 0 + X 1) ^ 2` is `p (A x + b)` for the monomial `p = X 0 ^ 2`, an invertible matrix `A`
and `b = 0`. -/
theorem X_add_X_sq_mem :
    ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℚ) ∈
      {f | f.totalDegree ≤ 2 ∧ ∃ (p : MvPolynomial (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℚ)
        (b : Fin 2 → ℚ), p.support.card ≤ 1 ∧ IsUnit A.det ∧
          f = aeval (fun i => ∑ j, C (A i j) * X j + C (b i)) p} := by
  refine ⟨?_, X 0 ^ 2, !![1, 1; 0, 1], 0, ?_, ?_, ?_⟩
  · refine (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 ?_ : _ ≤ 2 * 1)
    refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;> rw [totalDegree_X]
  · rw [X_pow_eq_monomial]
    exact (Finset.card_le_card support_monomial_subset).trans (Finset.card_singleton _).le
  · simp [Matrix.det_fin_two]
  · simp [Fin.sum_univ_two]

/-- The hitting set for one monomial in two variables and degree two has at most `65` points. -/
theorem card_sparseOrbitHittingSet_le_65 : (sparseOrbitHittingSet ℚ 2 1 2).card ≤ 65 :=
  card_sparseOrbitHittingSet_le 1 2

/-- The hitting set contains a point where `(X 0 + X 1) ^ 2` is nonzero. -/
theorem exists_eval_X_add_X_sq_ne_zero :
    ∃ a ∈ sparseOrbitHittingSet ℚ 2 1 2,
      eval a ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℚ) ≠ 0 :=
  isHittingSet_sparseOrbitHittingSet 1 2 _ X_add_X_sq_mem
    (pow_ne_zero 2 fun h => by
      have h1 := congrArg (eval fun _ => (1 : ℚ)) h
      norm_num at h1)

end CslibFrontierTests.SparseOrbit
