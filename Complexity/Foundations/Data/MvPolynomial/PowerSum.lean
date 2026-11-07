/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, partial derivatives of power sums)

public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Partial derivatives of power sums

The partial derivative of the power sum `psum σ R (d + 1) = ∑ j, X j ^ (d + 1)` along `X i` is
`(d + 1) * X i ^ d` (`MvPolynomial.pderiv_psum_succ`).

## Main results

* `MvPolynomial.pderiv_psum_succ`: the gradient of a power sum is a scaled power map.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] [Fintype σ]

/-- The partial derivative of `∑ j, X j ^ (d + 1)` along `X i` is `(d + 1) * X i ^ d`. -/
theorem pderiv_psum_succ (d : ℕ) (i : σ) :
    pderiv i (psum σ R (d + 1)) = (d + 1 : MvPolynomial σ R) * X i ^ d := by
  classical
  rw [psum, map_sum, Finset.sum_eq_single i (fun k _ hk => by rw [pderiv_pow, pderiv_X_of_ne hk,
    mul_zero]) (fun h => absurd (Finset.mem_univ i) h), pderiv_pow, pderiv_X_self,
    Nat.add_sub_cancel, mul_one]
  push_cast
  ring

end MvPolynomial
