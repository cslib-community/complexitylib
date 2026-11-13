/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, weighted homogeneous components under monomial substitution)

public import CslibFrontier.Init
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneous components and monomial substitutions

Substituting the monomial `b v • y ^ w v` for every variable `v` of a polynomial `G` gives a
polynomial in `y` whose coefficients are the values at `b` of the weighted homogeneous
components of `G` for the weight `w`. So a weighted homogeneous component can be read off
coefficientwise from a substitution into `G` itself.

## Main results

* `MvPolynomial.coeff_aeval_monomial`: the coefficient at `n` of `G (b v • y ^ w v)` is the
  value at `b` of the component of `G` of weighted degree `n`.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- Substituting the monomial `b v • y ^ w v` for every variable `v` of a polynomial gives a
polynomial in `y` whose coefficient at `n` is the value at `b` of the weighted homogeneous
component of weighted degree `n`, for the weight `w`. -/
theorem coeff_aeval_monomial (w : σ → τ →₀ ℕ) (b : σ → R) (G : MvPolynomial σ R)
    (n : τ →₀ ℕ) :
    (aeval (fun v => monomial (w v) (b v)) G).coeff n =
      eval b (weightedHomogeneousComponent w n G) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial d a =>
    have h : aeval (fun v => monomial (w v) (b v)) (monomial d a) =
        monomial (Finsupp.weight w d) (a * d.prod fun v k => b v ^ k) := by
      rw [aeval_monomial, Finsupp.weight_apply, ← C_mul_monomial, algebraMap_eq]
      simp only [Finsupp.prod, Finsupp.sum, monomial_pow, monomial_sum_prod]
    rw [h, coeff_monomial,
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial w d a rfl)]
    by_cases hn : Finsupp.weight w d = n
    · simp [hn, eval_monomial]
    · simp [hn, Ne.symm hn]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, ← hp, ← hq]
    rfl

end MvPolynomial
