/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, chain rule for formal partial derivatives and Hessians)

public import CslibFrontier.Foundations.Data.MvPolynomial.Hessian
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Finsupp.Weight

/-!
# The chain rule for formal Hessians

Substituting polynomials `L k` for the variables of `p` transforms partial derivatives by the
chain rule `∂ᵢ (p ∘ L) = ∑ₖ (∂ₖ p ∘ L) · ∂ᵢ Lₖ`. At a point `x`, the Hessian of `p ∘ L` is
`Jᵀ · Hess p (L x) · J` plus the Hessians of the `L k` weighted by the gradient of `p`, where `J`
is the Jacobian of `L` at `x`. An affine substitution (each `L k` of total degree at most one)
has vanishing Hessians, so it can only lower the rank of the Hessian. No assumption on the
characteristic is needed; the rank statement is over a field.

## Main results

* `MvPolynomial.pderiv_aeval`: the chain rule for formal partial derivatives.
* `MvPolynomial.hessian_aeval`: the chain rule for Hessians at a point.
* `MvPolynomial.hessian_eq_zero_of_totalDegree_le_one`: affine polynomials have zero Hessian.
* `MvPolynomial.rank_hessian_aeval_le`: an affine substitution does not increase Hessian rank.

## References

* The rank comparison is the chain-rule step of the Mignon–Ressayre argument
  [Mignon and Ressayre][MignonRessayre2004], in the exposition of
  [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], chapter "Determinantal Complexity Lower Bounds".
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- **Chain rule** for formal partial derivatives under polynomial substitution. -/
theorem pderiv_aeval [Fintype τ] (L : τ → MvPolynomial σ R) (p : MvPolynomial τ R) (i : σ) :
    pderiv i (aeval L p) = ∑ k, aeval L (pderiv k p) * pderiv i (L k) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hk : ∑ l, aeval L (pderiv l (X k : MvPolynomial τ R)) * pderiv i (L l) =
        pderiv i (L k) := by
      simp [pderiv_X, Pi.single_apply]
    rw [map_mul, aeval_X, pderiv_mul, hp]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul]
    rw [← hk, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => by ring)
      (Finset.sum_congr rfl fun l _ => by ring)

/-- Evaluating a substitution at `x` evaluates the substituted polynomial at the values of the
substituted polynomials. -/
theorem eval_aeval (x : σ → R) (L : τ → MvPolynomial σ R) (q : MvPolynomial τ R) :
    eval x (aeval L q) = eval (fun k => eval x (L k)) q := by
  rw [aeval_eq_bind₁]
  exact eval₂Hom_bind₁ _ _ _ _

/-- **Chain rule for Hessians**: at `x`, the Hessian of `p ∘ L` is `Jᵀ · Hess p (L x) · J` plus
the Hessians of the `L k` weighted by the gradient of `p` at `L x`, where `J` is the Jacobian of
`L` at `x`. -/
theorem hessian_aeval [Fintype τ] (x : σ → R) (L : τ → MvPolynomial σ R)
    (p : MvPolynomial τ R) :
    hessian x (aeval L p) =
      (Matrix.of fun k i => gradient x (L k) i).transpose * hessian (fun k => eval x (L k)) p *
          Matrix.of (fun k i => gradient x (L k) i) +
        ∑ k, gradient (fun k => eval x (L k)) p k • hessian x (L k) := by
  ext i j
  simp only [hessian, gradient, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [pderiv_aeval, pderiv_mul, map_add, map_mul, map_sum, eval_aeval,
    Finset.sum_add_distrib, Finset.sum_mul]
  refine congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_) rfl
  ring

/-- A polynomial of total degree at most one has zero Hessian at every point. -/
theorem hessian_eq_zero_of_totalDegree_le_one (x : σ → R) {p : MvPolynomial σ R}
    (hp : p.totalDegree ≤ 1) : hessian x p = 0 := by
  classical
  ext i j
  have : pderiv i (pderiv j p) = 0 := by
    ext m
    rw [coeff_pderiv, coeff_pderiv, coeff_eq_zero_of_totalDegree_lt, zero_mul, zero_mul]
    · rfl
    refine lt_of_le_of_lt hp ?_
    change 1 < Finsupp.degree (m + Finsupp.single i 1 + Finsupp.single j 1)
    rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega
  simp [hessian, this]

/-- Multiplying by a constant scales the Hessian. -/
theorem hessian_mul_C (x : σ → R) (p : MvPolynomial σ R) (c : R) :
    hessian x (p * C c) = c • hessian x p := by
  ext i j
  simp only [hessian, Matrix.smul_apply, smul_eq_mul, mul_comm p, pderiv_C_mul, map_mul, eval_C]

/-- An affine substitution does not increase the rank of the Hessian: the Hessian of `p ∘ L` at
`x` has rank at most that of the Hessian of `p` at `L x`. -/
theorem rank_hessian_aeval_le {K : Type*} [Field K] [Fintype σ] [Fintype τ] (x : σ → K)
    (L : τ → MvPolynomial σ K) (hL : ∀ k, (L k).totalDegree ≤ 1) (p : MvPolynomial τ K) :
    (hessian x (aeval L p)).rank ≤ (hessian (fun k => eval x (L k)) p).rank := by
  rw [hessian_aeval, Finset.sum_eq_zero fun k _ => by
    rw [hessian_eq_zero_of_totalDegree_le_one x (hL k), smul_zero], add_zero]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end MvPolynomial
