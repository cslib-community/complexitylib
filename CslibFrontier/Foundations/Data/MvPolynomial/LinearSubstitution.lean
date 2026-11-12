/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, linear substitutions in multivariate polynomials)

public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Linear substitutions

`MvPolynomial.linearSubst A` is the substitution `f ↦ f (A x)` of the linear forms
`∑ j, A i j * X j` for the variables. Substitutions compose as matrices multiply, so the
substitution of an invertible matrix is injective. By the chain rule, a linear substitution maps
a space of polynomials closed under partial derivatives to such a space.

## Main definitions

* `MvPolynomial.linearSubst`: the algebra homomorphism `f ↦ f (A x)`.

## Main results

* `MvPolynomial.linearSubst_linearSubst`: substitutions compose as matrices multiply.
* `MvPolynomial.linearSubst_injective`: the substitution of an invertible matrix is injective.
* `MvPolynomial.pderiv_linearSubst`: the chain rule.
* `MvPolynomial.pderiv_mem_map_linearSubst`: the image of a derivative-closed space is
  derivative-closed.
-/

@[expose] public section

namespace MvPolynomial

variable {σ τ υ R : Type*}

section CommSemiring

variable [CommSemiring R] [Fintype τ]

/-- The linear substitution `f ↦ f (A x)`, replacing the variable `X i` by `∑ j, A i j * X j`. -/
noncomputable def linearSubst (A : Matrix σ τ R) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval fun i => ∑ j, C (A i j) * X j

/-- Linear substitutions compose as matrices multiply. -/
theorem linearSubst_linearSubst [Fintype υ] (A : Matrix σ τ R) (B : Matrix τ υ R)
    (p : MvPolynomial σ R) : linearSubst B (linearSubst A p) = linearSubst (A * B) p := by
  rw [linearSubst, linearSubst, linearSubst, comp_aeval_apply]
  refine congrArg (fun L => aeval L p) (funext fun i => ?_)
  simp only [map_sum, map_mul, algHom_C, aeval_X, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- The substitution of the identity matrix is the identity. -/
theorem linearSubst_one [DecidableEq τ] (p : MvPolynomial τ R) :
    linearSubst (1 : Matrix τ τ R) p = p := by
  rw [linearSubst]
  simpa [Matrix.one_apply] using aeval_X_left_apply p

/-- The chain rule for a linear substitution. -/
theorem pderiv_linearSubst [Fintype σ] (A : Matrix σ τ R) (p : MvPolynomial σ R) (j : τ) :
    pderiv j (linearSubst A p) = ∑ i, A i j • linearSubst A (pderiv i p) := by
  classical
  have hd (i : σ) : pderiv j (∑ k, C (A i k) * X k) = C (A i j) := by
    simp only [map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp
  rw [linearSubst, pderiv_aeval]
  exact Finset.sum_congr rfl fun i _ => by rw [hd i, smul_eq_C_mul, mul_comm]

/-- A linear substitution maps a space closed under partial derivatives to such a space. -/
theorem pderiv_mem_map_linearSubst [Finite σ] (A : Matrix σ τ R)
    {V : Submodule R (MvPolynomial σ R)} (hV : ∀ i, ∀ p ∈ V, pderiv i p ∈ V) (j : τ)
    {q : MvPolynomial τ R} (hq : q ∈ V.map (linearSubst A).toLinearMap) :
    pderiv j q ∈ V.map (linearSubst A).toLinearMap := by
  have := Fintype.ofFinite σ
  obtain ⟨p, hp, rfl⟩ := hq
  rw [AlgHom.toLinearMap_apply, pderiv_linearSubst]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hV i p hp))

end CommSemiring

/-- The linear substitution of an invertible matrix is injective. -/
theorem linearSubst_injective [CommRing R] [Fintype τ] [DecidableEq τ] {A : Matrix τ τ R}
    (hA : IsUnit A.det) : Function.Injective (linearSubst A) :=
  Function.LeftInverse.injective (g := linearSubst A⁻¹) fun p => by
    rw [linearSubst_linearSubst, Matrix.mul_nonsing_inv _ hA, linearSubst_one]

end MvPolynomial
