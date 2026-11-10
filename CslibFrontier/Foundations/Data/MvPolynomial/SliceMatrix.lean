/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, matrices of operators between weighted homogeneous slices)

public import CslibFrontier.Foundations.Data.MvPolynomial.Bihomogeneous
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrices of operators between weighted homogeneous slices

An endomorphism `T` of the polynomial ring that maps the polynomials of weight `m` to the
polynomials of weight `m'` has a matrix in the monomial bases of these two slices,
`MvPolynomial.sliceMatrix w m' m T`. Over a field, the rank of this matrix is the dimension of
the image of the slice of weight `m`. For the operators `MvPolynomial.mixedOp s Q` the matrix
commutes with a change of the coefficient ring, which is the comparison between fields of
characteristic zero in [OpenAI, §6][OpenAI2026DepthFive].

## Main definitions

* `MvPolynomial.sliceMatrix`: the matrix of an endomorphism between two slices.

## Main results

* `MvPolynomial.rank_sliceMatrix`: its rank is the dimension of the image of the slice.
* `MvPolynomial.sliceMatrix_mixedOp_map`: naturality in the coefficient ring.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §6 (unrefereed preprint)
-/

@[expose] public section

open Finsupp

namespace MvPolynomial

variable {R S K σ M : Type*} [CommSemiring R] [CommSemiring S] [Field K] [AddCommMonoid M]
  (w : σ → M) (m' m : M)

/-- The matrix of an endomorphism of the polynomial ring between the slices of weights `m` and
`m'`, in the monomial bases: the entry `(N, D)` is the coefficient of the monomial `N` in the
image of the monomial `D`. -/
noncomputable def sliceMatrix (T : Module.End R (MvPolynomial σ R)) :
    Matrix {d : σ →₀ ℕ // weight w d = m'} {d : σ →₀ ℕ // weight w d = m} R :=
  Matrix.of fun N D => (T (monomial D.1 1)).coeff N.1

/-- The rank of the matrix of an operator that maps weight `m` to weight `m'` is the dimension
of the image of the slice of weight `m`. -/
theorem rank_sliceMatrix [Fintype {d : σ →₀ ℕ // weight w d = m}]
    (T : Module.End K (MvPolynomial σ K))
    (hT : ∀ p ∈ weightedHomogeneousSubmodule K w m, T p ∈ weightedHomogeneousSubmodule K w m') :
    (sliceMatrix w m' m T).rank =
      Module.finrank K ((weightedHomogeneousSubmodule K w m).map T) := by
  classical
  let φ : MvPolynomial σ K →ₗ[K] ({d : σ →₀ ℕ // weight w d = m'} → K) :=
    LinearMap.pi fun N => lcoeff K N.1
  have hcols : Set.range (sliceMatrix w m' m T).col =
      (φ ∘ₗ T) '' Set.range fun D : {d : σ →₀ ℕ // weight w d = m} => monomial D.1 (1 : K) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun D => funext fun N => rfl)
  have hinj : Function.Injective
      (φ.submoduleMap ((weightedHomogeneousSubmodule K w m).map T)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, p, hp, rfl⟩ h
    refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
    by_cases hd : weight w d = m'
    · exact congrFun (congrArg Subtype.val h) ⟨d, hd⟩
    · exact (hT p hp).coeff_eq_zero d hd
  rw [Matrix.rank_eq_finrank_span_cols, hcols, ← Submodule.map_span,
    ← weightedHomogeneousSubmodule_eq_span, Submodule.map_comp]
  exact (LinearEquiv.ofBijective _ ⟨hinj, LinearMap.submoduleMap_surjective _ _⟩).finrank_eq.symm

variable (s : σ → Prop) [DecidablePred s]

/-- The matrix of the operator `Q(∂_s, X_{sᶜ})` commutes with a change of coefficient ring. -/
theorem sliceMatrix_mixedOp_map (f : R →+* S) (Q : MvPolynomial σ R) :
    sliceMatrix w m' m (mixedOp s (map f Q)) = (sliceMatrix w m' m (mixedOp s Q)).map f := by
  ext N D
  simp only [sliceMatrix, Matrix.map_apply, Matrix.of_apply]
  rw [← coeff_map, mixedOp_map, map_monomial, f.map_one]

end MvPolynomial
