/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.Bihomogeneous
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A rank measure from differentiation and multiplication

Split the variables into a set `s` and its complement. A polynomial `g` and a bidegree `km`
give the operator `MvPolynomial.mixedOp s` of the component of `g` of bidegree `km`: it
differentiates in the variables in `s` and multiplies by the others. The measure
`MvPolynomial.rankMeasure s km ab g` is the rank of this operator on the polynomials of bidegree
`ab`. This is the measure `R(g) = rank F_g` of [OpenAI, §2][OpenAI2026DepthFive].

The measure is subadditive and does not grow under scaling, because the operator is linear in
`g`. For a product `Q * P` with `P` of bidegree `(i, j)`, the operator factors through the
polynomials of bidegree `(a - i, b + j)`, so its rank on bidegree `(a, b)` is at most the
dimension of that slice. This is the factorization step of
[OpenAI, Lemma 3.1][OpenAI2026DepthFive].

## Main definitions

* `MvPolynomial.rankMeasure`: the rank of `g_[km](∂_s, X_{sᶜ})` on a bihomogeneous slice.

## Main results

* `MvPolynomial.rankMeasure_sum_le`: the measure is subadditive.
* `MvPolynomial.finrank_map_mixedOp_mul_le`: the operator of a product factors through an
  intermediate slice.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §2 and Lemma 3.1 (unrefereed preprint)
-/

@[expose] public section

namespace MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ] (s : σ → Prop) [DecidablePred s]

/-- The rank of the operator `g_[km](∂_s, X_{sᶜ})` on the polynomials of bidegree `ab`, where
`g_[km]` is the component of `g` of bidegree `km`. -/
noncomputable def rankMeasure (km ab : ℕ × ℕ) (g : MvPolynomial σ K) : ℕ :=
  Module.finrank K ((weightedHomogeneousSubmodule K (bidegWeight s) ab).map
    (mixedOp s (weightedHomogeneousComponent (bidegWeight s) km g)))

variable {s} {km ab : ℕ × ℕ}

private instance (f : Module.End K (MvPolynomial σ K)) :
    Module.Finite K ((weightedHomogeneousSubmodule K (bidegWeight s) ab).map f) :=
  have : Module.Finite K (weightedHomogeneousSubmodule K (bidegWeight s) ab) :=
    finite_bihomogeneous s ab.1 ab.2
  Module.Finite.map _ f

@[simp]
theorem rankMeasure_zero : rankMeasure s km ab (0 : MvPolynomial σ K) = 0 := by
  simp [rankMeasure, Submodule.map_zero]

theorem rankMeasure_add_le (g h : MvPolynomial σ K) :
    rankMeasure s km ab (g + h) ≤ rankMeasure s km ab g + rankMeasure s km ab h := by
  rw [rankMeasure, map_add, map_add]
  exact (Submodule.finrank_mono (Submodule.map_add_le _ _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rankMeasure_smul_le (c : K) (g : MvPolynomial σ K) :
    rankMeasure s km ab (c • g) ≤ rankMeasure s km ab g := by
  rw [rankMeasure, map_smul, map_smul]
  refine Submodule.finrank_mono ?_
  rintro _ ⟨p, hp, rfl⟩
  exact Submodule.smul_mem _ c (Submodule.mem_map_of_mem hp)

/-- The measure is subadditive. -/
theorem rankMeasure_sum_le {ι : Type*} (t : Finset ι) (g : ι → MvPolynomial σ K) :
    rankMeasure s km ab (∑ i ∈ t, g i) ≤ ∑ i ∈ t, rankMeasure s km ab (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rankMeasure_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- The operator of a product `Q * P`, with `P` of bidegree `(i, j)`, factors through the
polynomials of bidegree `(a, b + j)` when applied to bidegree `(a + i, b)`. -/
theorem finrank_map_mixedOp_mul_le {P : MvPolynomial σ K} {i j : ℕ}
    (hP : P.IsWeightedHomogeneous (bidegWeight s) (i, j)) (Q : MvPolynomial σ K) (a b : ℕ) :
    Module.finrank K ((weightedHomogeneousSubmodule K (bidegWeight s) (a + i, b)).map
        (mixedOp s (Q * P))) ≤
      Module.finrank K (weightedHomogeneousSubmodule K (bidegWeight s) (a, b + j)) := by
  have h : (weightedHomogeneousSubmodule K (bidegWeight s) (a + i, b)).map (mixedOp s (Q * P)) ≤
      (weightedHomogeneousSubmodule K (bidegWeight s) (a, b + j)).map (mixedOp s Q) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [map_mul, Module.End.mul_apply]
    exact Submodule.mem_map_of_mem (mixedOp_mem_bihomogeneous hP hp)
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_map_le _ _)

end MvPolynomial
