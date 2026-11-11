/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.RankMeasure
public import CslibFrontier.Foundations.Data.MvPolynomial.SliceMatrix
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# The rank measure under a change of field

The rank measure `MvPolynomial.rankMeasure` of a polynomial is the rank of the matrix of its
operator in the monomial bases of two bihomogeneous slices. The entries of this matrix are
polynomial expressions with integer coefficients in the coefficients of the polynomial, so the
measure does not change when the polynomial is mapped to a larger field. This is the transfer
of the rank lower bound for `IMM` from the complex numbers to every field of characteristic
zero in [OpenAI, §6][OpenAI2026DepthFive].

## Main results

* `MvPolynomial.rankMeasure_eq_rank_sliceMatrix`: the measure is the rank of a matrix.
* `MvPolynomial.rankMeasure_map`: the measure is invariant under a field extension.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §6 (unrefereed preprint)
-/

public section

open Finsupp

namespace MvPolynomial

variable {K L σ : Type*} [Field K] [Field L] {s : σ → Prop} [DecidablePred s]

/-- The rank measure is the rank of the matrix of the operator in the monomial bases. -/
theorem rankMeasure_eq_rank_sliceMatrix (i j a b : ℕ)
    [Fintype {d : σ →₀ ℕ // weight (bidegWeight s) d = (a + i, b)}] (g : MvPolynomial σ K) :
    rankMeasure s (i, j) (a + i, b) g =
      (sliceMatrix (bidegWeight s) (a, b + j) (a + i, b)
        (mixedOp s (weightedHomogeneousComponent (bidegWeight s) (i, j) g))).rank :=
  (rank_sliceMatrix _ _ _ _ fun _ hp => mixedOp_mem_bihomogeneous
    (weightedHomogeneousComponent_isWeightedHomogeneous (i, j) g) hp).symm

/-- The rank measure does not change under a field extension. -/
theorem rankMeasure_map [Finite σ] (f : K →+* L) (i j a b : ℕ) (g : MvPolynomial σ K) :
    rankMeasure s (i, j) (a + i, b) (map f g) = rankMeasure s (i, j) (a + i, b) g := by
  have := Fintype.ofFinite {d : σ →₀ ℕ // weight (bidegWeight s) d = (a + i, b)}
  rw [rankMeasure_eq_rank_sliceMatrix, rankMeasure_eq_rank_sliceMatrix,
    weightedHomogeneousComponent_map, sliceMatrix_mixedOp_map, Matrix.rank_map_of_field]

end MvPolynomial
