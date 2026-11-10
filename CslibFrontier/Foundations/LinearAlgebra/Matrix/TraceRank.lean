/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, a rank lower bound from two trace moments)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# A rank lower bound from two trace moments

For a real matrix `A`, the Gram matrix `H = Aᵀ * A` is symmetric of the same rank as `A`, with
real eigenvalues. Its trace is the sum of the nonzero eigenvalues and the trace of `H * H` is the
sum of their squares, so the Cauchy–Schwarz inequality gives
`(tr H) ^ 2 ≤ rank A * tr (H * H)` (`Matrix.sq_trace_le_rank_mul_trace_sq`). This bounds the rank
of `A` from below by the first two trace moments of `H`. It is the rank bound in the proof of
[OpenAI, Proposition 4.1][OpenAI2026DepthFive], stated there with the conjugate transpose.

## Main results

* `Matrix.sq_trace_le_rank_mul_trace_sq`: `(tr AᵀA) ^ 2 ≤ rank A * tr ((AᵀA) * (AᵀA))`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §5 (unrefereed preprint)
-/

public section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The square of the trace of the Gram matrix `Aᵀ * A` is at most the rank of `A` times the
trace of the square of the Gram matrix. -/
theorem sq_trace_le_rank_mul_trace_sq (A : Matrix m n ℝ) :
    (Aᵀ * A).trace ^ 2 ≤ A.rank * ((Aᵀ * A) * (Aᵀ * A)).trace := by
  classical
  have hH : (Aᵀ * A).IsHermitian := by simpa using isHermitian_conjTranspose_mul_self A
  have hs := hH.spectral_theorem
  have hconj (X : Matrix n n ℝ) :
      (Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary X).trace = X.trace := by
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have h₁ : (Aᵀ * A).trace = ∑ i, hH.eigenvalues i := by
    simpa using hH.trace_eq_sum_eigenvalues
  have h₂ : ((Aᵀ * A) * (Aᵀ * A)).trace = ∑ i, hH.eigenvalues i ^ 2 := by
    have h : (Aᵀ * A) * (Aᵀ * A) = Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
          diagonal (RCLike.ofReal ∘ hH.eigenvalues)) := by
      rw [map_mul, ← hs]
    rw [h, hconj, diagonal_mul_diagonal, trace_diagonal]
    simp [sq]
  have hr : A.rank = (Finset.univ.filter fun i => hH.eigenvalues i ≠ 0).card := by
    rw [← rank_transpose_mul_self, hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  rw [h₁, h₂, hr, ← Finset.sum_filter_ne_zero]
  refine sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => sq_nonneg _

end Matrix
