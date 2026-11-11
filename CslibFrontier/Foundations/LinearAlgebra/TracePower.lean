/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `Analysis/InnerProductSpace/Trace`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Trace
import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Traces of powers of positive operators

For a symmetric operator `T` on a finite-dimensional inner product space, the trace of `T ^ j` is
the sum of the `j`-th powers of the eigenvalues
(`LinearMap.IsSymmetric.re_trace_pow_eq_sum_eigenvalues`). For a positive operator the eigenvalues
are nonnegative, so `tr (T ^ j)` sits between the `j`-th power of the largest eigenvalue and `dim E`
times that power. The largest eigenvalue is the maximum of the quadratic form `⟪x, T x⟫` on unit
vectors. This gives two bounds that need no eigenvalues in their statements:

* if `c ≤ ⟪x, T x⟫` for some unit vector `x`, then `c ^ j ≤ tr (T ^ j)`
  (`LinearMap.IsPositive.pow_le_re_trace_pow`);
* if `⟪x, T x⟫ ≤ s` for every unit vector `x`, then `tr (T ^ j) ≤ dim E * s ^ j`
  (`LinearMap.IsPositive.re_trace_pow_le`).

For `c > s` and `j` large compared with `log (dim E) / log (c / s)`, the two ranges are disjoint,
so the trace of a power separates the two cases even though `dim E` is exponential in the
number of qubits. This is the matrix-analysis step behind the containment of QMA in PP. Any
operator of the form `B† B` is positive with quadratic form `‖B x‖ ^ 2`
(`LinearMap.re_inner_adjoint_comp_self_apply`); the acceptance probability of a quantum verifier is
such a form (`Cslib.Quantum.UniformVerifierFamily.re_inner_acceptOp`). In an
orthonormal basis the trace of a power is a sum over closed paths of products of matrix entries
(`LinearMap.trace_pow_eq_sum`), which is what a counting argument computes. See
[Marriott, Watrous][MarriottWatrous2005], Section 3, for the use of `tr Q` together with strong
error reduction.

## Main results

* `LinearMap.IsSymmetric.re_trace_pow_eq_sum_eigenvalues`: `tr (T ^ j) = ∑ λᵢ ^ j`.
* `LinearMap.IsSymmetric.re_inner_apply_eq_sum`: the quadratic form in an eigenbasis.
* `LinearMap.IsPositive.pow_le_re_trace_pow`, `LinearMap.IsPositive.re_trace_pow_le`: the two
  trace bounds.
* `LinearMap.re_inner_adjoint_comp_self_apply`: the quadratic form of `B† B` is `‖B x‖ ^ 2`.
* `LinearMap.trace_pow_eq_sum`: the trace of a power in an orthonormal basis, as a sum over closed
  paths.

## References

* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
-/

public section

open Finset Module
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The quadratic form of `B† B` is the squared norm of `B`. -/
theorem re_inner_adjoint_comp_self_apply [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (B : E →ₗ[𝕜] F) (x : E) : RCLike.re ⟪x, (B.adjoint ∘ₗ B) x⟫_𝕜 = ‖B x‖ ^ 2 := by
  rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq]

/-- **The trace of a power in an orthonormal basis, as a sum over closed paths**: `tr (T ^ d)` is
the sum, over the index paths `p : Fin (d + 1) → ι` with `p 0 = p d`, of the products of the matrix
entries `⟪b (p i), T (b (p (i + 1)))⟫` along the path. -/
theorem trace_pow_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E)
    (T : E →ₗ[𝕜] E) (d : ℕ) :
    trace 𝕜 E (T ^ d) = ∑ p : Fin (d + 1) → ι,
      if p 0 = p (Fin.last d) then ∏ i : Fin d, ⟪b (p i.castSucc), T (b (p i.succ))⟫_𝕜 else 0 := by
  rw [trace_eq_matrix_trace 𝕜 b.toBasis, ← toMatrix_pow, Matrix.trace_pow_eq_sum]
  simp only [toMatrix_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]

variable [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} {N : ℕ} (hN : finrank 𝕜 E = N)

namespace IsSymmetric

/-- A power of `T` scales an eigenvector by the power of its eigenvalue. -/
theorem pow_apply_eigenvectorBasis (hT : T.IsSymmetric) (j : ℕ) (i : Fin N) :
    (T ^ j) (hT.eigenvectorBasis hN i) =
      ((hT.eigenvalues hN i : 𝕜) ^ j) • hT.eigenvectorBasis hN i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hT.apply_eigenvectorBasis, smul_smul,
      ← pow_succ]

/-- **The trace of a power of a symmetric operator is the sum of the powers of its
eigenvalues.** -/
theorem trace_pow_eq_sum_eigenvalues (hT : T.IsSymmetric) (j : ℕ) :
    trace 𝕜 E (T ^ j) = ∑ i, ((hT.eigenvalues hN i : 𝕜) ^ j) := by
  rw [trace_eq_sum_inner _ (hT.eigenvectorBasis hN)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT.pow_apply_eigenvectorBasis hN, inner_smul_right, inner_self_eq_norm_sq_to_K,
    OrthonormalBasis.norm_eq_one]
  simp

/-- The real part of `tr (T ^ j)` is the sum of the `j`-th powers of the eigenvalues. -/
theorem re_trace_pow_eq_sum_eigenvalues (hT : T.IsSymmetric) (j : ℕ) :
    RCLike.re (trace 𝕜 E (T ^ j)) = ∑ i, hT.eigenvalues hN i ^ j := by
  rw [hT.trace_pow_eq_sum_eigenvalues hN, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- An eigenvalue is the quadratic form at its unit eigenvector. -/
theorem eigenvalues_eq_re_inner (hT : T.IsSymmetric) (i : Fin N) :
    hT.eigenvalues hN i =
      RCLike.re ⟪hT.eigenvectorBasis hN i, T (hT.eigenvectorBasis hN i)⟫_𝕜 := by
  rw [hT.apply_eigenvectorBasis, inner_smul_right, inner_self_eq_norm_sq_to_K,
    OrthonormalBasis.norm_eq_one]
  simp

/-- **The quadratic form in an eigenbasis** is the sum of the eigenvalues weighted by the squared
norms of the coordinates. -/
theorem re_inner_apply_eq_sum (hT : T.IsSymmetric) (x : E) :
    RCLike.re ⟪x, T x⟫_𝕜 =
      ∑ i, hT.eigenvalues hN i * ‖⟪hT.eigenvectorBasis hN i, x⟫_𝕜‖ ^ 2 := by
  have hx : T x = ∑ i, ((hT.eigenvalues hN i : 𝕜) * ⟪hT.eigenvectorBasis hN i, x⟫_𝕜) •
      hT.eigenvectorBasis hN i := by
    conv_lhs => rw [← (hT.eigenvectorBasis hN).sum_repr' x]
    simp only [map_sum, map_smul, hT.apply_eigenvectorBasis, smul_smul, mul_comm]
  rw [hx, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm, mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul, RCLike.ofReal_re, RCLike.norm_conj]

end IsSymmetric

namespace IsPositive

/-- **Lower trace bound**: if the quadratic form of a positive operator reaches `c ≥ 0` on a unit
vector, then `c ^ j ≤ tr (T ^ j)`. Some eigenvalue is at least `c`, and the others contribute
nonnegative powers. -/
theorem pow_le_re_trace_pow (hT : T.IsPositive) {x : E} (hx : ‖x‖ = 1) {c : ℝ} (hc : 0 ≤ c)
    (hcx : c ≤ RCLike.re ⟪x, T x⟫_𝕜) (j : ℕ) : c ^ j ≤ RCLike.re (trace 𝕜 E (T ^ j)) := by
  have hS := hT.isSymmetric
  rw [hS.re_trace_pow_eq_sum_eigenvalues rfl]
  have hne : Nonempty (Fin (finrank 𝕜 E)) := by
    refine ⟨⟨0, Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, ?_⟩⟩⟩
    rintro rfl
    simp at hx
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image Finset.univ (hS.eigenvalues rfl) Finset.univ_nonempty
  have hci : c ≤ hS.eigenvalues rfl i := by
    refine hcx.trans ?_
    rw [hS.re_inner_apply_eq_sum rfl]
    calc ∑ k, hS.eigenvalues rfl k * ‖⟪hS.eigenvectorBasis rfl k, x⟫_𝕜‖ ^ 2
        ≤ ∑ k, hS.eigenvalues rfl i * ‖⟪hS.eigenvectorBasis rfl k, x⟫_𝕜‖ ^ 2 :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (hi k (mem_univ k)) (sq_nonneg _)
      _ = hS.eigenvalues rfl i := by
          rw [← Finset.mul_sum, OrthonormalBasis.sum_sq_norm_inner_right, hx, one_pow, mul_one]
  calc c ^ j ≤ hS.eigenvalues rfl i ^ j := pow_le_pow_left₀ hc hci j
    _ ≤ ∑ k, hS.eigenvalues rfl k ^ j :=
        Finset.single_le_sum (fun k _ => pow_nonneg (hT.nonneg_eigenvalues rfl k) j) (mem_univ i)

/-- **Upper trace bound**: if the quadratic form of a positive operator is at most `s` on every
unit vector, then `tr (T ^ j) ≤ dim E * s ^ j`, since every eigenvalue lies in `[0, s]`. -/
theorem re_trace_pow_le (hT : T.IsPositive) {s : ℝ}
    (hs : ∀ x : E, ‖x‖ = 1 → RCLike.re ⟪x, T x⟫_𝕜 ≤ s) (j : ℕ) :
    RCLike.re (trace 𝕜 E (T ^ j)) ≤ finrank 𝕜 E * s ^ j := by
  have hS := hT.isSymmetric
  rw [hS.re_trace_pow_eq_sum_eigenvalues rfl]
  calc ∑ k, hS.eigenvalues rfl k ^ j ≤ ∑ _k : Fin (finrank 𝕜 E), s ^ j :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (hT.nonneg_eigenvalues rfl k)
          ((hS.eigenvalues_eq_re_inner rfl k).trans_le
            (hs _ (OrthonormalBasis.norm_eq_one _ _))) j
    _ = finrank 𝕜 E * s ^ j := by simp

end IsPositive

end LinearMap
