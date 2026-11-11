/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.SecondMoment
import CslibFrontier.Foundations.LinearAlgebra.Matrix.TraceRank

/-!
# The rank lower bound for iterated matrix multiplication

For the balanced layer schedule, the rank measure of `IMM_{n,n}` is at least
`D * exp (-C * √n)`, where `D` is the dimension of the slice on which the operator acts
[OpenAI, §4 and §5][OpenAI2026DepthFive]. The proof compares the first two trace moments of
`Fᵀ * F`, for the matrix `F` of the operator in the normalized monomial bases: the square of the
first is at most the rank times the second. The first moment is bounded below in `FirstMoment`
and the second above in `SecondMoment`, up to the sum of the weights of the type words. The
bound `exp (C₂ * √n)` for that sum is a hypothesis here.

## Main results

* `rankMeasure_imm_ge`: the rank measure of `IMM_{n,n}` is at least `D * exp (-(C₂ + 5) * √n)`
  over every field of characteristic zero.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4, §5 and §6 (unrefereed preprint)
-/

public section

open MvPolynomial Cslib.Circuits.Arithmetic
open scoped Matrix

namespace Cslib.Circuits.DepthFive

variable {p : Params} [NeZero p.n]

/-- **The rank lower bound for iterated matrix multiplication.** If the weights of the type
words sum to at most `exp (C₂ * √n)`, the rank measure of `IMM_{n,n}` for the balanced schedule
is at least `D * exp (-(C₂ + 5) * √n)`, over every field of characteristic zero. -/
theorem rankMeasure_imm_ge (hp : p.Good)
    (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k)
    (hadj : ∀ t t' : Fin p.n, (t : ℕ) + 1 = t' → p.isV t → p.isV t' → False) {C₂ : ℝ}
    (hword : ∑ τ, p.wordWeight τ ≤ Real.exp (C₂ * √(p.n : ℝ)))
    (K : Type*) [Field K] [CharZero K] :
    p.D * Real.exp (-(C₂ + 5) * √(p.n : ℝ)) ≤
      rankMeasure p.layerVar (p.k, p.m) (p.a, p.b) (imm K p.n p.n) := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast hp.n_pos
  have hr : (1 : ℝ) ≤ √(p.n : ℝ) := Real.one_le_sqrt.2 hn
  have hβ := hp.β_pos
  have hmc {r t : ℕ} (h : 0 < r) : 0 < r.multichoose t := by
    rw [Nat.multichoose_eq]
    exact Nat.choose_pos (by omega)
  have hD : (0 : ℝ) < p.D := by exact_mod_cast Nat.mul_pos (hmc hp.v_pos) (hmc hp.u_pos)
  have hμ : 0 < p.μ := by
    have : (0 : ℝ) < p.a := by exact_mod_cast hp.a_pos
    have : (0 : ℝ) < p.v := by exact_mod_cast hp.v_pos
    have : (0 : ℝ) < p.b := by exact_mod_cast hp.b_pos
    have : (0 : ℝ) < p.u := by exact_mod_cast hp.u_pos
    rw [Params.μ]
    positivity
  have hT := first_trace_ge hp hcard
  have hT₂ := (second_trace_le hp hcard hadj).trans
    (mul_le_mul_of_nonneg_left hword (by positivity))
  have hR := Matrix.sq_trace_le_rank_mul_trace_sq (pathMatrix p)
  rw [rank_pathMatrix_eq K hcard hp.k_le_a] at hR
  have hpow : (1 + p.β) ^ p.m ≤ Real.exp (2 * √(p.n : ℝ)) := by
    have hm : (p.m : ℝ) ≤ p.n := by exact_mod_cast (by have := p.hkm; omega : p.m ≤ p.n)
    calc (1 + p.β) ^ p.m ≤ Real.exp p.β ^ p.m :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp p.β]) _
      _ = Real.exp (p.m * p.β) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (2 * √(p.n : ℝ)) := by
          refine Real.exp_le_exp.2 ((mul_le_mul hm hp.β_le hβ.le (by positivity)).trans
            (le_of_eq ?_))
          rw [mul_div_assoc', mul_comm, mul_div_assoc, Real.div_sqrt]
  have hE : Real.exp (-(C₂ + 5) * √(p.n : ℝ)) *
      ((1 + p.β) ^ p.m * Real.exp (C₂ * √(p.n : ℝ))) ≤
        Real.exp (-(3 / 2) / √(p.n : ℝ)) ^ 2 := by
    calc Real.exp (-(C₂ + 5) * √(p.n : ℝ)) * ((1 + p.β) ^ p.m * Real.exp (C₂ * √(p.n : ℝ)))
        ≤ Real.exp (-(C₂ + 5) * √(p.n : ℝ)) *
            (Real.exp (2 * √(p.n : ℝ)) * Real.exp (C₂ * √(p.n : ℝ))) := by gcongr
      _ = Real.exp (-3 * √(p.n : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-(3 / 2) / √(p.n : ℝ)) ^ 2 := by
          rw [← Real.exp_nat_mul]
          refine Real.exp_le_exp.2 ?_
          have : 1 / √(p.n : ℝ) ≤ √(p.n : ℝ) := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith
          have h : (2 : ℕ) * (-(3 / 2) / √(p.n : ℝ)) = -3 * (1 / √(p.n : ℝ)) := by
            push_cast
            ring
          rw [h]
          linarith
  have hX : (0 : ℝ) < p.D * (p.n : ℝ) ^ (2 * (p.n - 1)) * p.μ ^ 2 * (1 + p.β) ^ p.m *
      Real.exp (C₂ * √(p.n : ℝ)) := by positivity
  refine le_of_mul_le_mul_right ?_ hX
  calc p.D * Real.exp (-(C₂ + 5) * √(p.n : ℝ)) * (p.D * (p.n : ℝ) ^ (2 * (p.n - 1)) * p.μ ^ 2 *
        (1 + p.β) ^ p.m * Real.exp (C₂ * √(p.n : ℝ)))
      = ((p.D : ℝ) * (p.n : ℝ) ^ (p.n - 1) * p.μ) ^ 2 * (Real.exp (-(C₂ + 5) * √(p.n : ℝ)) *
          ((1 + p.β) ^ p.m * Real.exp (C₂ * √(p.n : ℝ)))) := by ring
    _ ≤ ((p.D : ℝ) * (p.n : ℝ) ^ (p.n - 1) * p.μ) ^ 2 *
          Real.exp (-(3 / 2) / √(p.n : ℝ)) ^ 2 := by gcongr
    _ = (p.D * (p.n : ℝ) ^ (p.n - 1) * p.μ * Real.exp (-(3 / 2) / √(p.n : ℝ))) ^ 2 := by ring
    _ ≤ ((pathMatrix p)ᵀ * pathMatrix p).trace ^ 2 := by gcongr
    _ ≤ _ := hR.trans (mul_le_mul_of_nonneg_left hT₂ (Nat.cast_nonneg _))

end Cslib.Circuits.DepthFive
