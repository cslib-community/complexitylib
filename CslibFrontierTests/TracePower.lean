/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.LinearAlgebra.TracePower
import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd

/-! Traces of powers: the closed-path expansion on a concrete matrix, and the two trace bounds on
the identity, where both are attained. -/

namespace CslibFrontierTests.TracePower

open Matrix LinearMap Module
open scoped InnerProductSpace

/-! ### Closed paths -/

-- The Fibonacci matrix: `tr (M ^ 3) = 4`, the number of closed walks of length `3` in the graph
-- with a loop at `0` and an edge `0 — 1`.
example : ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 3).trace = 4 := by decide

example : ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 3).trace =
    ∑ p : Fin 4 → Fin 2, if p 0 = p (Fin.last 3) then
      ∏ i : Fin 3, (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) (p i.castSucc) (p i.succ)
    else 0 :=
  trace_pow_eq_sum _ 3

/-! ### The trace bounds on the identity of `ℂ²` -/

-- The quadratic form of the identity is `1` on unit vectors, and `tr (1 ^ j) = 2`.
example (j : ℕ) :
    (1 : ℝ) ^ j ≤ RCLike.re (trace ℂ (EuclideanSpace ℂ (Fin 2))
      ((1 : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) ^ j)) := by
  have hx : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1 := by simp
  refine isPositive_one.pow_le_re_trace_pow hx zero_le_one ?_ j
  rw [Module.End.one_apply, inner_self_eq_norm_sq, hx, one_pow]

example (j : ℕ) :
    RCLike.re (trace ℂ (EuclideanSpace ℂ (Fin 2))
      ((1 : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) ^ j)) ≤ 2 * 1 ^ j := by
  have h := isPositive_one.re_trace_pow_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin 2)) (s := 1)
    (fun x hx => by rw [Module.End.one_apply, inner_self_eq_norm_sq, hx, one_pow]) j
  refine h.trans_eq ?_
  simp

-- Both bounds are attained: `tr (1 ^ j) = 2 = dim ℂ²`.
example (j : ℕ) :
    RCLike.re (trace ℂ (EuclideanSpace ℂ (Fin 2))
      ((1 : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) ^ j)) = 2 := by
  simp

end CslibFrontierTests.TracePower
