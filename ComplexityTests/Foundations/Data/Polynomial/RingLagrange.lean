/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Polynomial.RingLagrange
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-! Tests for Lagrange interpolation over a commutative ring. -/

namespace ComplexityTests.RingLagrange

open Polynomial Lagrange

/-! ### Interpolation over `ZMod 8`, which is not a domain -/

/-- The nodes `0` and `1` of `ZMod 8` differ by a unit. -/
theorem pairwise_isUnit :
    ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)).Pairwise
      fun i j => IsUnit ((![0, 1] : Fin 2 → ZMod 8) i - ![0, 1] j) := by
  intro i _ j _ hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simp
  · simp
  · exact absurd rfl hij

/-- The interpolant of the values `3, 5` at `0, 1` takes those values. -/
example : (ringInterpolate Finset.univ (![0, 1] : Fin 2 → ZMod 8) ![3, 5]).eval 0 = 3 ∧
    (ringInterpolate Finset.univ (![0, 1] : Fin 2 → ZMod 8) ![3, 5]).eval 1 = 5 :=
  ⟨eval_ringInterpolate_at_node pairwise_isUnit _ (Finset.mem_univ (0 : Fin 2)),
    eval_ringInterpolate_at_node pairwise_isUnit _ (Finset.mem_univ (1 : Fin 2))⟩

/-- A linear polynomial over `ZMod 8` is the interpolant of its values at `0` and `1`. -/
example : (C 3 + C 2 * X : (ZMod 8)[X]) =
    ringInterpolate Finset.univ (![0, 1] : Fin 2 → ZMod 8)
      (fun i => (C 3 + C 2 * X : (ZMod 8)[X]).eval (![0, 1] i)) :=
  eq_ringInterpolate pairwise_isUnit ((degree_add_le _ _).trans_lt (max_lt
    (degree_C_le.trans_lt (by decide)) ((degree_C_mul_X_le _).trans_lt (by decide))))

/-! ### Unit differences are needed -/

/-- Over `ZMod 4`, the nodes `0` and `2` differ by the non-unit `2`, and the nonzero polynomial
`2 X` of degree below two vanishes at both: uniqueness fails without unit differences. -/
example : (C 2 * X : (ZMod 4)[X]).eval 0 = 0 ∧ (C 2 * X : (ZMod 4)[X]).eval 2 = 0 ∧
    (C 2 * X : (ZMod 4)[X]) ≠ 0 := by
  refine ⟨by simp, by simp only [eval_mul, eval_C, eval_X]; decide, fun h => ?_⟩
  have := congrArg (coeff · 1) h
  simp only [coeff_C_mul, coeff_X_one, mul_one, coeff_zero] at this
  exact absurd this (by decide)

end ComplexityTests.RingLagrange
