/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of Complexity.Foundations.Data.Polynomial.HermiteInterpolation)

import Complexity.Foundations.Data.Polynomial.HermiteInterpolation
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

/-! Tests for confluent Hermite interpolation from Taylor jets. -/

namespace ComplexityTests.HermiteInterpolation

open Polynomial

/-! ### Concrete jets and matrix entries -/

/-- `p (1 + z) = 1 + 2 z + z ^ 2` for `p = X ^ 2`: the order-2 jet at `1` is `(1, 2)`. -/
example :
    taylorJet ![(1 : ℚ)] 2 (X ^ 2) (0, 0) = 1 ∧ taylorJet ![(1 : ℚ)] 2 (X ^ 2) (0, 1) = 2 := by
  refine ⟨?_, ?_⟩
  · change (taylor (1 : ℚ) (X ^ 2)).coeff 0 = 1
    rw [taylor_coeff_zero]
    simp
  · change (taylor (1 : ℚ) (X ^ 2)).coeff 1 = 2
    rw [taylor_coeff_one]
    norm_num

/-- Row `(t, j) = (2, 1)`, column `X ^ 3` (`finProdFinEquiv (1, 1) = 3`): `(3 choose 1) 2 ^ 2`. -/
example : hermiteMatrix ![1, 2] 2 (1, 1) (1, 1) = 12 := by
  decide

/-- The Hermite matrix of distinct nodes is nonsingular. -/
example : (hermiteMatrix ![1, 2, 3] 4).det ≠ 0 :=
  det_hermiteMatrix_ne_zero (by decide)

/-! ### Degenerate cases -/

/-- With no nodes the degree bound forces the zero polynomial. -/
example (p : ℚ[X]) (hp : p.degree < ↑(0 * 3)) : p = 0 :=
  eq_zero_of_taylorJet_eq_zero (t := Fin.elim0) (fun i => i.elim0) hp
    (funext fun r => r.1.elim0)

/-- With empty jets (`J = 0`) the degree bound forces the zero polynomial. -/
example (p : ℚ[X]) (hp : p.degree < ↑(2 * 0)) : p = 0 :=
  eq_zero_of_taylorJet_eq_zero (t := ![0, 1]) (fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp_all) hp (funext fun r => r.2.elim0)

/-! ### The hypotheses are needed -/

/-- The degree bound is sharp: `(X - 1) ^ 2` has degree `2 = 1 * 2` and vanishing order-2 jet at
the node `1`. -/
example : taylorJet ![(1 : ℚ)] 2 ((X - 1) ^ 2) = 0 ∧ ((X - 1) ^ 2 : ℚ[X]) ≠ 0 := by
  refine ⟨funext fun r => ?_, pow_ne_zero 2 (X_sub_C_ne_zero 1)⟩
  obtain ⟨i, j⟩ := r
  fin_cases i
  fin_cases j <;> simp

/-- Unit differences are needed: over `ZMod 4`, `2 X` has degree `1 < 2 * 1` and vanishes at the
nodes `0` and `2`, whose difference `2` is not a unit. -/
example : taylorJet ![(0 : ZMod 4), 2] 1 (C 2 * X) = 0 ∧ (C 2 * X : (ZMod 4)[X]) ≠ 0 := by
  refine ⟨funext fun r => ?_, ?_⟩
  · obtain ⟨i, j⟩ := r
    fin_cases i <;> fin_cases j
    all_goals simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, taylorJet_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, taylor_mul, taylor_C,
      taylor_X, Fin.val_eq_zero, mul_coeff_zero, coeff_C_zero, coeff_add, coeff_X_zero, zero_add,
      Pi.zero_apply]
    all_goals decide
  · intro h
    have := congrArg (coeff · 1) h
    simp only [coeff_C_mul_X, coeff_zero] at this
    exact absurd this (by decide)

/-! ### Reconstruction -/

/-- The value at `0` of `X ^ 2 + 3`, recovered from its order-2 jets at the nodes `1, 2`. -/
example : (3 : ℚ) = ((hermiteMatrix ![1, 2] 2).det : ℚ)⁻¹ •
    (((hermiteMatrix ![1, 2] 2).map (Int.cast : ℤ → ℚ)).updateCol (⟨0, by decide⟩, ⟨0, by decide⟩)
      (taylorJet (fun i => ((![1, 2] : Fin 2 → ℤ) i : ℚ)) 2 (X ^ 2 + C 3))).det := by
  have h := eval_zero_eq_of_taylorJet ℚ (t := ![1, 2]) (J := 2) (by decide) (by decide)
    (by decide) (p := X ^ 2 + C 3) (by
      rw [show (X ^ 2 + C 3 : ℚ[X]).degree = 2 by compute_degree!]
      exact WithBot.coe_lt_coe.mpr (by norm_num))
  rw [← h]
  simp

end ComplexityTests.HermiteInterpolation
