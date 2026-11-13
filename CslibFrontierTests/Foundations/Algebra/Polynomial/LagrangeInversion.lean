/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Polynomial.LagrangeInversion
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Lagrange inversion for a fixed point: concrete checks

Over `ℚ[t]` with the ideal `(t)`, the constant polynomial `G = t` in `y` has the fixed point
`t`, and the Lagrange sum agrees with it modulo every power of `(t)`. The weight filtration is
checked on `G = t + y ^ 2`.
-/

public section

namespace CslibFrontierTests.LagrangeInversion

open Polynomial

/-- The fixed point `t` of the constant polynomial `G = t` agrees with the Lagrange sum modulo
every power of `(t)`. -/
example (e : ℕ) :
    (X : ℚ[X]) -
      ∑ m ∈ Finset.range (2 * e), ((m : ℚ) + 1)⁻¹ • ((C X : ℚ[X][X]) ^ (m + 1)).coeff m ∈
      Ideal.span {(X : ℚ[X])} ^ e :=
  sub_sum_coeff_pow_mem_of_eval_eq (F := ℚ) (G := C X)
    (by simp) (by simp) (Ideal.subset_span rfl) (by simp) le_rfl

/-- `t + y ^ 2` has weight at least two for the ideal `(t)`. -/
example : HasWeight (Ideal.span {(X : ℚ[X])}) 2 (C X + X ^ 2 : ℚ[X][X]) :=
  hasWeight_two_of_coeff_mem (by simp) (by simp)

end CslibFrontierTests.LagrangeInversion
