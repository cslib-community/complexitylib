/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Jensen's inequality for `exp` and a uniform average

`exp (𝔼 x, g x) ≤ 𝔼 x, exp (g x)` over a finite nonempty type: Mathlib's `convexOn_exp.map_sum_le`
with uniform weights, stated with the uniform average `𝔼`.

## Main results

* `Real.exp_expect_le`: Jensen's inequality for `exp` and a uniform average.
-/

public section

namespace Real

open scoped BigOperators

/-- **Jensen's inequality for `exp` and a uniform average**: `exp (𝔼 x, g x) ≤ 𝔼 x, exp (g x)`. -/
theorem exp_expect_le {α : Type*} [Fintype α] [Nonempty α] (g : α → ℝ) :
    exp (𝔼 x, g x) ≤ 𝔼 x, exp (g x) := by
  have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => (Fintype.card α : ℝ)⁻¹)
    (p := g) (fun _ _ => by positivity) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne'])
    fun _ _ => Set.mem_univ _
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, div_eq_inv_mul,
    div_eq_inv_mul, Finset.mul_sum, Finset.mul_sum]
  simpa only [smul_eq_mul] using h

end Real
