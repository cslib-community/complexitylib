/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Square-root averaging and scaling lemmas

Cauchy–Schwarz bounds the mean square root by the square root of an upper bound on the mean
(`Finset.sum_sqrt_le_card_mul_sqrt`), and `Real.sqrt_mul_div_self` rescales square-root regret
bounds to time averages.
-/

public section

namespace Finset

/-- Cauchy–Schwarz averaging: if `∑ i ∈ s, F i ≤ #s * B`, then `∑ i ∈ s, √(F i) ≤ #s * √B`. -/
theorem sum_sqrt_le_card_mul_sqrt {ι : Type*} (s : Finset ι) {F : ι → ℝ}
    (hF : ∀ i ∈ s, 0 ≤ F i) {B : ℝ} (hB : 0 ≤ B) (hsum : ∑ i ∈ s, F i ≤ #s * B) :
    ∑ i ∈ s, Real.sqrt (F i) ≤ #s * Real.sqrt B := by
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (F i))
  have hsq : ∑ i ∈ s, Real.sqrt (F i) ^ 2 = ∑ i ∈ s, F i :=
    sum_congr rfl fun i hi => Real.sq_sqrt (hF i hi)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, hsq] at hcs
  refine (pow_le_pow_iff_left₀ (sum_nonneg fun i _ => Real.sqrt_nonneg _) (by positivity)
    two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt hB]
  nlinarith [(by positivity : (0 : ℝ) ≤ #s)]

end Finset

/-- Dividing the square root of `T * L` by `T > 0` yields `√(L / T)`. -/
theorem Real.sqrt_mul_div_self {T L : ℝ} (hT : 0 < T) : √(T * L) / T = √(L / T) := by
  have hs : √T * √T = T := Real.mul_self_sqrt hT.le
  have hs0 : 0 < √T := Real.sqrt_pos.mpr hT
  rw [Real.sqrt_mul hT.le, Real.sqrt_div' L hT.le, div_eq_div_iff hT.ne' hs0.ne']
  linear_combination √L * hs
