/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Averaging square roots over a finite set

Cauchy–Schwarz bounds the mean square root by the square root of an upper bound on the mean.
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
