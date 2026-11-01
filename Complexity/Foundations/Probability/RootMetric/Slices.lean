/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Integrating conditional row moments

The integrated row moment is exactly the sum of conditional endpoint moments weighted by
actual joint retention densities. Thus a uniform conditional contraction passes to the row
norm without a conditioning penalty, even when the slices have different sizes or are empty.
The source mask, endpoint mask and errors may all be correlated.

This is the density-accounting step in [OpenAI2026LogSpace, Lemma 7.8, printed p. 42], at
revision `7ef5c0cc` (23 September 2026, not peer reviewed). The source uses exponent eight;
these identities work for every natural exponent, including the fourth-moment route.
The conditional contraction itself must be supplied by the sampler; this module does not
construct the recursive estimator or prove that its samples vary every required coordinate.

## Main results

* `Cslib.rowNormPow_eq_sum_dens_mul_expect`: exact conditional decomposition.
* `Cslib.rowNormPow_le_of_conditional_expect_le`: uniform slice estimates integrate directly.
* `Cslib.rowNormPow_le_sum_conditional_budgets`: nonuniform slice budgets retain their densities.
-/

public section

namespace Cslib

open Finset
open scoped BigOperators

variable {Ω V : Type*} [Fintype Ω] [Fintype V]
  {p : ℕ} {N u : ℝ} {X Y : Ω → V → Prop}
  [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]

/-- Exchange the finite expectation with the source and endpoint sums, preserving their
actual joint mask. The two masks and the table may depend on the same draw. -/
theorem expect_filtered_sum_eq (H : Ω → V → V → ℝ) :
    (𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), H σ x y) =
      ∑ x, ∑ y, 𝔼 σ, if X σ x ∧ Y σ y then H σ x y else 0 := by
  have hpoint : ∀ σ,
      (∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), H σ x y) =
        ∑ x, ∑ y, if X σ x ∧ Y σ y then H σ x y else 0 := by
    intro σ
    rw [sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : X σ x
    · simp [hx, sum_filter]
    · simp [hx]
  simp_rw [hpoint]
  rw [expect_sum_comm]
  exact sum_congr rfl fun x _ => expect_sum_comm _ _ _

/-- Actual slice densities cancel the conditional averaging denominators, including empty
slices. No independence or uniform retention probability is needed. -/
theorem rowNormPow_eq_sum_dens_mul_expect (F : Ω → V → V → ℝ) :
    rowNormPow p N u X Y F = (N * u)⁻¹ * ∑ x, ∑ y,
      (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) *
        𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), |F σ x y| ^ p := by
  classical
  rw [rowNormPow, expect_filtered_sum_eq]
  congr 1
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simpa only [mem_filter, mem_univ, true_and, NNRat.smul_def] using
    (Fintype.expect_ite_mem ({σ | X σ x ∧ Y σ y} : Finset Ω)
      (fun σ => |F σ x y| ^ p))

/-- Conditional estimates with the same factor on every retained pair give the same factor
in the integrated row norm. The input slice moments may differ arbitrarily. -/
theorem rowNormPow_le_of_conditional_expect_le (hNu : 0 ≤ N * u)
    (F E : Ω → V → V → ℝ) (c : ℝ)
    (h : ∀ x y, (𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), |E σ x y| ^ p) ≤
      c * 𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), |F σ x y| ^ p) :
    rowNormPow p N u X Y E ≤ c * rowNormPow p N u X Y F := by
  rw [rowNormPow_eq_sum_dens_mul_expect, rowNormPow_eq_sum_dens_mul_expect]
  calc
    _ ≤ (N * u)⁻¹ * ∑ x, ∑ y,
        (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) *
          (c * 𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), |F σ x y| ^ p) := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => sum_le_sum fun y _ => ?_)
        (inv_nonneg.mpr hNu)
      exact mul_le_mul_of_nonneg_left (h x y) (by positivity)
    _ = _ := by simp only [mul_left_comm _ c, ← mul_sum]

/-- Slice-specific budgets are integrated with their actual densities, rather than a maximum
budget or a reciprocal minimum-density penalty. -/
theorem rowNormPow_le_sum_conditional_budgets (hNu : 0 ≤ N * u)
    (E : Ω → V → V → ℝ) (b : V → V → ℝ)
    (h : ∀ x y, (𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), |E σ x y| ^ p) ≤ b x y) :
    rowNormPow p N u X Y E ≤ (N * u)⁻¹ * ∑ x, ∑ y,
      (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) * b x y := by
  rw [rowNormPow_eq_sum_dens_mul_expect]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => sum_le_sum fun y _ => ?_)
    (inv_nonneg.mpr hNu)
  exact mul_le_mul_of_nonneg_left (h x y) (by positivity)

end Cslib
