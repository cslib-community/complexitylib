/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.ConditionalProductMean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Clipped accuracy of positive conditional means

These finite estimates clip after averaging on the actual joint slice. Only the canonical
mean is dominated by the target; the approximate mean needs no such support hypothesis.
They do not control centered sampling noise or a separate saturated preparation signal.
The fourth-power fidelity estimate follows from the homogeneous-loss API, avoiding a
second proof of reverse Minkowski. The scalar constant agrees with `fidelity` in the supplied
OpenAI reference `AffineSampling.lean` at revision `4eaee87548250b2682affda7d05d947c05554bae`.

## Main results

* `Cslib.min_relative_sub_le_root_four`: scalar fidelity with one-sided domination.
* `Cslib.min_relative_expect_sub_four_le`: a positive conditional-mean moment payment.
* `Cslib.min_abs_sum_div_le`: signed sums after the positive-summand comparisons.
-/
public section
namespace Cslib
open Finset
open scoped BigOperators

/-- Clipped fourth-root fidelity. The canonical value `s` is dominated, but `t` may be
arbitrarily large. This is the scalar reference `fidelity`, with the same constant 32. -/
theorem min_relative_sub_le_root_four {s t D K : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hD : 0 ≤ D) (hK : 1 ≤ K) (hdom : s ≤ K * D) :
    min 1 (|s - t| / (1 + D)) ≤ 32 * K * |s ^ (4⁻¹ : ℝ) - t ^ (4⁻¹ : ℝ)| := by
  have hk : 0 ≤ K := by linarith
  have h := mul_min_pow_le_homogeneousLoss (s := 4) (by decide) hk hD
    (by norm_num : (0 : ℝ) < 1) hs hdom ht
  have hr := homogeneousLoss_le_rpow_inv_sub_pow (s := 4) (by decide) hs ht
  norm_num only [one_mul, Nat.reduceSub, Nat.cast_ofNat] at h
  norm_num only [Nat.cast_ofNat, show (4⁻¹ : ℝ) = 1 / 4 from by norm_num] at hr ⊢
  have hc : 2 * (3 * K + 3) ^ 3 * (4 : ℝ) ^ 4 ≤ (32 * K) ^ 4 := by
    have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * K + 3)
      (show 3 * K + 3 ≤ 6 * K by linarith) 3
    have h4 : K ^ 3 ≤ K ^ 4 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ K ^ 3) (sub_nonneg.mpr hK)]
    nlinarith
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp
  rw [mul_pow]
  have hm := mul_le_mul_of_nonneg_right hc
    (pow_nonneg (abs_nonneg (s ^ (1 / 4 : ℝ) - t ^ (1 / 4 : ℝ))) 4)
  exact h.trans ((mul_le_mul_of_nonneg_left hr (by positivity)).trans (by nlinarith))

/-- Clipped triangle inequality for signed errors with one fixed positive denominator. -/
theorem min_abs_add_div_le {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    min 1 (|x + y| / a) ≤ min 1 (|x| / a) + min 1 (|y| / a) := by
  have hx : 0 ≤ min 1 (|x| / a) := by positivity
  have hy : 0 ≤ min 1 (|y| / a) := by positivity
  by_cases hx1 : 1 ≤ |x| / a
  · rw [min_eq_left hx1]
    exact (min_le_left _ _).trans (by linarith)
  by_cases hy1 : 1 ≤ |y| / a
  · rw [min_eq_left hy1]
    exact (min_le_left _ _).trans (by linarith)
  rw [min_eq_right (le_of_not_ge hx1), min_eq_right (le_of_not_ge hy1), ← add_div]
  exact (min_le_right _ _).trans
    (div_le_div_of_nonneg_right (abs_add_le x y) ha.le)

/-- Finite signed sums are clipped after adding. Apply positive mean domination to each
summand separately before invoking this inequality on a paired difference or prefix. -/
theorem min_abs_sum_div_le {ι : Type*} (S : Finset ι) {a : ℝ} (ha : 0 < a) (e : ι → ℝ) :
    min 1 (|∑ i ∈ S, e i| / a) ≤ ∑ i ∈ S, min 1 (|e i| / a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (min_abs_add_div_le ha _ _).trans (add_le_add_right ih _)

/-- Clipping after a common finite conditional mean costs one power of the physical
scale `c`. Empty slices are allowed. All samples may be correlated. Domination is required
before subtracting any signed summands. Ordinary progress is a separate payment. -/
theorem min_relative_expect_sub_four_le {Ω : Type*} (S : Finset Ω)
    {C A : Ω → ℝ} {c D K : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hC : ∀ σ ∈ S, 0 ≤ C σ) (hA : ∀ σ ∈ S, 0 ≤ A σ)
    (hdom : c * (𝔼 σ ∈ S, C σ) ≤ K * D) :
    min 1 (|c * (𝔼 σ ∈ S, (A σ - C σ))| / (1 + D)) ^ 4 ≤
      (512 * (3 * K + 3) ^ 3) * c *
        𝔼 σ ∈ S, |A σ ^ (4⁻¹ : ℝ) - C σ ^ (4⁻¹ : ℝ)| ^ 4 := by
  have h := mul_min_pow_le_homogeneousLoss (s := 4) (by decide) hK hD
    (by norm_num : (0 : ℝ) < 1) (mul_nonneg hc (expect_nonneg hC)) hdom
    (mul_nonneg hc (expect_nonneg hA))
  rw [one_mul, homogeneousLoss_mul (by decide) hc] at h
  have he := homogeneousLoss_expect_le S (s := 4) (by decide) hC hA
  have hp : (𝔼 σ ∈ S, homogeneousLoss 4 (C σ) (A σ)) ≤
      256 * 𝔼 σ ∈ S, |A σ ^ (4⁻¹ : ℝ) - C σ ^ (4⁻¹ : ℝ)| ^ 4 := by
    rw [mul_expect]
    apply expect_le_expect
    intro σ hσ
    have hr := homogeneousLoss_le_rpow_inv_sub_pow (s := 4) (by decide) (hC σ hσ) (hA σ hσ)
    norm_num only [Nat.cast_ofNat, show (4 : ℝ) ^ 4 = 256 from by norm_num] at hr
    simpa only [abs_sub_comm, show (4⁻¹ : ℝ) = 1 / 4 from by norm_num] using hr
  have heq : |c * (𝔼 σ ∈ S, (A σ - C σ))| =
      |c * (𝔼 σ ∈ S, C σ) - c * (𝔼 σ ∈ S, A σ)| := by
    rw [expect_sub_distrib, mul_sub, abs_sub_comm]
  rw [heq]
  calc
    _ ≤ 2 * (3 * K + 3) ^ (4 - 1) * (c * homogeneousLoss 4
        (𝔼 σ ∈ S, C σ) (𝔼 σ ∈ S, A σ)) := h
    _ ≤ 2 * (3 * K + 3) ^ (4 - 1) * (c * (256 *
        𝔼 σ ∈ S, |A σ ^ (4⁻¹ : ℝ) - C σ ^ (4⁻¹ : ℝ)| ^ 4)) := by
      gcongr
      exact he.trans hp
    _ = _ := by ring

end Cslib
