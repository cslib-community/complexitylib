/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACBayes.KL
import CslibFrontierTests.PACBayes

/-! Checks for the PAC-Bayes-kl bound and the binary relative entropy, on the two constant
classifiers of `CslibFrontierTests.PACBayes` under the noisy distribution, with the uniform prior
and the 0-1 loss. -/

namespace CslibFrontierTests.PACBayesKL

open Cslib.Probability Cslib.MachineLearning Cslib.MachineLearning.PACBayes MeasureTheory
open InformationTheory (klFun_apply klFun_zero)
open CslibFrontierTests.PACBayes (zeroOne measurable_zeroOne zeroOne_mem_Icc prior
  prior_singleton trueRisk_noisy)
open CslibFrontierTests.AgnosticPAC (noisy)

/-- `kl(0 ‖ 1 / 2) = log 2`. -/
theorem binaryKL_zero_half : binaryKL 0 (1 / 2) = Real.log 2 := by
  rw [binaryKL_def, klFun_apply, klFun_apply]
  norm_num
  ring

/-- **The Occam form at `m = 1023`, `δ = 1 / 16`**: with probability at least `15 / 16`, neither
constant has empirical risk `0` under `noisy`. The margin is `15 log 2 / 1023`, far below
`kl(0 ‖ 1 / 2) = log 2`; McAllester's form at this sample size has margin about `0.1`. -/
example : Measure.pi (fun _ : Fin 1023 => noisy)
    {S | ∃ b, empiricalRisk zeroOne S b = 0} ≤ ENNReal.ofReal (1 / 16) := by
  refine (measure_mono fun S hS => ?_).trans (measure_pi_exists_binaryKL_risk_gt (D := noisy)
    measurable_zeroOne zeroOne_mem_Icc (by norm_num) prior (by norm_num : (0 : ℝ) < 1 / 16))
  obtain ⟨b, hb⟩ := hS
  refine ⟨b, by rw [prior_singleton]; norm_num, ?_⟩
  have hreal : prior.real {b} = 1 / 2 := by
    rw [measureReal_def, prior_singleton]; norm_num
  rw [hb, trueRisk_noisy, binaryKL_zero_half, hreal,
    show (1 : ℝ) / (1 / 2) = 2 ^ 1 by norm_num,
    show ((1023 : ℕ) : ℝ) + 1 = 2 ^ 10 by norm_num,
    show (2 : ℝ) ^ 10 / (1 / 16) = 2 ^ 14 by norm_num, Real.log_pow, Real.log_pow]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  push_cast
  rw [div_lt_iff₀ (by norm_num)]
  linarith

/-- The hypothesis `0 < m` is needed: on the empty sample the margin divides by `0` and
vanishes, while the empirical risk `0` has positive divergence from the true risk `1 / 2`. -/
example (c : ℝ) : c / ((0 : ℕ) : ℝ) <
    binaryKL (empiricalRisk zeroOne (![] : Fin 0 → Bool × Bool) true)
      (trueRisk zeroOne noisy true) := by
  rw [trueRisk_noisy, Nat.cast_zero, div_zero,
    show empiricalRisk zeroOne (![] : Fin 0 → Bool × Bool) true = 0 by
      simp [empiricalRisk_eq_sum_div],
    binaryKL_zero_half]
  exact Real.log_pos (by norm_num)

/-- At `p = 0` the true divergence of `q = 1` is infinite, but `binaryKL 1 0 = 1`. -/
example : binaryKL 1 0 = 1 := by
  simp [binaryKL_def, klFun_zero]

/-- The junk values are not convex, so Jensen's inequality for `binaryKL` needs `q = p` wherever
`p ∈ {0, 1}`: the midpoint of `(1, 0)` and `(1, 1)` has `kl(1 ‖ 1 / 2) = log 2`, above the average
`1 / 2` of `binaryKL 1 0 = 1` and `binaryKL 1 1 = 0`. -/
example : (binaryKL 1 0 + binaryKL 1 1) / 2 < binaryKL 1 (1 / 2) := by
  have h : binaryKL 1 (1 / 2) = Real.log 2 := by
    rw [binaryKL_def, klFun_apply, klFun_apply]
    norm_num
    ring
  rw [h, binaryKL_self]
  have h1 : binaryKL 1 0 = 1 := by simp [binaryKL_def, klFun_zero]
  rw [h1]
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

/-- The binomial term bound at `m = 2`, `k = 1`, `p = 1 / 2`:
`C(2, 1) (1 / 2) (1 / 2) exp (2 kl(1 / 2 ‖ 1 / 2)) = 1 / 2 ≤ 1`. -/
example : ((2 : ℕ).choose 1 : ℝ) * (1 / 2) ^ 1 * (1 - 1 / 2) ^ (2 - 1) *
    Real.exp ((2 : ℕ) * binaryKL ((1 : ℕ) / (2 : ℕ)) (1 / 2)) ≤ 1 :=
  choose_mul_pow_mul_exp_binaryKL_le_one (by norm_num) (by norm_num)

end CslibFrontierTests.PACBayesKL
