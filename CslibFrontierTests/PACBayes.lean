/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACBayes.Basic
import CslibFrontierTests.AgnosticPAC

/-! Checks for the PAC-Bayes bounds: the two constant classifiers on `Bool` under the noisy
distribution of `CslibFrontierTests.AgnosticPAC`, a uniform prior, the 0-1 loss, and explicit
sample sizes. -/

namespace CslibFrontierTests.PACBayes

open Cslib.MachineLearning Cslib.MachineLearning.PACBayes MeasureTheory InformationTheory
open CslibFrontierTests.AgnosticPAC (noisy)
open scoped ENNReal

/-- The 0-1 loss of the constant classifier `b` on the labelled example `z`. -/
def zeroOne (b : Bool) (z : Bool × Bool) : ℝ := if b = z.2 then 0 else 1

theorem measurable_zeroOne (b : Bool) : Measurable (zeroOne b) :=
  measurable_of_countable _

theorem zeroOne_mem_Icc (b : Bool) (z : Bool × Bool) : zeroOne b z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold zeroOne
  split_ifs <;> norm_num

/-- The uniform prior on the two constants. -/
noncomputable def prior : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac true + (2⁻¹ : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure prior := by
  constructor
  simp only [prior, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

theorem prior_singleton (b : Bool) : prior {b} = 2⁻¹ := by
  cases b <;> simp [prior]

/-- Each constant has true risk `1 / 2` under `noisy`. -/
theorem trueRisk_noisy (b : Bool) : trueRisk zeroOne noisy b = 1 / 2 := by
  rw [trueRisk_def, noisy, integral_add_measure (Integrable.of_finite.smul_measure (by simp))
      (Integrable.of_finite.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  cases b <;> norm_num [zeroOne]

/-- On the two-example sample that sees both labels, each constant has empirical risk `1 / 2`. -/
example (b : Bool) : empiricalRisk zeroOne ![((false, true) : Bool × Bool), (false, false)] b =
    1 / 2 := by
  cases b <;> norm_num [empiricalRisk_eq_sum_div, zeroOne, Fin.sum_univ_two]

/-- `log (1 / (1 / 2)) + log (1024 / (1 / 16)) = 15 log 2 ≤ 15`, so the margin of the bound is
below `1 / 10` at `m = 1024`. -/
private theorem sqrt_margin_lt (c : ℝ) (hc : c ≤ 15) :
    Real.sqrt (c / (2 * ((1024 : ℕ) - 1 : ℝ))) < 1 / 10 := by
  rw [Real.sqrt_lt' (by norm_num)]
  push_cast
  rw [div_lt_iff₀ (by norm_num)]
  linarith

private theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
  linarith

/-- **The Occam corollary at `m = 1024`, `δ = 1 / 16`**: with probability at least `15 / 16`,
both constants have empirical risk at least `2 / 5` under `noisy`, whose true risks are `1 / 2`. -/
example : Measure.pi (fun _ : Fin 1024 => noisy)
    {S | ∃ b, empiricalRisk zeroOne S b < 2 / 5} ≤ ENNReal.ofReal (1 / 16) := by
  refine (measure_mono fun S hS => ?_).trans (measure_pi_exists_risk_gt (D := noisy)
    measurable_zeroOne zeroOne_mem_Icc (by norm_num) prior (by norm_num : (0 : ℝ) < 1 / 16))
  obtain ⟨b, hb⟩ := hS
  refine ⟨b, by rw [prior_singleton]; norm_num, ?_⟩
  have hreal : prior.real {b} = 1 / 2 := by
    rw [measureReal_def, prior_singleton]; norm_num
  have hlog : Real.log (1 / prior.real {b}) + Real.log ((1024 : ℕ) / (1 / 16)) ≤ 15 := by
    rw [hreal, show (1 : ℝ) / (1 / 2) = 2 ^ 1 by norm_num,
      show ((1024 : ℕ) : ℝ) / (1 / 16) = 2 ^ 14 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    linarith [log_two_le_one]
  rw [trueRisk_noisy]
  linarith [sqrt_margin_lt _ hlog]

/-- **The posterior-averaged bound at the prior**: `KL(P ‖ P) = 0`, so with probability at least
`15 / 16` the prior-averaged empirical risk under `noisy` is at least `2 / 5`. -/
example : Measure.pi (fun _ : Fin 1024 => noisy)
    {S | ∫ b, empiricalRisk zeroOne S b ∂prior < 2 / 5} ≤ ENNReal.ofReal (1 / 16) := by
  refine (measure_mono fun S hS => ?_).trans (measure_pi_exists_integral_risk_gt_log_div
    (D := noisy) measurable_zeroOne zeroOne_mem_Icc (by norm_num) prior
    (by norm_num : (0 : ℝ) < 1 / 16))
  refine ⟨prior, inferInstance, by simp [klDiv_self], ?_⟩
  have hlog : (klDiv prior prior).toReal + Real.log ((1024 : ℕ) / (1 / 16)) ≤ 15 := by
    rw [klDiv_self, ENNReal.toReal_zero, zero_add,
      show ((1024 : ℕ) : ℝ) / (1 / 16) = 2 ^ 14 by norm_num, Real.log_pow]
    push_cast
    linarith [log_two_le_one]
  have hrisk : ∫ b, trueRisk zeroOne noisy b ∂prior = 1 / 2 := by
    simp only [trueRisk_noisy, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hrisk]
  linarith [sqrt_margin_lt _ hlog, show ∫ b, empiricalRisk zeroOne S b ∂prior < 2 / 5 from hS]

/-- A posterior that charges a hypothesis outside the support of the prior has infinite
divergence, so the bounds exclude it. -/
example : klDiv (Measure.dirac true) (Measure.dirac false) = ⊤ :=
  klDiv_of_not_ac fun h => by simpa using h (s := {true})

/-- The hypothesis `2 ≤ m` is needed: at `m = 1` the margin divides by `2 (m - 1) = 0` and
vanishes, and the one-example sample `(false, true)`, which has probability `1 / 2` under
`noisy`, gives the constant `true` empirical risk `0` against true risk `1 / 2`. -/
example (c : ℝ) : empiricalRisk zeroOne ![((false, true) : Bool × Bool)] true +
    Real.sqrt (c / (2 * ((1 : ℕ) - 1 : ℝ))) < trueRisk zeroOne noisy true := by
  rw [trueRisk_noisy, Nat.cast_one, sub_self, mul_zero, div_zero, Real.sqrt_zero]
  norm_num [empiricalRisk_eq_sum_div, zeroOne]

end CslibFrontierTests.PACBayes
