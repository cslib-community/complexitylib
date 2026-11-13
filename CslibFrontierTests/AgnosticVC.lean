/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.AgnosticVC
import CslibFrontierTests.RealizablePAC

/-! Checks for agnostic PAC learning of an infinite class of finite VC dimension: a noisy
distribution on `ℕ × Bool` that thresholds do not realize, under which their optimal error is
`1 / 4` and the constant learner fails; uniform convergence and the ERM tail bound for thresholds
under it; and an explicit agnostic sample size for thresholds, with the resulting sample-complexity
bound and agnostic PAC learnability. -/

namespace CslibFrontierTests.AgnosticVC

open Cslib.MachineLearning.PACLearning MeasureTheory
open CslibFrontierTests.RealizablePAC (thresholds card_le_one_of_setShatters_thresholds
  hasFiniteVCDim_thresholds)
open scoped NNReal ENNReal

/-! ### A noisy distribution on `ℕ × Bool` -/

/-- The point `0` labeled `false` with probability `1 / 2`, and the point `1` labeled `true` or
`false` with probability `1 / 4` each. -/
noncomputable def noisy : Measure (ℕ × Bool) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (0, false) +
    (2⁻¹ : ℝ≥0∞) • ((2⁻¹ : ℝ≥0∞) • Measure.dirac (1, true) +
      (2⁻¹ : ℝ≥0∞) • Measure.dirac (1, false))

instance : IsProbabilityMeasure noisy := by
  constructor
  simp only [noisy, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    ENNReal.inv_two_add_inv_two]

/-- The error of a hypothesis under `noisy` from its values at `0` and `1`. -/
theorem error_noisy (h : ℕ → Bool) :
    error noisy h = (if h 0 = false then 0 else 2⁻¹) + 2⁻¹ * 2⁻¹ := by
  cases h0 : h 0 <;> cases h1 : h 1 <;> simp [noisy, error, h0, h1]

/-- Every hypothesis errs with probability at least `1 / 4` under `noisy`, since the point `1`
carries both labels. -/
theorem le_error_noisy (h : ℕ → Bool) : 2⁻¹ * 2⁻¹ ≤ error noisy h := by
  rw [error_noisy]
  exact le_add_self

/-- `noisy` is realizable by no class, so the realizable-case theorems say nothing about it. -/
example (C : ConceptClass ℕ Bool) : noisy ∉ realizableDistributions C := by
  rintro ⟨h, -, hh⟩
  have := le_error_noisy h
  rw [hh, nonpos_iff_eq_zero] at this
  simp at this

/-- The threshold at `1` attains the best possible error `1 / 4`. -/
theorem optimalError_noisy_thresholds : optimalError noisy thresholds = 2⁻¹ * 2⁻¹ := by
  refine le_antisymm (iInf₂_le (fun x => decide (1 ≤ x)) ⟨1, rfl⟩ |>.trans_eq ?_) ?_
  · simp [error_noisy]
  · exact le_iInf₂ fun h _ => le_error_noisy h

/-! ### Uniform convergence and ERM for thresholds -/

/-- Uniform convergence for thresholds under `noisy`: since `Π(2m) ≤ 2m + 1`, the probability that
some threshold's empirical error is off by at least `ε` is at most
`4 (2m + 1) exp (-m ε² / 8)`. -/
example (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => noisy)
        {S | ∃ h ∈ thresholds, ε ≤ |(empiricalMiscount h S : ℝ) / m - (error noisy h).toReal|} ≤
      ENNReal.ofReal (4 * (m + m + 1 : ℕ) * Real.exp (-(m * ε ^ 2 / 8))) := by
  refine (measure_pi_exists_le_abs_empiricalMiscount_div_sub_error_le noisy thresholds m hε).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := growthFunction_le_add_one_pow (fun W hW => card_le_one_of_setShatters_thresholds hW)
    (C := thresholds) (m + m)
  rw [pow_one] at h
  have : (growthFunction thresholds (m + m) : ℝ) ≤ (m + m + 1 : ℕ) := by exact_mod_cast h
  gcongr

/-- An empirical risk minimizer for thresholds under `noisy` has error at most `1 / 4 + ε` except
with probability `4 Π(2m) exp (-m ε² / 32)`. -/
example {m : ℕ} {A : Learner ℕ Bool m} (hA : IsERM A thresholds) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => noisy) {S | 2⁻¹ * 2⁻¹ + ENNReal.ofReal ε < error noisy (A S)} ≤
      ENNReal.ofReal (4 * growthFunction thresholds (m + m) * Real.exp (-(m * ε ^ 2 / 32))) := by
  simpa only [optimalError_noisy_thresholds] using hA.measure_pi_lt_error_le_growthFunction noisy hε

/-! ### An explicit agnostic sample size -/

/-- `1 / 10` as an accuracy or confidence parameter. -/
noncomputable def tenth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 10, by norm_num, by norm_num⟩

/-- The learning sample size of thresholds at `ε = δ = 1 / 10` is
`6400 (2 log 200 + log 40) ≤ 6400 · 22 log 2 ≤ 97600`, since `200 ≤ 2 ^ 8` and `40 ≤ 2 ^ 6`. -/
theorem uniformConvergenceSampleSize_tenth_le :
    uniformConvergenceSampleSize 1 ((1 / 10 : ℝ) / 2) (1 / 10) ≤ 97600 := by
  have h200 : Real.log (10 / ((1 / 10 : ℝ) / 2)) ≤ 8 * Real.log 2 := by
    calc Real.log (10 / ((1 / 10 : ℝ) / 2)) ≤ Real.log ((2 : ℝ) ^ 8) :=
          Real.log_le_log (by norm_num) (by norm_num)
      _ = 8 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h40 : Real.log (4 / (1 / 10 : ℝ)) ≤ 6 * Real.log 2 := by
    calc Real.log (4 / (1 / 10 : ℝ)) ≤ Real.log ((2 : ℝ) ^ 6) :=
          Real.log_le_log (by norm_num) (by norm_num)
      _ = 6 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [uniformConvergenceSampleSize, show (16 : ℝ) / ((1 / 10 : ℝ) / 2) ^ 2 = 6400 by norm_num]
  push_cast
  nlinarith [Real.log_two_lt_d9]

/-- **An explicit agnostic sample size**: `97600` examples learn thresholds on `ℕ` to accuracy and
confidence `1 / 10` under every distribution, including `noisy`. -/
theorem isPACLearnerFor_thresholds_univ :
    IsPACLearnerFor 97600 tenth tenth thresholds Set.univ := by
  refine isPACLearnerFor_univ_of_uniformConvergenceSampleSize_le
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) ?_
  simp only [tenth, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, Nat.cast_ofNat]
  exact uniformConvergenceSampleSize_tenth_le

/-- The agnostic sample complexity of thresholds at `(1 / 10, 1 / 10)` is at most `97600`. -/
example : sampleComplexity IsPACLearnerFor thresholds tenth tenth Set.univ ≤ 97600 :=
  Nat.sInf_le isPACLearnerFor_thresholds_univ

/-- Thresholds on `ℕ` are agnostically PAC learnable. -/
example : IsPACLearnable thresholds Set.univ :=
  isPACLearnable_univ_of_hasFiniteVCDim hasFiniteVCDim_thresholds

/-- Not every learner works: the learner that always predicts `true` (the threshold at `0`) has
error `3 / 4 > 1 / 4 + 1 / 10` under `noisy` on every sample. -/
example (m : ℕ) :
    ¬ ∀ D : Measure (ℕ × Bool), ∀ [IsProbabilityMeasure D],
      Measure.pi (fun _ : Fin m => D)
          {S | optimalError D thresholds + ↑tenth.val <
            error D ((fun _ _ => true : Learner ℕ Bool m) S)} ≤ ↑tenth.val := by
  intro h
  have key := h noisy
  have hset : {S : LabeledSample ℕ Bool m | optimalError noisy thresholds + ↑tenth.val <
      error noisy ((fun _ _ => true : Learner ℕ Bool m) S)} = Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    change optimalError noisy thresholds + ↑tenth.val < error noisy fun _ => true
    rw [optimalError_noisy_thresholds, error_noisy, tenth]
    simp only [Bool.true_eq_false, ite_false]
    rw [← ENNReal.coe_two, ← ENNReal.coe_inv two_ne_zero, ← ENNReal.coe_mul, ← ENNReal.coe_add,
      ← ENNReal.coe_add, ENNReal.coe_lt_coe]
    norm_num
  rw [hset, measure_univ, tenth] at key
  exact absurd key (by exact_mod_cast (by norm_num : ¬ (1 : ℝ≥0) ≤ 1 / 10))

end CslibFrontierTests.AgnosticVC
