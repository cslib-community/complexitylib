/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.AgnosticVCSharp
import CslibFrontierTests.AgnosticVC
import CslibFrontierTests.AgnosticVCSharpModule

/-! Checks for the sharp agnostic sample size, for thresholds on `ℕ` under the non-realizable
distribution `CslibFrontierTests.AgnosticVC.noisy`. -/

namespace CslibFrontierTests.AgnosticVCSharp

open Cslib.MachineLearning.PACLearning MeasureTheory
open CslibFrontierTests.RealizablePAC (thresholds card_le_one_of_setShatters_thresholds
  hasFiniteVCDim_thresholds)
open CslibFrontierTests.AgnosticVC (noisy optimalError_noisy_thresholds tenth)
open scoped NNReal ENNReal

/-- Uniform convergence for thresholds under `noisy`, with no growth-function factor. -/
example {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hm : 16384 ≤ m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => noisy) {S | ¬ IsRepresentative noisy thresholds ε S} ≤
      ENNReal.ofReal (4 * Real.exp (-(m * ε ^ 2 / 32))) :=
  measure_pi_not_isRepresentative_le_exp noisy
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) hε (by simpa using hm)

/-- An empirical risk minimizer for thresholds under `noisy` is within `ε` of the optimal error
`1 / 4` except with probability `4 exp (-m ε² / 128)`. -/
example {m : ℕ} {A : Learner ℕ Bool m} (hA : IsERM A thresholds) {ε : ℝ} (hε : 0 ≤ ε)
    (hm : 65536 ≤ m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => noisy) {S | 2⁻¹ * 2⁻¹ + ENNReal.ofReal ε < error noisy (A S)} ≤
      ENNReal.ofReal (4 * Real.exp (-(m * ε ^ 2 / 128))) := by
  simpa only [optimalError_noisy_thresholds] using
    hA.measure_pi_lt_error_le_exp noisy (fun _ hW => card_le_one_of_setShatters_thresholds hW) hε
      (by simpa using hm)

/-- **An explicit sharp agnostic sample size**: `6607000` examples learn thresholds on `ℕ` to
accuracy and confidence `1 / 10` under every distribution, including `noisy`. -/
theorem isPACLearnerFor_thresholds_univ_chaining :
    IsPACLearnerFor 6607000 tenth tenth thresholds Set.univ := by
  refine isPACLearnerFor_univ_of_chainingSampleSize_le
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) ?_
  simp only [tenth, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, Nat.cast_ofNat]
  exact chainingSampleSize_tenth_le

/-- The agnostic sample complexity of thresholds at `(1 / 10, 1 / 10)` is at most `6607000`. -/
example : sampleComplexity IsPACLearnerFor thresholds tenth tenth Set.univ ≤ 6607000 :=
  Nat.sInf_le isPACLearnerFor_thresholds_univ_chaining

/-- The general sample-complexity bound, instantiated at thresholds. -/
example : sampleComplexity IsPACLearnerFor thresholds tenth tenth Set.univ ≤
    ⌈chainingSampleSize (vcDim thresholds) ((tenth.val : ℝ) / 2) tenth.val⌉₊ :=
  sampleComplexity_univ_le_chainingSampleSize hasFiniteVCDim_thresholds tenth tenth

end CslibFrontierTests.AgnosticVCSharp
