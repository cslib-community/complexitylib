/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.Compression.VCDimension
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-! Checks for voting over subsamples on the thresholds `x < θ` on `ℕ`, which shatter no two
points. Take a consistent learner reading `⌈vcSampleSize 1 (1/3) (1/2)⌉` examples. For every
nonempty realizable sample, some distribution on subsamples makes it wrong at each example with
probability at most `1/3`. -/

namespace CslibFrontierTests.VCCompression

open Cslib.MachineLearning.PACLearning Cslib.MachineLearning.OnlineLearning.MistakeBound

/-- The thresholds on `ℕ` shatter no two points. -/
theorem card_le_one_of_setShatters_thresholdClass (W : Finset ℕ)
    (hW : SetShatters thresholdClass ↑W) : W.card ≤ 1 :=
  not_lt.1 fun h => not_setShatters_thresholdClass h hW

/-- Voting over subsamples for the thresholds, at accuracy `1/3` and confidence `1/2`. -/
theorem exists_pmf_subsample {m : ℕ} (hm : 0 < m) {S : LabeledSample ℕ Bool m}
    (hS : Realizable thresholdClass S) :
    ∃ A : Learner ℕ Bool ⌈vcSampleSize 1 (1 / 3) (1 / 2)⌉₊, ∃ μ : PMF (Fin _ → Fin m),
      ∀ i, μ.toOuterMeasure {b | A (S ∘ b) (S i).1 ≠ (S i).2} ≤ ENNReal.ofReal (1 / 3) := by
  obtain ⟨A, hA⟩ := exists_isConsistent (m := ⌈vcSampleSize 1 (1 / 3) (1 / 2)⌉₊)
    ⟨_, mem_thresholdClass.2 ⟨0, rfl⟩⟩
  exact ⟨A, hA.exists_pmf_subsample_toOuterMeasure_le card_le_one_of_setShatters_thresholdClass
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Nat.le_ceil _) hm hS⟩

/-- A concrete realizable sample: `0` is below the threshold `1` and `5` is not. -/
example : ∃ A : Learner ℕ Bool ⌈vcSampleSize 1 (1 / 3) (1 / 2)⌉₊, ∃ μ : PMF (Fin _ → Fin 2),
    ∀ i, μ.toOuterMeasure {b | A (![(0, true), (5, false)] ∘ b) (![(0, true), (5, false)] i).1 ≠
      (![(0, true), (5, false)] i).2} ≤ ENNReal.ofReal (1 / 3) :=
  exists_pmf_subsample (by norm_num)
    ⟨_, mem_thresholdClass.2 ⟨1, rfl⟩, by decide⟩

end CslibFrontierTests.VCCompression
