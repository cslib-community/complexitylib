/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.Compression.VCDimension
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-! Checks for the Moran–Yehudayoff construction on the thresholds `x < θ` on `ℕ`, which shatter
no two points. Take a consistent learner reading `⌈vcSampleSize 1 (1/3) (1/2)⌉` examples. For
every nonempty realizable sample, some distribution on subsamples makes it wrong at each example
with probability at most `1/3`. The resulting compression scheme for VC dimension `1` keeps at most
`6921 * 244` examples, and through the compression bound it learns the thresholds. -/

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

/-- The Moran–Yehudayoff scheme for the thresholds. -/
noncomputable def thresholdScheme : SampleCompressionScheme thresholdClass (vcCompressionSize 1) :=
  SampleCompressionScheme.ofVCDim card_le_one_of_setShatters_thresholdClass

/-- Through the compression bound, the scheme learns the thresholds. -/
example : IsPACLearnable thresholdClass (realizableDistributions thresholdClass) :=
  thresholdScheme.isPACLearnable (measurableReconstruction_of_countable _)

/-- For VC dimension `1` the scheme keeps at most `6921 * 244` examples: at most
`⌈256 (6 log 40 + log 8)⌉ ≤ 6921` subsamples of `⌈32 (log 192 + log 8)⌉ ≤ 244` examples each,
from `log 40 ≤ 6 log 2`, `log 192 ≤ 8 log 2` and `log 8 = 3 log 2`. -/
example : vcCompressionSize 1 ≤ 6921 * 244 := by
  have hlog2 := Real.log_two_lt_d9
  have hlog (x : ℝ) (n : ℕ) (hx : 0 < x) (h : x ≤ 2 ^ n) : Real.log x ≤ n * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log hx h
  have hs : vcCompressionBlockSize 1 ≤ 244 := by
    rw [vcCompressionBlockSize, Nat.ceil_le, vcSampleSize]
    have h1 := hlog (48 / (1 / 4)) 8 (by norm_num) (by norm_num)
    have h2 := hlog (4 / (1 / 2)) 3 (by norm_num) (by norm_num)
    push_cast at h1 h2 ⊢
    nlinarith
  have hT : vcCompressionBlockCount 1 ≤ 6921 := by
    rw [vcCompressionBlockCount, Nat.ceil_le, uniformConvergenceSampleSize]
    have h1 := hlog (10 / (1 / 4)) 6 (by norm_num) (by norm_num)
    have h2 := hlog (4 / (1 / 2)) 3 (by norm_num) (by norm_num)
    push_cast at h1 h2 ⊢
    nlinarith
  exact Nat.mul_le_mul hT hs

end CslibFrontierTests.VCCompression
