/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.Compression.Order
import CslibFrontier.MachineLearning.PACLearning.Compression.MistakeBound
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Halving
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-! Checks for sample compression schemes: the threshold and interval schemes on concrete samples,
including a non-realizable sample on which the threshold reconstruction errs; explicit sample sizes
for thresholds and intervals on `ℝ`; the halving algorithm's compression scheme on a concrete
sample; and an explicit sample size for thresholds on `ℕ` from their Littlestone dimension. -/

namespace CslibFrontierTests.SampleCompression

open Cslib.MachineLearning.PACLearning Cslib.MachineLearning.OnlineLearning.MistakeBound
open MeasureTheory
open scoped NNReal

/-! ### Thresholds and intervals -/

/-- A sample labelled by the threshold `x ≤ 4`. -/
def thresholdSample : LabeledSample ℕ Bool 4 := ![(3, true), (7, false), (4, true), (0, true)]

theorem realizable_thresholdSample : Realizable (lowerSetClass ℕ) thresholdSample :=
  ⟨fun x => decide (x ≤ 4), mem_lowerSetClass.2 fun x y hyx hx => by
    simp only [decide_eq_true_eq] at hx ⊢; omega, by decide⟩

/-- The threshold scheme keeps only the largest positive example. -/
example : lowerSetScheme.compress thresholdSample = [2] := by decide

/-- The kept example `(4, true)` reconstructs the labels of the whole sample. -/
example : ∀ i, lowerSetScheme.learner thresholdSample (thresholdSample i).1 =
    (thresholdSample i).2 := by decide

/-- On a sample that no threshold realizes, the reconstruction from the largest positive example
mislabels the smaller negative one: realizability is needed. -/
example : lowerSetScheme.learner (![(1, false), (2, true)] : LabeledSample ℕ Bool 2) 1 = true := by
  decide

/-- Restricting the interval scheme to thresholds gives a second, size-`2` scheme for them; on the
threshold sample it keeps the smallest and the largest positive example. -/
example : (ordConnectedScheme.mono lowerSetClass_subset_ordConnectedClass).compress
    thresholdSample = [3, 2] := by decide

/-- A sample labelled by the interval `[2, 5]`. -/
def intervalSample : LabeledSample ℕ Bool 5 :=
  ![(4, true), (1, false), (2, true), (8, false), (5, true)]

/-- The interval scheme keeps the smallest and the largest positive example. -/
example : ordConnectedScheme.compress intervalSample = [2, 4] := by decide

example : ∀ i, ordConnectedScheme.learner intervalSample (intervalSample i).1 =
    (intervalSample i).2 := by decide

/-! ### Explicit sample sizes on `ℝ` -/

/-- `1 / 2` as an accuracy or confidence parameter. -/
noncomputable def half : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Five examples learn thresholds on `ℝ` to accuracy and confidence `1 / 2`, because
`6 (1 / 2) ^ 4 ≤ 1 / 2`. -/
theorem isPACLearnerFor_lowerSetClass_five :
    IsPACLearnerFor 5 half half (lowerSetClass ℝ) (realizableDistributions (lowerSetClass ℝ)) :=
  lowerSetScheme.isPACLearnerFor measurableReconstruction_lowerSetScheme (by norm_num [half])

/-- Ten examples learn intervals on `ℝ` to accuracy and confidence `1 / 2`, because
`11 ^ 2 (1 / 2) ^ 8 ≤ 1 / 2`. -/
theorem isPACLearnerFor_ordConnectedClass_ten :
    IsPACLearnerFor 10 half half (ordConnectedClass ℝ)
      (realizableDistributions (ordConnectedClass ℝ)) :=
  ordConnectedScheme.isPACLearnerFor measurableReconstruction_ordConnectedScheme
    (by norm_num [half])

/-! ### Schemes from mistake bounds -/

/-- Three concepts on `Fin 2`: the two constants and the indicator of `1`. -/
def three : Finset (Fin 2 → Bool) := {fun _ => false, fun i => decide (i = 1), fun _ => true}

/-- The halving algorithm makes at most `⌊log₂ 3⌋ = 1` mistake on `three`. -/
theorem mistakeBound_halving_three_le : mistakeBound (halving three) (three : Set _) ≤ (1 : ℕ) :=
  (mistakeBound_halving_le three).trans (by decide)

/-- The size-`1` scheme of the halving algorithm on `three`. -/
def halvingScheme : SampleCompressionScheme (three : Set (Fin 2 → Bool)) 1 :=
  .ofMistakeBound (halving three) mistakeBound_halving_three_le

/-- A sample labelled by the constant `false`. -/
def falseSample : LabeledSample (Fin 2) Bool 3 := ![(0, false), (1, false), (0, false)]

/-- Halving predicts the majority label `true` at `1`, errs on `(1, false)` and keeps it. -/
example : halvingScheme.compress falseSample = [1] := by decide

example : ∀ i, halvingScheme.learner falseSample (falseSample i).1 = (falseSample i).2 := by
  decide

/-- A sample labelled by the indicator of `1`, on which halving makes no mistake: nothing is
kept. -/
example :
    halvingScheme.compress (![(0, false), (1, true)] : LabeledSample (Fin 2) Bool 2) = [] := by
  decide

/-- The thresholds `θ ≤ 3` on `ℕ` have Littlestone dimension `2`, so ten examples learn them to
accuracy and confidence `1 / 2`, because `11 ^ 2 (1 / 2) ^ 8 ≤ 1 / 2`. -/
theorem isPACLearnerFor_thresholdClassUpTo_ten :
    IsPACLearnerFor 10 half half (thresholdClassUpTo 3)
      (realizableDistributions (thresholdClassUpTo 3)) :=
  SampleCompressionScheme.isPACLearnerFor_of_littlestoneDim_le (d := 2)
    (by rw [littlestoneDim_thresholdClassUpTo]; decide) (by norm_num [half])

end CslibFrontierTests.SampleCompression
