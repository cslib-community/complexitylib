/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.DualVCDimension
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-! Checks for the dual class: Assouad's bound for the thresholds `x < θ` on `ℕ`, which have VC
dimension `1`, and a one-threshold family that the dual class shatters. -/

namespace CslibFrontierTests.DualVCDimension

open Cslib.MachineLearning.PACLearning Cslib.MachineLearning.OnlineLearning.MistakeBound

/-- The thresholds on `ℕ` shatter no two points. -/
theorem card_le_one_of_setShatters_thresholdClass (W : Finset ℕ)
    (hW : SetShatters thresholdClass ↑W) : W.card ≤ 1 :=
  not_lt.1 fun h => not_setShatters_thresholdClass h hW

/-- So the dual class of the thresholds shatters at most `2 ^ 2 - 1 = 3` thresholds. -/
example (F : Finset ↥thresholdClass) (hF : SetShatters (dualClass thresholdClass) ↑F) :
    F.card ≤ 3 :=
  card_le_of_setShatters_dualClass card_le_one_of_setShatters_thresholdClass hF

/-- The same bound for `vcDim`. -/
example : vcDim (dualClass thresholdClass) ≤ 3 := by
  have h := vcDim_dualClass_le
    (hasFiniteVCDim_iff.2 ⟨1, card_le_one_of_setShatters_thresholdClass⟩)
  rwa [vcDim_thresholdClass] at h

/-- The threshold `x < 1` as a concept of `thresholdClass`. -/
def one : ↥thresholdClass := ⟨thresholdConcept 1, mem_thresholdClass.2 ⟨1, rfl⟩⟩

/-- The dual class shatters the family `{x < 1}`: the point `0` lies below the threshold and the
point `1` does not. -/
example : SetShatters (dualClass thresholdClass) {one} := by
  intro V hV
  rcases Set.subset_singleton_iff_eq.1 hV with rfl | rfl
  · refine ⟨_, mem_dualClass.2 ⟨1, rfl⟩, Set.eq_empty_of_forall_notMem fun c ⟨hc, hc1⟩ => ?_⟩
    rw [Set.mem_singleton_iff.1 hc1] at hc
    simp [one, thresholdConcept_apply] at hc
  · refine ⟨_, mem_dualClass.2 ⟨0, rfl⟩, Set.ext fun c => ⟨fun h => h.2, fun hc => ⟨?_, hc⟩⟩⟩
    rw [Set.mem_singleton_iff.1 hc]
    simp [one, thresholdConcept_apply]

end CslibFrontierTests.DualVCDimension
