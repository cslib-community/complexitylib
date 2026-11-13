/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.EpsilonApproximation

/-! Checks for ε-approximations: the class of all Boolean functions on `Bool` shatters at most two
points, so under every probability measure on `Bool` it has a `1/4`-approximation of
`⌈uniformConvergenceSampleSize 2 (1/4) (1/2)⌉` points. Under the point mass at `true` such a
sequence must contain `true`. -/

namespace CslibFrontierTests.EpsilonApproximation

open MeasureTheory Cslib.MachineLearning.PACLearning

/-- A `1/4`-approximation for all Boolean functions on `Bool`, under any probability measure. -/
theorem exists_isEpsApprox_bool (μ : Measure Bool) [IsProbabilityMeasure μ] :
    ∃ S : Fin ⌈uniformConvergenceSampleSize 2 (1 / 4) (1 / 2)⌉₊ → Bool,
      IsEpsApprox μ Set.univ (1 / 4) S :=
  exists_isEpsApprox_of_uniformConvergenceSampleSize_le _ (fun W _ => W.card_le_univ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Nat.le_ceil _)

/-- A `1/4`-approximation under the point mass at `true` contains `true`: the relative frequency
of `true` is within `1/4` of `1`. -/
example {m : ℕ} {S : Fin m → Bool} (hS : IsEpsApprox (Measure.dirac true) Set.univ (1 / 4) S) :
    ∃ i, S i = true := by
  have h := hS id (Set.mem_univ _)
  have hμ : ((Measure.dirac true) {z : Bool | id z = true}).toReal = 1 := by
    rw [Measure.dirac_apply_of_mem (by simp)]
    simp
  rw [hμ] at h
  by_contra hne
  simp only [not_exists, Bool.not_eq_true] at hne
  have : (Finset.univ.filter fun i => id (S i) = true) = ∅ :=
    Finset.filter_false_of_mem fun i _ => by simp [hne i]
  rw [this, Finset.card_empty, Nat.cast_zero, zero_div, zero_sub, abs_neg] at h
  norm_num [abs_of_pos] at h

end CslibFrontierTests.EpsilonApproximation
