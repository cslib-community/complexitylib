/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound
public import CslibFrontierTests.NatarajanDimension

/-!
# Checks for the multiclass realizable upper bound

Exercises `CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound` on the constant functions
from `ℕ` to `Fin 3`, a class of Natarajan dimension `1` on an infinite countable domain:

* **Loss class growth:** Natarajan's lemma bounds the growth function of its loss class by
  `natarajanSum m 3 1 = 1 + 3 m`.
* **Learnability:** the class is PAC learnable in the realizable setting, with realizable sample
  complexity at most `⌈(8 / ε) (log (48 / ε) + 2 log 3 + log (4 / δ))⌉`.
* **Sample sizes:** the multiclass sample size is the VC sample size at the reduced confidence
  `δ / k ^ (2 d)`; with `d = 0` it does not depend on the number of labels.
-/

public section

namespace CslibFrontierTests.NatarajanUpperBound

open Cslib.MachineLearning.PACLearning CslibFrontierTests.NatarajanDimension
open scoped NNReal

/-- The constant functions from `ℕ` to `Fin 3` N-shatter no finite set of more than one point. -/
theorem card_le_one_of_natarajanShatters (W : Finset ℕ)
    (hW : NatarajanShatters (constants (α := ℕ) (Fin 3)) ↑W) : W.card ≤ 1 :=
  card_le_one_of_natarajanShatters_constants hW

/-- The loss class of the constants to `Fin 3` realizes at most `1 + 3 m` patterns on `m` labeled
points. -/
example (m : ℕ) : growthFunction (lossClass (constants (α := ℕ) (Fin 3))) m ≤ 1 + m * 3 := by
  have h := growthFunction_lossClass_le_natarajanSum card_le_one_of_natarajanShatters m
  simpa [natarajanSum, Finset.sum_range_succ] using h

/-- The constants to `Fin 3` are PAC learnable in the realizable setting. -/
example : IsPACLearnable (constants (α := ℕ) (Fin 3))
    (realizableDistributions (constants (α := ℕ) (Fin 3))) :=
  isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim
    (hasFiniteNatarajanDim_iff.2 ⟨1, card_le_one_of_natarajanShatters⟩)

/-- The realizable sample complexity of the constants to `Fin 3`, through their Natarajan
dimension `1`. -/
example (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor (constants (α := ℕ) (Fin 3)) ε δ
        (realizableDistributions (constants (α := ℕ) (Fin 3))) ≤
      ⌈natarajanSampleSize 1 3 ε.val δ.val⌉₊ := by
  have h := sampleComplexity_realizableDistributions_le_of_hasFiniteNatarajanDim
    (hasFiniteNatarajanDim_iff.2 ⟨1, card_le_one_of_natarajanShatters⟩) ε δ
  rwa [natarajanDim_constants (by decide : (0 : Fin 3) ≠ 1), Fintype.card_fin] at h

/-- With `Bool` labels the multiclass sample size is the VC sample size at confidence
`δ / 4 ^ d`. -/
example (d : ℕ) (ε δ : ℝ) (hδ : 0 < δ) :
    natarajanSampleSize d (Fintype.card Bool) ε δ = vcSampleSize d ε (δ / 4 ^ d) := by
  rw [natarajanSampleSize_eq_vcSampleSize d Fintype.card_pos ε hδ, Fintype.card_bool, pow_mul]
  norm_num

/-- A class that N-shatters only the empty set needs the VC sample size for `d = 0`, whatever the
number of labels. -/
example (k : ℕ) (ε δ : ℝ) : natarajanSampleSize 0 k ε δ = vcSampleSize 0 ε δ := by
  simp [natarajanSampleSize, vcSampleSize]

end CslibFrontierTests.NatarajanUpperBound
