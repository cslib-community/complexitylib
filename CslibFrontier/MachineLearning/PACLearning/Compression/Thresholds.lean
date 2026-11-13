/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Order
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-!
# Compression for the thresholds of the mistake-bound development

The thresholds `x < θ` on `ℕ` (`thresholdClass`) have infinite Littlestone dimension
(`littlestoneDim_thresholdClass`), so no deterministic online learner has a finite mistake bound
for them and the scheme from a mistake bound (`SampleCompressionScheme.ofMistakeBound`) does not
apply. They are lower-set concepts, however, so the size-`1` threshold scheme `lowerSetScheme`
compresses them, and the compression bound makes them PAC learnable in the realizable setting.

This module joins the online and compression developments, so that the order schemes
(`CslibFrontier/MachineLearning/PACLearning/Compression/Order.lean`) and the online threshold module
need not import each other.

## Main results

- `thresholdClass_subset_lowerSetClass`: every threshold `x < θ` on `ℕ` is a lower-set concept.
- `isPACLearnable_thresholdClass`: the thresholds on `ℕ` are PAC learnable in the realizable
  setting.
-/

public section

namespace Cslib.MachineLearning.PACLearning

open OnlineLearning.MistakeBound

/-- The thresholds `x < θ` on `ℕ` of the mistake-bound development are lower-set concepts. Their
Littlestone dimension is infinite (`littlestoneDim_thresholdClass`), so the scheme from a mistake
bound does not apply, but `lowerSetScheme` compresses them to one example. -/
theorem thresholdClass_subset_lowerSetClass : thresholdClass ⊆ lowerSetClass ℕ := by
  intro c hc
  obtain ⟨θ, rfl⟩ := mem_thresholdClass.1 hc
  refine mem_lowerSetClass.2 fun x y hyx hx => ?_
  simp only [thresholdConcept_apply, decide_eq_true_eq] at hx ⊢
  omega

/-- The thresholds `x < θ` on `ℕ` are PAC learnable in the realizable setting, although no online
learner learns them with finitely many mistakes. -/
theorem isPACLearnable_thresholdClass :
    IsPACLearnable thresholdClass (realizableDistributions thresholdClass) :=
  (lowerSetScheme.ofSubset thresholdClass_subset_lowerSetClass).isPACLearnable
    (measurableReconstruction_of_countable _)

end Cslib.MachineLearning.PACLearning
