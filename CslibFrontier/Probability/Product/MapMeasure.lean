/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Finite images of product measures

Applying almost everywhere measurable maps into finite types coordinatewise to an independent
sample from a product of probability measures gives an independent sample from the product of the
image distributions. This turns statements about a finite statistic of i.i.d. samples on an
arbitrary measurable space, such as the number of samples in an event, into statements about the
finite product `Cslib.Probability.PMF.pi`, where the PMF concentration bounds apply: Hoeffding's
`Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge` and the Chernoff bounds such as
`Cslib.Probability.PMF.pi_sum_le_one_sub_mul`.

## Main results

* `Cslib.Probability.PMF.map_measurePi_eq_toMeasure_pi`: the image of `Measure.pi μ` under
  coordinatewise almost everywhere measurable maps into finite types is the product of the image
  PMFs.
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory

/-- The image of a product of probability measures under coordinatewise almost everywhere
measurable maps into finite types is the measure of the product of the image distributions. -/
theorem map_measurePi_eq_toMeasure_pi {ι : Type*} [Fintype ι] {Z β : ι → Type*}
    [∀ i, MeasurableSpace (Z i)] [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)]
    [∀ i, Finite (β i)] (μ : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : ∀ i, Z i → β i} (hg : ∀ i, AEMeasurable (g i) (μ i)) :
    (Measure.pi μ).map (fun z i => g i (z i)) =
      (pi fun i => ((μ i).map (g i)).toPMF).toMeasure := by
  simp only [toMeasure_pi, Measure.toPMF_toMeasure]
  exact Measure.pi_map_pi hg

end Cslib.Probability.PMF
