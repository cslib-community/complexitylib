/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, full-L1 total variation under measurable maps)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation under measurable maps

## Main results

* `MeasureTheory.etvDist_map_le`: a measurable map contracts extended total variation.
* `MeasureTheory.tvDist_map_le`: the corresponding real-valued inequality.

The finite measures may have different total masses. The existing full-L1 convention is
preserved: the distance between probability measures lies in `[0, 2]`.

## References

This is a measure-level consequence of Mathlib's `VectorMeasure.variation_map_le` and the
existing signed-measure definition of total variation. No new distance is defined.
-/

public section

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Measurable postprocessing cannot increase the extended total variation of finite measures.
No equal-mass or probability assumption is required. -/
theorem etvDist_map_le {f : X → Y} (hf : Measurable f) :
    etvDist (μ.map f) (ν.map f) ≤ etvDist μ ν := by
  have hmap : (μ.map f).toSignedMeasure - (ν.map f).toSignedMeasure =
      (μ.toSignedMeasure - ν.toSignedMeasure).map f := by
    ext s hs
    rw [Measure.toSignedMeasure_sub_apply hs, VectorMeasure.map_apply _ hf hs,
      Measure.toSignedMeasure_sub_apply (hf hs)]
    simp only [Measure.real, Measure.map_apply hf hs]
  simp only [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist]
  rw [hmap]
  exact (VectorMeasure.variation_map_le Set.univ).trans_eq
    (by rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ])

/-- Measurable postprocessing cannot increase the full-L1 distance of finite measures.
Finiteness prevents the real-valued distance from hiding an infinite extended distance. -/
theorem tvDist_map_le {f : X → Y} (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν :=
  ENNReal.toReal_mono (etvDist_ne_top μ ν) (etvDist_map_le μ ν hf)

end MeasureTheory
