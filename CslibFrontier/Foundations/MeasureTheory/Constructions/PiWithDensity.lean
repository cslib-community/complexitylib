/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Measure/WithDensity.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
import CslibFrontier.Foundations.MeasureTheory.Integral.Pi

/-!
# Products of measures with densities

A finite product of σ-finite measures with densities `fᵢ` is the product measure with the density
`x ↦ ∏ i, fᵢ (x i)` (`MeasureTheory.Measure.pi_withDensity`), the `Measure.pi` version of
Mathlib's `prod_withDensity`. The proof evaluates both sides on boxes with Tonelli's theorem for
products of functions of the coordinates, `MeasureTheory.lintegral_fintype_prod_eq_prod`.

## Main results

* `MeasureTheory.Measure.pi_withDensity`: `Measure.pi (fun i => (μ i).withDensity (f i))` is
  `(Measure.pi μ).withDensity fun x => ∏ i, f i (x i)`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

namespace Measure

/-- **A product of measures with densities** has the product density: for σ-finite measures
`μ i` and measurable densities `f i`, `Measure.pi (fun i => (μ i).withDensity (f i))` is
`(Measure.pi μ).withDensity fun x => ∏ i, f i (x i)`. -/
theorem pi_withDensity {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ : (i : ι) → Measure (α i)} [∀ i, SigmaFinite (μ i)] {f : (i : ι) → α i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity fun x => ∏ i, f i (x i) := by
  refine pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), restrict_pi_pi,
    lintegral_fintype_prod_eq_prod hf]
  exact Finset.prod_congr rfl fun i _ => (withDensity_apply _ (hs i)).symm

end Measure

end MeasureTheory
