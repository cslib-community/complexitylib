/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, convolution with a density and a singular measure)

public import Complexity.Init
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Convolution with one density

The first measure may be singular with respect to the invariant reference measure. The second
has a measurable nonnegative density, which may take the value infinity. No probability or
integrability assumption is needed.

## Main results

* `MeasureTheory.mconv_withDensity_eq_withDensity_lintegral`: left convolution integrates the
  translated density against the first measure.
* `MeasureTheory.conv_withDensity_eq_withDensity_lintegral`: the additive version.

## References

This extends Mathlib's `mconv_withDensity_eq_mlconvolution` from two density-bearing measures
to an arbitrary first measure. The proof uses the same weighted-product, invariant-translation
and Tonelli argument. The existing convolution and density definitions are reused.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {σ μ : Measure G} [SFinite σ] [SFinite μ] [μ.IsMulLeftInvariant]

/-- Convolving an arbitrary s-finite measure with a density integrates its left translates.
The first measure need not have a density, and the density may be infinite. -/
@[to_additive /-- Convolving an arbitrary s-finite measure with a density integrates its translates.
The first measure need not have a density, and the density may be infinite. -/]
theorem mconv_withDensity_eq_withDensity_lintegral {f : G → ℝ≥0∞} (hf : Measurable f) :
    σ ∗ₘ μ.withDensity f = μ.withDensity (fun x ↦ ∫⁻ y, f (y⁻¹ * x) ∂σ) := by
  have hd : Measurable (fun x ↦ ∫⁻ y, f (y⁻¹ * x) ∂σ) :=
    (hf.comp (measurable_fst.inv.mul measurable_snd)).lintegral_prod_left'
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [Measure.lintegral_mconv_eq_lintegral_prod hφ, prod_withDensity_right hf,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_prod _ (by fun_prop), lintegral_withDensity_eq_lintegral_mul _ hd hφ]
  calc
    _ = ∫⁻ y, ∫⁻ x, f (y⁻¹ * x) * φ x ∂μ ∂σ := by
      apply lintegral_congr
      intro y
      rw [← lintegral_mul_left_eq_self (fun x ↦ f (y⁻¹ * x) * φ x) y]
      simp only [Pi.mul_apply, inv_mul_cancel_left]
    _ = _ := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      apply lintegral_congr
      intro x
      exact lintegral_mul_const'' _ (by fun_prop)

end MeasureTheory
