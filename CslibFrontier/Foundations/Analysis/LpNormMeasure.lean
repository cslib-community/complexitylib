/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.LpNorm
public import Cslib.Probability.PMF
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Measure-theoretic bridge for finite `L^p` norms

On a nonempty finite type `α` with measurable singletons and `0 < p`, `Cslib.lpNorm p f` agrees
with Mathlib's `MeasureTheory.lpNorm` with respect to both `ProbabilityTheory.uniformOn Set.univ`
(`Cslib.lpNorm_eq_measureTheory_lpNorm_uniformOn`) and CSLib's
`(Probability.PMF.uniformOfFintype α).toMeasure` (`Cslib.lpNorm_eq_measureTheory_lpNorm`).

## Main results

* `Cslib.lpNorm_eq_measureTheory_lpNorm_uniformOn`: agreement with `MeasureTheory.lpNorm` under
  `ProbabilityTheory.uniformOn Set.univ`.
* `Cslib.lpNorm_eq_measureTheory_lpNorm`: agreement with `MeasureTheory.lpNorm` under
  `(Probability.PMF.uniformOfFintype α).toMeasure`.
-/

@[expose] public section

namespace Cslib

open Finset
open scoped BigOperators ENNReal

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- For `0 < p` on a nonempty finite type with measurable singletons, `lpNorm p f` is Mathlib's
`MeasureTheory.lpNorm` with respect to `ProbabilityTheory.uniformOn Set.univ`. -/
theorem lpNorm_eq_measureTheory_lpNorm_uniformOn {p : ℝ} (hp : 0 < p) (f : α → ℝ) :
    lpNorm p f =
      MeasureTheory.lpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hf : MeasureTheory.AEStronglyMeasurable f (ProbabilityTheory.uniformOn Set.univ) :=
    MeasureTheory.AEStronglyMeasurable.of_discrete
  rw [MeasureTheory.lpNorm,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, one_div, ← ENNReal.toReal_rpow, MeasureTheory.lintegral_fintype,
    lpNorm]
  congr 1
  have hcard : (Fintype.card α : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hsing (x : α) :
      ProbabilityTheory.uniformOn (Set.univ : Set α) {x} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [ProbabilityTheory.uniformOn_univ, MeasureTheory.Measure.count_singleton, one_div]
  simp_rw [hsing]
  rw [ENNReal.toReal_sum fun x _ =>
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le enorm_ne_top) hcard]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm, Real.norm_eq_abs,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.expect_eq_sum_div_card, div_eq_mul_inv,
    Finset.sum_mul]

/-- For `0 < p` on a nonempty finite type with measurable singletons, `lpNorm p f` is Mathlib's
`MeasureTheory.lpNorm` with respect to `(PMF.uniformOfFintype α).toMeasure`. -/
theorem lpNorm_eq_measureTheory_lpNorm {p : ℝ} (hp : 0 < p) (f : α → ℝ) :
    lpNorm p f =
      MeasureTheory.lpNorm f (ENNReal.ofReal p) (Probability.PMF.uniformOfFintype α).toMeasure := by
  rw [lpNorm_eq_measureTheory_lpNorm_uniformOn hp f]
  congr 2
  refine MeasureTheory.Measure.ext_of_singleton fun x => ?_
  rw [ProbabilityTheory.uniformOn_univ, MeasureTheory.Measure.count_singleton, one_div,
    PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x),
    Probability.PMF.uniformOfFintype_apply]

end Cslib
