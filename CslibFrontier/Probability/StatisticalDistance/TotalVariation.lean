/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
import CslibFrontier.Probability.PMF.Event
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# `CloseTo`, the finite statistical distance and total variation

Three notions measure the distance between PMFs: the all-event relation `CloseTo μ ν ε`
(error in `ℝ≥0∞`, any type), the finite-type metric `dist μ ν` (half the L1 distance, in `ℝ`),
and Mathlib's total variation `etvDist`/`tvDist` of the induced measures (the full L1 distance).
Each is determined by the positive-part sum `∑' a, (μ a - ν a)` of `closeTo_iff_tsum_tsub_le`, so
`CloseTo` is exactly a bound on either distance, with no slack in the coercions.

## Main results

* `Cslib.Probability.closeTo_iff_ofReal_dist_le`: on a finite type,
  `CloseTo μ ν ε ↔ ENNReal.ofReal (dist μ ν) ≤ ε`, for every `ε : ℝ≥0∞`.
* `Cslib.Probability.closeTo_coe_iff_dist_le`, `Cslib.Probability.closeTo_ofReal_iff_dist_le`:
  the same with an `ℝ≥0` error, or a nonnegative real one.
* `Cslib.Probability.closeTo_of_dist_le`, `Cslib.Probability.closeTo_of_dist_le_ofReal`: the
  forward bridges, used by finite-source hashing and approximate sampling.
* `Cslib.Probability.closeTo_iff_etvDist_le`: on any type with measurable singletons,
  `CloseTo μ ν ε ↔ etvDist μ.toMeasure ν.toMeasure ≤ 2 * ε`.
* `Cslib.Probability.closeTo_ofReal_iff_tvDist_le`: the same with `tvDist` and a nonnegative real
  error.
* `Cslib.Probability.PMF.dist_eq_tvDist_toMeasure_div_two`: statistical distance is half of
  `tvDist`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Cslib.Probability.PMF

namespace Cslib.Probability

namespace PMF

variable {α : Type*}

/-- The finite statistical distance is the positive-part sum `∑' a, (μ a - ν a)`. -/
theorem ofReal_dist [Fintype α] (μ ν : PMF α) :
    ENNReal.ofReal (dist μ ν) = ∑' a, (μ a - ν a) := by
  have hpt (a : α) :
      ENNReal.ofReal |(μ a).toReal - (ν a).toReal| = μ a - ν a + (ν a - μ a) := by
    rcases le_total (μ a) (ν a) with h | h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono (ν.apply_ne_top a) h)),
        ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ν.apply_ne_top a),
        ENNReal.ofReal_toReal (μ.apply_ne_top a), tsub_eq_zero_of_le h, zero_add]
    · rw [abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono (μ.apply_ne_top a) h)),
        ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ν.apply_ne_top a),
        ENNReal.ofReal_toReal (μ.apply_ne_top a), tsub_eq_zero_of_le h, add_zero]
  have hcomm := tsum_tsub_comm μ ν
  rw [tsum_fintype, tsum_fintype] at hcomm
  rw [dist_eq, ENNReal.ofReal_div_of_pos two_pos,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _, tsum_fintype]
  simp only [hpt, Finset.sum_add_distrib, ← hcomm, ENNReal.ofReal_ofNat]
  rw [← two_mul, mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Mathlib's total variation distance of PMF measures is twice the positive-part sum. -/
theorem etvDist_toMeasure (μ ν : PMF α) :
    etvDist μ.toMeasure ν.toMeasure = 2 * ∑' a, (μ a - ν a) := by
  let s : Set α := {a | μ a ≤ ν a}
  have hs : MeasurableSet s := by
    have hc : sᶜ.Countable := μ.support_countable.mono fun a ha =>
      (PMF.mem_support_iff μ a).2 (ne_bot_of_gt (not_le.1 ha))
    simpa using hc.measurableSet.compl
  have hle (ρ σ : PMF α) (t : Set α) (ht : MeasurableSet t) (h : ∀ a ∈ t, ρ a ≤ σ a) :
      ρ.toMeasure.restrict t ≤ σ.toMeasure.restrict t :=
    Measure.le_iff'.2 fun u => by
      simp only [Measure.restrict_apply' ht, PMF.toMeasure_apply_eq_toOuterMeasure,
        PMF.toOuterMeasure_apply]
      exact tsum_le_tsum fun a => Set.indicator_le_indicator' fun ha => h a ha.2
  have hahn : IsHahnDecomposition μ.toMeasure ν.toMeasure s :=
    ⟨hs, hle μ ν s hs fun _ ha => ha, hle ν μ sᶜ hs.compl fun _ ha => (not_le.1 ha).le⟩
  simp only [hahn.etvDist_eq, PMF.toMeasure_apply_eq_toOuterMeasure]
  rw [toOuterMeasure_eq_add_tsum_tsub ν μ (s := s) (fun _ ha => ha) fun _ ha => (not_le.1 ha).le,
    toOuterMeasure_eq_add_tsum_tsub μ ν (s := sᶜ) (fun _ ha => (not_le.1 ha).le)
      fun _ ha => not_not.1 ha,
    ENNReal.add_sub_cancel_left (toOuterMeasure_ne_top _ _),
    ENNReal.add_sub_cancel_left (toOuterMeasure_ne_top _ _), ← tsum_tsub_comm, two_mul]

/-- Statistical distance is half of Mathlib's total variation distance `tvDist` of the PMF
measures. -/
theorem dist_eq_tvDist_toMeasure_div_two [Fintype α] (p q : PMF α) :
    dist p q = tvDist p.toMeasure q.toMeasure / 2 := by
  rw [tvDist, etvDist_toMeasure, ← ofReal_dist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofNat, mul_div_cancel_left₀ _ two_ne_zero]

end PMF

variable {α : Type} {μ ν : PMF α}

section Finite

variable [Fintype α]

/-- On a finite type, `CloseTo μ ν ε` holds exactly when `dist μ ν ≤ ε`, for any `ε : ℝ≥0∞`. -/
theorem closeTo_iff_ofReal_dist_le {ε : ℝ≥0∞} :
    CloseTo μ ν ε ↔ ENNReal.ofReal (dist μ ν) ≤ ε := by
  rw [closeTo_iff_tsum_tsub_le, PMF.ofReal_dist]

/-- On a finite type, `CloseTo` with an `ℝ≥0` error is the upstream `PMF.StatisticallyClose`:
a bound on the finite statistical distance. -/
theorem closeTo_coe_iff_dist_le {ε : ℝ≥0} : CloseTo μ ν ε ↔ dist μ ν ≤ ε := by
  rw [closeTo_iff_ofReal_dist_le, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_le_ofReal_iff ε.coe_nonneg]

/-- On a finite type, `CloseTo` with a nonnegative real error is a bound on the finite statistical
distance. -/
theorem closeTo_ofReal_iff_dist_le {ε : ℝ} (hε : 0 ≤ ε) :
    CloseTo μ ν (ENNReal.ofReal ε) ↔ dist μ ν ≤ ε := by
  rw [closeTo_iff_ofReal_dist_le, ENNReal.ofReal_le_ofReal_iff hε]

/-- Finite-support statistical distance bounds `CloseTo` on all events. -/
theorem closeTo_of_dist_le {ε : ℝ≥0} (h : dist μ ν ≤ ε) : CloseTo μ ν ε :=
  closeTo_coe_iff_dist_le.2 h

/-- Real-valued finite-support statistical distance bounds `CloseTo` via `ENNReal.ofReal`, with
no separate `0 ≤ ε` premise. -/
theorem closeTo_of_dist_le_ofReal {ε : ℝ} (h : dist μ ν ≤ ε) : CloseTo μ ν (ENNReal.ofReal ε) :=
  closeTo_iff_ofReal_dist_le.2 (ENNReal.ofReal_le_ofReal h)

end Finite

section TotalVariation

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- On any type with measurable singletons, `CloseTo μ ν ε` holds exactly when the total
variation distance of the induced measures is at most `2 * ε`. -/
theorem closeTo_iff_etvDist_le {ε : ℝ≥0∞} :
    CloseTo μ ν ε ↔ etvDist μ.toMeasure ν.toMeasure ≤ 2 * ε := by
  rw [closeTo_iff_tsum_tsub_le, PMF.etvDist_toMeasure,
    ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top]

/-- Real-valued form of `closeTo_iff_etvDist_le`. -/
theorem closeTo_ofReal_iff_tvDist_le {ε : ℝ} (hε : 0 ≤ ε) :
    CloseTo μ ν (ENNReal.ofReal ε) ↔ tvDist μ.toMeasure ν.toMeasure ≤ 2 * ε := by
  rw [closeTo_iff_etvDist_le, ← ofReal_tvDist, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_le_ofReal_iff (by positivity)]

end TotalVariation

end Cslib.Probability
