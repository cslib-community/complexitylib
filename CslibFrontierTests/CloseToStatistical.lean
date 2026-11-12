/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.StatisticalDistance.TotalVariation

/-!
# `CloseTo`, finite statistical distance and total variation

The shared distance bridge suffices to bound every event after an arbitrary kernel into `ℕ`.
No lattice protocol, native sampler or finite output-type instance is needed. The finite
characterization is exact, and the total-variation one applies on infinite types.
-/

open Cslib.Probability
open scoped ENNReal NNReal Cslib.Probability.PMF

example (next : Bool → PMF ℕ) :
    CloseTo ((PMF.pure true).bind next) ((PMF.uniformOfFintype Bool).bind next) (1 / 2) := by
  have h : dist (PMF.pure true) (PMF.uniformOfFintype Bool) ≤ (1 / 2 : ℝ≥0) := by
    norm_num [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, PMF.pure_apply,
      PMF.uniformOfFintype_apply]
  simpa using (closeTo_of_dist_le h).bind_left next

/-- The finite characterization is exact: a point mass and a fair coin are `1 / 2`-close and no
closer. -/
example : CloseTo (PMF.pure true) (PMF.uniformOfFintype Bool) (1 / 2 : ℝ≥0) ∧
    ¬ CloseTo (PMF.pure true) (PMF.uniformOfFintype Bool) (1 / 4 : ℝ≥0) := by
  have h : dist (PMF.pure true) (PMF.uniformOfFintype Bool) = 1 / 2 := by
    norm_num [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, PMF.pure_apply,
      PMF.uniformOfFintype_apply]
  simp only [closeTo_coe_iff_dist_le, h]
  norm_num

/-- On the infinite type `ℕ`, `CloseTo` and Mathlib's total variation determine each other. -/
example (μ ν : PMF ℕ) (h : CloseTo μ ν (ENNReal.ofReal (1 / 8))) :
    MeasureTheory.tvDist μ.toMeasure ν.toMeasure ≤ 1 / 4 := by
  have := (closeTo_ofReal_iff_tvDist_le (by norm_num)).1 h
  linarith
