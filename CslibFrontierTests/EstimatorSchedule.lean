/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import CslibFrontier.Computability.LogSpaceDerandomization.EstimatorSchedule
import Mathlib.Tactic.NormNum

/-!
# Regression examples for the slack schedule

The same nonconstant endpoint sample is tested on a full slice, a singleton slice and an
empty source slice. Other examples cover signed scale offsets, cutoff equality, zero budget,
a zero last child budget and a nonzero budget-zero sample that must not be dropped.
-/

namespace ComplexityTests.EstimatorSchedule

open Cslib Cslib.LogSpaceEstimation Finset
open scoped BigOperators

example : scaleCutoff 2 3 = 8 ∧ scaleCutoff 2 (-3) = 8 := by decide

example : lastBudget 20 4 2 1 = 16 ∧ lastBudget 20 8 2 1 = 12 := by decide

example : lastBudget 8 1 2 (-3) = 0 ∧ lastBudget 0 1 2 0 = 0 := by decide

example : slackGroup 20 4 2 1 = Ico 12 16 := by decide

-- An included layer at a negative scale has both child budgets strictly below its parent.
example {m : ℕ} (hm : m ∈ range (lastBudget 20 4 2 (-1))) : m + 1 < 20 ∧ m < 20 := by
  have hlast := lastBudget_lt (M := 20) (d := 4) (c := 2) (h := -1) (by decide) (by decide)
  have hmem := mem_range.mp hm
  omega

-- A nonzero budget-zero value remains as a boundary term.
example : (∑ m ∈ range (lastBudget 20 4 2 1),
    (((m + 1 : ℕ) : ℝ) ^ 2 + 7 - ((m : ℝ) ^ 2 + 7))) = 256 := by
  rw [sum_lastBudget_differences (fun m => (m : ℝ) ^ 2 + 7)]
  norm_num [lastBudget, scaleCutoff]

private abbrev source (_ : Bool) (x : Bool) : Prop := x = false
private abbrev endpoint (σ y : Bool) : Prop := y = false ∨ σ = true

private def sample (m : ℕ) (σ : Bool) (_ : Bool) (y : Bool) : ℝ :=
  (m : ℝ) ^ 2 + (if σ then (m : ℝ) else 0) * (if y then 2 else 1)

-- On the singleton slice, the nonconstant sample takes its true branch.
example : (∑ m ∈ range (lastBudget 20 4 2 1), rowSliceMean source endpoint
    (fun σ x y => sample (m + 1) σ x y - sample m σ x y) false true) = 288 := by
  rw [sum_rowSliceMean_differences]
  norm_num [rowSliceMean, sample, source, endpoint, lastBudget, scaleCutoff,
    expect_eq_sum_div_card, Finset.filter_insert, Finset.filter_empty, Finset.filter_singleton]

-- On the full slice the same sample is averaged, giving a different answer.
example : (∑ m ∈ range (lastBudget 20 4 2 1), rowSliceMean source endpoint
    (fun σ x y => sample (m + 1) σ x y - sample m σ x y) false false) = 264 := by
  rw [sum_rowSliceMean_differences]
  norm_num [rowSliceMean, sample, source, endpoint, lastBudget, scaleCutoff,
    expect_eq_sum_div_card, Finset.filter_insert, Finset.filter_empty, Finset.filter_singleton]

-- A wholly empty source slice stays zero, with the same schedule and sample.
example : (∑ m ∈ range (lastBudget 20 4 2 1), rowSliceMean source endpoint
    (fun σ x y => sample (m + 1) σ x y - sample m σ x y) true false) = 0 := by
  rw [sum_rowSliceMean_differences]
  norm_num [rowSliceMean, source]

-- Cutoff equality leaves an empty prefix, even though later sample values are nonzero.
example : (∑ m ∈ range (lastBudget 8 1 2 (-3)), rowSliceMean source endpoint
    (fun σ x y => sample (m + 1) σ x y - sample m σ x y) false false) = 0 := by
  norm_num [lastBudget, scaleCutoff]

-- An active coarse-scale task has a nonempty full (slack-one) schedule.
example : scaleCutoff 2 2 < 200 := by
  apply coarse_scale_available (A := 1) (a := (2 : ℝ) ^ (-4 : ℝ))
    (a' := (2 : ℝ) ^ (-2 : ℝ)) (u := (2 : ℝ) ^ (-2 : ℝ)) 200 2 1 2
      (by decide) (by norm_num) (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  · rw [precision_dyadic_rates]
    norm_num

-- A finite set containing coarse, zero-offset and fine scales uses one convergent majorant.
example : ∑ h ∈ ({-4, 0, 3} : Finset ℤ), scaleMajorant h ≤ ∑' h, scaleMajorant h :=
  summable_scaleMajorant.sum_le_tsum _ (fun h _ => scaleMajorant_nonneg h)

-- A scheduled coarse child loses ten budget units and one dependency rank.
example : binNormCost 4 4 * (2 : ℝ) ^ (-(79 / 16 : ℝ)) ≤
    (2 : ℝ) ^ (-(49 / 16 : ℝ)) * scaleMajorant 4 := by
  have h := scheduled_child_cost_le (A := 1) (a := (2 : ℝ) ^ (-4 : ℝ))
    (a' := 1) (u := 1) (u' := 1) (by norm_num) 200 4 2 2 1 (by decide) 4
    (by decide) (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by
      rw [one_div, Real.logb_inv,
        Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num)]
      norm_num)
  simp only [precision, Real.logb_one,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h
  norm_num [lastBudget, scaleCutoff] at h
  exact h

-- The mirrored fine child has lower precision and smaller scale cost, with the same bound.
example : binNormCost 4 (-4) * (2 : ℝ) ^ (-(15 / 16 : ℝ)) ≤
    (2 : ℝ) ^ (-(49 / 16 : ℝ)) * scaleMajorant (-4) := by
  have h := scheduled_child_cost_le (A := 1) (a := (2 : ℝ) ^ (-4 : ℝ))
    (a' := (2 : ℝ) ^ (-8 : ℝ)) (u := 1) (u' := 1) (by norm_num)
    200 4 2 2 1 (by decide) (-4) (by decide)
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by
      rw [Real.logb_div (by positivity) (by positivity),
        Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num),
        Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num)]
      norm_num)
  simp only [precision, Real.logb_one,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h
  norm_num [lastBudget, scaleCutoff] at h
  exact h

end ComplexityTests.EstimatorSchedule
