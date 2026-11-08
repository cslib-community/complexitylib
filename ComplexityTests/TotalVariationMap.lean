/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.MeasureTheory.Measure.TotalVariation.Map
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.MeasureTheory.Group.AddCircle

/-! Full-L1 units, strict coarsening, unequal masses, and actual reduction modulo one. -/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace ComplexityTests.TotalVariationMap

private theorem atoms_distance : tvDist (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ)) = 2 := by
  have h : Measure.dirac (0 : ℝ) ⟂ₘ Measure.dirac (1 : ℝ) :=
    ⟨{1}, measurableSet_singleton _, by simp, by simp⟩
  rw [tvDist_of_mutuallySingular h]
  norm_num

example : tvDist ((Measure.dirac (0 : ℝ)).map id) ((Measure.dirac (1 : ℝ)).map id) = 2 := by
  simpa using atoms_distance

/-- Deterministic coarsening can strictly reduce the full-L1 distance from two to zero. -/
example : tvDist ((Measure.dirac (0 : ℝ)).map (fun _ ↦ (0 : ℝ)))
      ((Measure.dirac (1 : ℝ)).map (fun _ ↦ (0 : ℝ))) = 0 ∧
    tvDist (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ)) = 2 := by
  constructor
  · simp
  · exact atoms_distance

example : tvDist ((Measure.dirac (0 : ℝ)).map (fun _ ↦ (0 : ℝ)))
    ((Measure.dirac (1 : ℝ)).map (fun _ ↦ (0 : ℝ))) ≤ 2 := by
  exact (tvDist_map_le (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ))
    (f := fun _ : ℝ ↦ (0 : ℝ)) measurable_const).trans_eq atoms_distance

/-- Unequal finite masses are allowed and keep the full mass discrepancy. -/
example : tvDist ((2 : ℝ≥0) • Measure.dirac (1 : ℝ)) 0 = 2 := by
  simp [tvDist_zero_right, Measure.real]

example : tvDist (((2 : ℝ≥0) • Measure.dirac (1 : ℝ)).map (fun x ↦ x + 4))
    ((0 : Measure ℝ).map (fun x ↦ x + 4)) ≤ 2 := by
  have h := tvDist_map_le ((2 : ℝ≥0) • Measure.dirac (1 : ℝ)) 0
    (show Measurable (fun x : ℝ ↦ x + 4) by fun_prop)
  simpa [tvDist_zero_right, Measure.real] using h

example : etvDist (((2 : ℝ≥0) • Measure.dirac (1 : ℝ)).map (fun x ↦ -x))
    ((0 : Measure ℝ).map (fun x ↦ -x)) ≤ 2 := by
  have h := etvDist_map_le ((2 : ℝ≥0) • Measure.dirac (1 : ℝ)) 0
    (show Measurable (fun x : ℝ ↦ -x) by fun_prop)
  simpa using h

/-- The canonical mod-one map is a genuine measurable postprocessing client. -/
example : tvDist ((Measure.dirac (0 : ℝ)).map (fun x : ℝ ↦ (x : UnitAddCircle)))
    ((Measure.dirac (1 : ℝ)).map (fun x : ℝ ↦ (x : UnitAddCircle))) ≤ 2 := by
  exact (tvDist_map_le (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ))
    (f := fun x : ℝ ↦ (x : UnitAddCircle)) (by fun_prop)).trans_eq atoms_distance

end ComplexityTests.TotalVariationMap
