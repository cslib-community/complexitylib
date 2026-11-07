/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.RoutedBinPreparation

/-! Checked preparation for an actual bounded routed top bin, including its light side. -/

open Cslib Matrix Matrix.FourthRootHierarchyParams

public section
noncomputable section

private def switch : ℝ → ℝ := polynomialSwitch4 (1 / 2) 1

private theorem switch_zero (v : ℝ) (hv : v ≤ 1 / 2) : switch v = 0 :=
  polynomialSwitch4_of_le (by norm_num) hv

private theorem numerator_one :
    boundedRoutedBinCutoff switch (fun _ => 1) 1 0 (fun _ => 1) 1 = 1 := by
  have h : switch 1 = 1 := polynomialSwitch4_of_ge (by norm_num) le_rfl
  norm_num [boundedRoutedBinCutoff, routedBinCutoff, binWeight, h]

example : boundedRoutedBinCutoff switch (fun _ => 1) 1 0 (fun _ => 1) 0 = 0 :=
  boundedRoutedBinCutoff_eq_zero (by norm_num) switch_zero
    (fun _ => by norm_num) (fun _ _ _ => le_rfl) (by norm_num) 0 (fun _ => 1)

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    polynomialPrepCutoff4 HP.θ 0 = 0 :=
  (routedBin_prep_laws HP).2.1 0 (div_nonneg HP.θ_pos.le (by norm_num))

/-- A nonzero genuine top bin lies on the selected preparation plateau. -/
theorem routedBinPreparation_plateau (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    polynomialPrepCutoff4 HP.θ 1 = 1 := by
  apply routedBin_prep_eq_one HP (χ := switch) (b := fun _ => 1)
    (cap := 1) (d := 1) (by norm_num) switch_zero
    (fun _ => by norm_num) (fun _ _ _ => le_rfl) 0 (fun _ => 1)
  rw [numerator_one]
  norm_num

-- Constant-one preparation fails the light-input contract used by the accuracy proof.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ¬ ∀ v : ℝ, v ≤ HP.θ / 2 → (1 : ℝ) = 0 := by
  intro h
  exact one_ne_zero (h 0 (div_nonneg HP.θ_pos.le (by norm_num)))
