/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Normed/Module/FiniteDimension.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compactness and extrema on unit-vector assignments

In a finite-dimensional real normed space `F`, the set of unit-vector assignments
`{v : W → F | ∀ i, ‖v i‖ = 1}` is compact (`NormedSpace.isCompact_unitSphereFun`), so when `F` is
nontrivial every continuous real-valued function on unit-vector assignments attains its maximum
(`NormedSpace.exists_isMaxOn_unitSphereFun`).

## Main results

* `NormedSpace.isCompact_unitSphereFun`: compactness of `{v : W → F | ∀ i, ‖v i‖ = 1}`.
* `NormedSpace.exists_isMaxOn_unitSphereFun`: existence of a maximizer for any continuous
  `f : (W → F) → ℝ` on unit-vector assignments.
-/

public section

namespace NormedSpace

/-- In a finite-dimensional real normed space, the set of unit-vector assignments `W → F` is
compact. -/
theorem isCompact_unitSphereFun (W F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    IsCompact {v' : W → F | ∀ i, ‖v' i‖ = 1} := by
  have := isCompact_univ_pi fun _ : W => isCompact_sphere (0 : F) 1
  simpa only [Set.pi, Set.mem_univ, Metric.mem_sphere, dist_zero_right, true_imp_iff] using this

/-- Every continuous real-valued function on unit-vector assignments `W → F` in a nontrivial
finite-dimensional real normed space attains its maximum. -/
theorem exists_isMaxOn_unitSphereFun {W F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] {f : (W → F) → ℝ} (hf : Continuous f) :
    ∃ v : W → F, (∀ i, ‖v i‖ = 1) ∧ IsMaxOn f {v' | ∀ i, ‖v' i‖ = 1} v := by
  obtain ⟨u, hu⟩ := (sphere_nonempty_rclike ℝ (E := F) zero_le_one).some
  rw [mem_sphere_zero_iff_norm] at hu
  exact (isCompact_unitSphereFun W F).exists_isMaxOn ⟨fun _ => u, fun _ => hu⟩ hf.continuousOn

end NormedSpace
