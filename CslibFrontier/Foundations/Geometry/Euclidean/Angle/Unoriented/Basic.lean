/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos

/-!
# Unoriented angles between unit vectors and vectors of equal norm

For unit vectors `x` and `y`, `InnerProductGeometry.angle x y = Real.arccos ⟪x, y⟫`
(`InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one`). More generally, for vectors `u` and
`v` of equal norm whose sum is nonzero, the half-angle formula expresses `angle u v` as
`2 * Real.arctan (‖v - u‖ / ‖u + v‖)` (`InnerProductGeometry.angle_eq_two_mul_arctan`).

## Main results

* `InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one`: the angle between unit vectors is
  `arccos` of their inner product.
* `InnerProductGeometry.angle_eq_two_mul_arctan`: the half-angle formula for vectors of equal norm.
-/

public section

open Real
open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The angle between unit vectors is the `arccos` of their inner product. -/
theorem angle_eq_arccos_inner_of_norm_eq_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y = arccos ⟪x, y⟫ := by
  simp [angle, hx, hy]

/-- **The half-angle formula.** Two vectors of equal norm whose sum is nonzero make the angle
`2 arctan (‖v - u‖ / ‖u + v‖)`. -/
theorem angle_eq_two_mul_arctan {u v : V} (huv : ‖u‖ = ‖v‖) (hne : u + v ≠ 0) :
    angle u v = 2 * arctan (‖v - u‖ / ‖u + v‖) := by
  have hr : 0 < ‖u‖ := by
    refine norm_pos_iff.2 fun hu => hne ?_
    rw [hu, norm_zero, eq_comm, norm_eq_zero] at huv
    rw [hu, huv, add_zero]
  set c := ⟪u, v⟫ / (‖u‖ * ‖u‖) with hc
  have hinner : ⟪u, v⟫ = c * ‖u‖ ^ 2 := by
    rw [hc, sq, div_mul_cancel₀ _ (by positivity)]
  have hsub : ‖v - u‖ = √(2 * ‖u‖ ^ 2) * √(1 - c) := by
    rw [← sqrt_mul (by positivity), ← sqrt_sq (norm_nonneg (v - u)), norm_sub_sq_real,
      real_inner_comm, hinner, ← huv]
    ring_nf
  have hadd : ‖u + v‖ = √(2 * ‖u‖ ^ 2) * √(1 + c) := by
    rw [← sqrt_mul (by positivity), ← sqrt_sq (norm_nonneg (u + v)), norm_add_sq_real, hinner,
      ← huv]
    ring_nf
  have hc1 : -1 < c := by
    have h : 0 < ‖u + v‖ := norm_pos_iff.2 hne
    rw [hadd] at h
    have := (mul_pos_iff_of_pos_left (sqrt_pos.2 (by positivity))).1 h
    linarith [sqrt_pos.1 this]
  rw [hsub, hadd, mul_div_mul_left _ _ (sqrt_pos.2 (by positivity)).ne',
    ← arccos_eq_two_mul_arctan hc1, angle, ← huv]

end InnerProductGeometry
