/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/Deriv.lean`)

public import Complexity.Init
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# First-order conditions for convex functions on normed spaces

A convex function lies above its tangent hyperplanes: if `f` is convex on `K`, differentiable at
`x ∈ K` with derivative `f'`, and `y ∈ K`, then `f x + f' (y - x) ≤ f y`. In a Hilbert space with
gradient `g` this reads `f x + ⟪g, y - x⟫ ≤ f y`, so the gradient is a subgradient relative to
`K`. For `m`-strongly convex functions the bound improves by `m / 2 * ‖y - x‖ ^ 2`. Mathlib proves
the one-dimensional statements (`ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` and its relatives);
here they are lifted along the segment `s ↦ x + s • (y - x)`.

These are the forms of convexity and strong convexity assumed by online convex optimization
([Hazan2022] §2.1).

## Main results

* `ConvexOn.add_le_of_hasFDerivAt`: the tangent-hyperplane inequality on a real normed space.
* `ConvexOn.add_inner_le_of_hasGradientAt`: the gradient form in a Hilbert space.
* `StrongConvexOn.add_inner_add_le_of_hasGradientAt`: the strongly convex gradient form
  `f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y`.

## References

* [Hazan2022]
-/

public section

open Set
open scoped RealInnerProductSpace

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set F} {f : F → ℝ}

/-- A convex function lies above its tangent hyperplane at any point of differentiability:
`f x + f' (y - x) ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_le_of_hasFDerivAt (hf : ConvexOn ℝ K f) {x y : F} {f' : F →L[ℝ] ℝ}
    (hx : x ∈ K) (hy : y ∈ K) (hd : HasFDerivAt f f' x) :
    f x + f' (y - x) ≤ f y := by
  set φ : ℝ → F := fun s => x + s • (y - x) with hφ
  have hφK : ∀ s ∈ Icc (0 : ℝ) 1, φ s ∈ K := fun s hs => by
    have := hf.1 hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring : 1 - s + s = 1)
    convert this using 1
    simp only [hφ]
    module
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ φ) := by
    refine ⟨convex_Icc 0 1, fun a ha b hb p q hp hq hpq => ?_⟩
    have hφab : φ (p • a + q • b) = p • φ a + q • φ b := by
      obtain rfl : q = 1 - p := by linarith
      simp only [hφ]
      module
    simp only [Function.comp_apply]
    rw [hφab]
    exact hf.2 (hφK a ha) (hφK b hb) hp hq hpq
  have hderφ : HasDerivAt φ (y - x) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
    simpa only [one_smul, hφ, id] using this
  have hfd : HasFDerivAt f f' (φ 0) := by
    simpa only [hφ, zero_smul, add_zero] using hd
  have hder : HasDerivAt (f ∘ φ) (f' (y - x)) 0 := hfd.comp_hasDerivAt (0 : ℝ) hderφ
  have h := hconv.le_slope_of_hasDerivWithinAt_Ioi (by simp) (by simp) zero_lt_one
    hder.hasDerivWithinAt
  simp only [slope_def_field, Function.comp_apply, hφ, zero_smul, add_zero, one_smul,
    add_sub_cancel, sub_zero, div_one] at h
  linarith

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {K : Set E} {f : E → ℝ}

/-- The gradient of a convex function is a subgradient relative to its domain:
`f x + ⟪g, y - x⟫ ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_inner_le_of_hasGradientAt (hf : ConvexOn ℝ K f) {x y g : E} (hx : x ∈ K)
    (hy : y ∈ K) (hg : HasGradientAt f g x) :
    f x + ⟪g, y - x⟫ ≤ f y := by
  simpa only [InnerProductSpace.toDual_apply_apply] using
    hf.add_le_of_hasFDerivAt hx hy hg.hasFDerivAt

/-- The first-order bound for an `m`-strongly convex function:
`f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for `x y ∈ K`. -/
theorem StrongConvexOn.add_inner_add_le_of_hasGradientAt {m : ℝ} (hf : StrongConvexOn K m f)
    {x y g : E} (hx : x ∈ K) (hy : y ∈ K) (hg : HasGradientAt f g x) :
    f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hd := hg.hasFDerivAt.sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (m / 2))
  have h := (strongConvexOn_iff_convex.mp hf).add_le_of_hasFDerivAt hx hy hd
  simp only [sub_apply, smul_apply, InnerProductSpace.toDual_apply_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h ⊢
  rw [real_inner_comm x y]
  linarith

end InnerProduct
