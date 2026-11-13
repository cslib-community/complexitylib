/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/Deriv.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# First-order conditions for convex functions on normed spaces

A convex function lies above its tangent hyperplanes: if `f` is convex on `K` and differentiable
within `K` at `x ∈ K` with derivative `f'`, then `f x + f' (y - x) ≤ f y` for `y ∈ K`. In a
Hilbert space with gradient `g` this reads `f x + ⟪g, y - x⟫ ≤ f y`, so the gradient is a
subgradient relative to `K`. For `m`-strongly convex functions the bound improves by
`m / 2 * ‖y - x‖ ^ 2`. Mathlib proves
the one-dimensional statements (`ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` and its relatives);
here they are lifted along the segment `s ↦ x + s • (y - x)`.

These are the forms of convexity and strong convexity assumed by online convex optimization
([Hazan2022] §2.1).

## Main results

* `ConvexOn.add_le_of_hasFDerivWithinAt`: the tangent-hyperplane inequality on a real normed
  space, for a derivative within `K` (so boundary points of `K` are allowed);
  `ConvexOn.add_le_of_hasFDerivAt` is the special case of a full derivative.
* `ConvexOn.add_inner_le_of_hasGradientWithinAt`, `ConvexOn.add_inner_le_of_hasGradientAt`: the
  gradient form in a Hilbert space.
* `StrongConvexOn.add_inner_add_le_of_hasGradientWithinAt`,
  `StrongConvexOn.add_inner_add_le_of_hasGradientAt`: the strongly convex gradient form
  `f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y`.
* `convexOn_of_forall_add_le`, `convexOn_of_forall_add_inner_le`: conversely, a function with a
  subgradient relative to `K` at every point of `K` is convex on `K`.
* `abs_sub_le_of_forall_add_inner_le`: subgradients of norm at most `ρ` make the function
  `ρ`-Lipschitz on `K`.

## References

* [Hazan2022]
-/

public section

open Set
open scoped RealInnerProductSpace

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set F} {f : F → ℝ}

/-- A convex function lies above its tangent hyperplane at any point where it is differentiable
within its domain: `f x + f' (y - x) ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_le_of_hasFDerivWithinAt (hf : ConvexOn ℝ K f) {x y : F} {f' : F →L[ℝ] ℝ}
    (hx : x ∈ K) (hy : y ∈ K) (hd : HasFDerivWithinAt f f' K x) :
    f x + f' (y - x) ≤ f y := by
  set φ : ℝ → F := fun s => x + s • (y - x) with hφ
  have hφK : MapsTo φ (Icc 0 1) K := fun s hs => by
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
    exact hf.2 (hφK ha) (hφK hb) hp hq hpq
  have hderφ : HasDerivAt φ (y - x) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
    simpa only [one_smul, hφ, id] using this
  have hfd : HasFDerivWithinAt f f' K (φ 0) := by
    simpa only [hφ, zero_smul, add_zero] using hd
  have hder : HasDerivWithinAt (f ∘ φ) (f' (y - x)) (Icc 0 1) 0 :=
    hfd.comp_hasDerivWithinAt (0 : ℝ) hderφ.hasDerivWithinAt hφK
  have h := hconv.le_slope_of_hasDerivWithinAt_Ioi (by simp) (by simp) zero_lt_one
    (hder.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT zero_lt_one))
  simp only [slope_def_field, Function.comp_apply, hφ, zero_smul, add_zero, one_smul,
    add_sub_cancel, sub_zero, div_one] at h
  linarith

/-- A convex function lies above its tangent hyperplane at any point of differentiability:
`f x + f' (y - x) ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_le_of_hasFDerivAt (hf : ConvexOn ℝ K f) {x y : F} {f' : F →L[ℝ] ℝ}
    (hx : x ∈ K) (hy : y ∈ K) (hd : HasFDerivAt f f' x) :
    f x + f' (y - x) ≤ f y :=
  hf.add_le_of_hasFDerivWithinAt hx hy hd.hasFDerivWithinAt

/-- Conversely, a function with a subgradient relative to `K` at every point of a convex set `K`
is convex on `K`: if `f x + g x (y - x) ≤ f y` for all `x y ∈ K`, then `f` is convex on `K`. -/
theorem convexOn_of_forall_add_le (hK : Convex ℝ K) {g : F → F →L[ℝ] ℝ}
    (hsub : ∀ x ∈ K, ∀ y ∈ K, f x + g x (y - x) ≤ f y) : ConvexOn ℝ K f := by
  refine ⟨hK, fun x hx y hy a b ha hb hab => ?_⟩
  set p := a • x + b • y
  have hp : p ∈ K := hK hx hy ha hb hab
  have hlin : a * g p (x - p) + b * g p (y - p) = 0 := by
    have h : a • (x - p) + b • (y - p) = 0 := by
      simp only [smul_sub, p]
      rw [show b = 1 - a by linarith]
      module
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add, h, map_zero]
  have e1 := mul_le_mul_of_nonneg_left (hsub p hp x hx) ha
  have e2 := mul_le_mul_of_nonneg_left (hsub p hp y hy) hb
  rw [mul_add] at e1 e2
  have hfp : f p = a * f p + b * f p := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  linarith

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {K : Set E} {f : E → ℝ}

/-- The gradient of a convex function within its domain is a subgradient relative to the domain:
`f x + ⟪g, y - x⟫ ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_inner_le_of_hasGradientWithinAt (hf : ConvexOn ℝ K f) {x y g : E}
    (hx : x ∈ K) (hy : y ∈ K) (hg : HasGradientWithinAt f g K x) :
    f x + ⟪g, y - x⟫ ≤ f y := by
  simpa only [InnerProductSpace.toDual_apply_apply] using
    hf.add_le_of_hasFDerivWithinAt hx hy hg.hasFDerivWithinAt

/-- The gradient of a convex function is a subgradient relative to its domain:
`f x + ⟪g, y - x⟫ ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_inner_le_of_hasGradientAt (hf : ConvexOn ℝ K f) {x y g : E} (hx : x ∈ K)
    (hy : y ∈ K) (hg : HasGradientAt f g x) :
    f x + ⟪g, y - x⟫ ≤ f y :=
  hf.add_inner_le_of_hasGradientWithinAt hx hy
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mpr hg.hasFDerivAt.hasFDerivWithinAt)

omit [CompleteSpace E] in
/-- Conversely, a function with a subgradient relative to `K` at every point of a convex set `K`
is convex on `K`: if `f x + ⟪g x, y - x⟫ ≤ f y` for all `x y ∈ K`, then `f` is convex on `K`. -/
theorem convexOn_of_forall_add_inner_le (hK : Convex ℝ K) {g : E → E}
    (hsub : ∀ x ∈ K, ∀ y ∈ K, f x + ⟪g x, y - x⟫ ≤ f y) : ConvexOn ℝ K f :=
  convexOn_of_forall_add_le (g := fun x => innerSL ℝ (g x)) hK fun x hx y hy => by
    simpa only [innerSL_apply_apply] using hsub x hx y hy

omit [CompleteSpace E] in
/-- Bounded subgradients make a function Lipschitz: if `f x + ⟪g x, y - x⟫ ≤ f y` for `x y ∈ K`
and `‖g x‖ ≤ ρ` on `K`, then `|f x - f y| ≤ ρ * ‖x - y‖` for `x y ∈ K`. -/
theorem abs_sub_le_of_forall_add_inner_le {g : E → E} {ρ : ℝ}
    (hsub : ∀ x ∈ K, ∀ y ∈ K, f x + ⟪g x, y - x⟫ ≤ f y) (hg : ∀ x ∈ K, ‖g x‖ ≤ ρ) {x y : E}
    (hx : x ∈ K) (hy : y ∈ K) : |f x - f y| ≤ ρ * ‖x - y‖ := by
  have h1 := hsub x hx y hy
  have h2 := hsub y hy x hx
  have b1 : |⟪g x, y - x⟫| ≤ ρ * ‖x - y‖ := by
    rw [norm_sub_rev]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hg x hx) (norm_nonneg _))
  have b2 : |⟪g y, x - y⟫| ≤ ρ * ‖x - y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg y hy) (norm_nonneg _))
  rw [abs_le] at b1 b2 ⊢
  constructor <;> linarith

/-- The first-order bound for an `m`-strongly convex function with a gradient within its domain:
`f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for `x y ∈ K`. -/
theorem StrongConvexOn.add_inner_add_le_of_hasGradientWithinAt {m : ℝ}
    (hf : StrongConvexOn K m f) {x y g : E} (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientWithinAt f g K x) :
    f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hd := hg.hasFDerivWithinAt.sub
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.hasFDerivWithinAt.const_mul (m / 2))
  have h := (strongConvexOn_iff_convex.mp hf).add_le_of_hasFDerivWithinAt hx hy hd
  simp only [sub_apply, smul_apply, InnerProductSpace.toDual_apply_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h ⊢
  rw [real_inner_comm x y]
  linarith

/-- The first-order bound for an `m`-strongly convex function:
`f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for `x y ∈ K`. -/
theorem StrongConvexOn.add_inner_add_le_of_hasGradientAt {m : ℝ} (hf : StrongConvexOn K m f)
    {x y g : E} (hx : x ∈ K) (hy : y ∈ K) (hg : HasGradientAt f g x) :
    f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y :=
  hf.add_inner_add_le_of_hasGradientWithinAt hx hy
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mpr hg.hasFDerivAt.hasFDerivWithinAt)

end InnerProduct
