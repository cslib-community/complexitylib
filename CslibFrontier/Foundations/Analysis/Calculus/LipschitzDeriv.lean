/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Calculus/MeanValue.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Functions with a Lipschitz derivative

A differentiable function `f : E → ℝ` whose derivative is `β`-Lipschitz (a *`β`-smooth* function
[ShalevShwartzBenDavid2014, Definition 12.8]) lies below its first-order approximation plus
`β/2 ‖y - x‖²`, and when it is nonnegative its derivative is bounded by its value.

## Main results

* `image_le_of_lipschitzWith_hasFDerivAt`: the quadratic upper bound
  `f y ≤ f x + f' x (y - x) + β/2 ‖y - x‖²` [ShalevShwartzBenDavid2014, (12.5)].
* `norm_sq_le_of_lipschitzWith_hasFDerivAt`: *self-boundedness*: if moreover `f ≥ 0`, then
  `‖f' x‖² ≤ 2β f x` [ShalevShwartzBenDavid2014, (12.6)].

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 12.1.3
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The quadratic upper bound for a Lipschitz derivative** [ShalevShwartzBenDavid2014, (12.5)]:
if `f` has derivative `f' x` at every `x` and `f'` is `β`-Lipschitz, then
`f y ≤ f x + f' x (y - x) + β/2 ‖y - x‖²`. -/
theorem image_le_of_lipschitzWith_hasFDerivAt {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {β : NNReal}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hlip : LipschitzWith β f') (x y : E) :
    f y ≤ f x + f' x (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
  set h := y - x
  -- Along the segment, `φ t = f (x + t h) - t f' x h` grows at most like `β t² ‖h‖² / 2`.
  set φ : ℝ → ℝ := fun t => f (x + t • h) - t * f' x h with hφ_def
  set φ' : ℝ → ℝ := fun t => f' (x + t • h) h - f' x h with hφ'_def
  have hφ : ∀ t, HasDerivAt φ (φ' t) t := fun t => by
    have hline : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    exact ((hf (x + t • h)).comp_hasDerivAt t hline).sub (hasDerivAt_mul_const (f' x h))
  set B : ℝ → ℝ := fun t => f x + β / 2 * ‖h‖ ^ 2 * t ^ 2 with hB_def
  have hB : ∀ t, HasDerivAt B (β * ‖h‖ ^ 2 * t) t := fun t => by
    have := ((hasDerivAt_pow 2 t).const_mul ((β : ℝ) / 2 * ‖h‖ ^ 2)).const_add (f x)
    convert this using 1
    norm_num
    ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, φ' t ≤ β * ‖h‖ ^ 2 * t := fun t ht => by
    have hdist : ‖f' (x + t • h) - f' x‖ ≤ β * (t * ‖h‖) := by
      have := hlip.dist_le_mul (x + t • h) x
      rwa [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
        at this
    calc φ' t = (f' (x + t • h) - f' x) h := by simp [φ']
      _ ≤ ‖(f' (x + t • h) - f' x) h‖ := Real.le_norm_self _
      _ ≤ ‖f' (x + t • h) - f' x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ β * (t * ‖h‖) * ‖h‖ := by gcongr
      _ = β * ‖h‖ ^ 2 * t := by ring
  have key := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hφ t).continuousAt.continuousWithinAt)
    (fun t _ => (hφ t).hasDerivWithinAt) (by simp [φ, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hbound (right_mem_Icc.2 zero_le_one)
  simp only [φ, B, one_smul, one_mul, one_pow, mul_one] at key
  have hy : x + h = y := add_sub_cancel x y
  rw [hy] at key
  linarith

/-- **Self-boundedness** [ShalevShwartzBenDavid2014, (12.6)]: if `f ≥ 0` has derivative `f' x` at
every `x` and `f'` is `β`-Lipschitz, then `‖f' x‖² ≤ 2β f x`. -/
theorem norm_sq_le_of_lipschitzWith_hasFDerivAt {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {β : NNReal}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hlip : LipschitzWith β f') (hf0 : ∀ x, 0 ≤ f x)
    (x : E) : ‖f' x‖ ^ 2 ≤ 2 * β * f x := by
  have hfx := hf0 x
  -- In each direction `h`, `0 ≤ f (x + s h) ≤ f x + s f' x h + β/2 s² ‖h‖²` for every `s`, so the
  -- discriminant `(f' x h)² - 2β ‖h‖² f x` of this quadratic in `s` is nonpositive.
  have hdir : ∀ h, |f' x h| ≤ √(2 * β * f x) * ‖h‖ := fun h => by
    have hq : ∀ s : ℝ, 0 ≤ (β / 2 * ‖h‖ ^ 2) * (s * s) + f' x h * s + f x := fun s => by
      have := image_le_of_lipschitzWith_hasFDerivAt hf hlip x (x + s • h)
      rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs] at this
      have := hf0 (x + s • h)
      nlinarith
    have hd := discrim_le_zero hq
    rw [discrim] at hd
    rw [← Real.sqrt_sq (norm_nonneg h), ← Real.sqrt_mul (by positivity), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hop : ‖f' x‖ ≤ √(2 * β * f x) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun h => by
      rw [Real.norm_eq_abs]
      exact hdir h
  calc ‖f' x‖ ^ 2 ≤ √(2 * β * f x) ^ 2 := by gcongr
    _ = 2 * β * f x := Real.sq_sqrt (by positivity)
