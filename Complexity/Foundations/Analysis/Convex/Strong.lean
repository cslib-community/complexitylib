/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/Strong.lean`)

public import Complexity.Init
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Order.Filter.Extr
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Strongly convex functions: scaling, quadratic growth and stability

Mathlib defines `m`-strong convexity on a real normed space (`StrongConvexOn`) through the
inequality `f (a • x + b • y) ≤ a • f x + b • f y - a * b * (m / 2 * ‖x - y‖ ^ 2)`. This file adds
the facts used by follow-the-regularized-leader:

* closure under nonnegative scaling and under adding a convex function;
* *quadratic growth* at a minimizer: if `x` minimizes an `m`-strongly convex `f` on `s`, then
  `f x + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for `y ∈ s`;
* the *stability bound*: if moreover `ℓ x - ℓ y ≤ L * ‖x - y‖` and `m > 0`, then
  `f x + ℓ x - (f y + ℓ y) ≤ L ^ 2 / (2 * m)`;
* in a real inner product space, `m / 2 * ‖y - x₀‖ ^ 2` is `m`-strongly convex (the Euclidean
  regularizer).

The first three need neither differentiability nor an inner product. The norm is that of the
ambient space, so the same statements cover strong convexity with respect to `ℓ¹`, `ℓ²` or any
other norm. The stability bound is the inequality behind [Orabona2019, Lemma 7.8] (there obtained
from subgradients and the dual norm); here it follows from quadratic growth and the elementary
bound `L d - m / 2 d ² ≤ L ² / (2 m)`.

## Main results

* `StrongConvexOn.smul`, `StrongConvexOn.add_convexOn`: closure properties.
* `StrongConvexOn.add_le_of_isMinOn`: quadratic growth at a minimizer.
* `StrongConvexOn.sub_le_of_isMinOn`: the stability bound.
* `strongConvexOn_mul_norm_sub_sq`: strong convexity of the squared Euclidean distance.

## References

* [Orabona2019]
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f g : E → ℝ}
  {m : ℝ}

/-- Scaling an `m`-strongly convex function by `c ≥ 0` gives a `c * m`-strongly convex function. -/
theorem StrongConvexOn.smul {c : ℝ} (hc : 0 ≤ c) (hf : StrongConvexOn s m f) :
    StrongConvexOn s (c * m) fun x => c • f x := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
  simp only [smul_eq_mul] at h ⊢
  linarith

/-- Adding a convex function to an `m`-strongly convex function keeps it `m`-strongly convex. -/
theorem StrongConvexOn.add_convexOn (hf : StrongConvexOn s m f) (hg : ConvexOn ℝ s g) :
    StrongConvexOn s m (f + g) := by
  have h := UniformConvexOn.add hf hg.uniformConvexOn_zero
  simpa only [StrongConvexOn, add_zero] using h

/-- **Quadratic growth at a minimizer.** If `x` minimizes an `m`-strongly convex function `f` on
`s`, then `f x + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for every `y ∈ s`. -/
theorem StrongConvexOn.add_le_of_isMinOn (hf : StrongConvexOn s m f) {x : E} (hx : x ∈ s)
    (hmin : IsMinOn f s x) {y : E} (hy : y ∈ s) :
    f x + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  set c := m / 2 * ‖y - x‖ ^ 2 with hc
  set g := f y - f x with hg
  -- `f (a • y + (1 - a) • x) ≤ f x + a * g - a * (1 - a) * c`, and `f x` is the minimum, so
  -- `a * (1 - a) * c ≤ a * g` for every `a ∈ [0, 1]`.
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a * (1 - a) * c ≤ a * g := by
    intro a ha0 ha1
    have hconv := hf.2 hy hx ha0 (sub_nonneg.mpr ha1) (by ring)
    have hmem : a • y + (1 - a) • x ∈ s :=
      hf.1 hy hx ha0 (sub_nonneg.mpr ha1) (by ring)
    have hle : f x ≤ f (a • y + (1 - a) • x) := hmin hmem
    simp only [smul_eq_mul] at hconv
    rw [hc]
    nlinarith
  have hg0 : 0 ≤ g := by
    have : f x ≤ f y := hmin hy
    linarith
  by_contra hlt
  have hgc : g < c := by linarith [not_le.mp hlt]
  have hc0 : 0 < c := lt_of_le_of_lt hg0 hgc
  set a := (c - g) / (2 * c) with ha
  have ha0 : 0 < a := div_pos (by linarith) (by positivity)
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]
    linarith
  have h := key a ha0.le ha1
  have h' : (1 - a) * c ≤ g := le_of_mul_le_mul_left (by linarith) ha0
  have h1a : (1 - a) * c = (c + g) / 2 := by
    rw [ha]
    field_simp
    ring
  linarith

/-- **Stability of a strongly convex minimizer under a perturbation.** If `x` minimizes an
`m`-strongly convex function `f` on `s` with `m > 0`, and the perturbation `ℓ` satisfies the
one-sided Lipschitz bound `ℓ x - ℓ y ≤ L * ‖x - y‖`, then
`f x + ℓ x - (f y + ℓ y) ≤ L ^ 2 / (2 * m)` (compare [Orabona2019, Lemma 7.8]). -/
theorem StrongConvexOn.sub_le_of_isMinOn (hf : StrongConvexOn s m f) (hm : 0 < m) {x : E}
    (hx : x ∈ s) (hmin : IsMinOn f s x) {y : E} (hy : y ∈ s) {ℓ : E → ℝ} {L : ℝ}
    (hℓ : ℓ x - ℓ y ≤ L * ‖x - y‖) :
    f x + ℓ x - (f y + ℓ y) ≤ L ^ 2 / (2 * m) := by
  have hq := hf.add_le_of_isMinOn hx hmin hy
  rw [norm_sub_rev] at hq
  set d := ‖x - y‖
  have hsq : L * d - m / 2 * d ^ 2 ≤ L ^ 2 / (2 * m) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (m * d - L)]
  linarith

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {K : Set F}

/-- In a real inner product space the squared distance `m / 2 * ‖y - x₀‖ ^ 2` to a fixed point
is `m`-strongly convex on every convex set. -/
theorem strongConvexOn_mul_norm_sub_sq (hK : Convex ℝ K) (m : ℝ) (x₀ : F) :
    StrongConvexOn K m fun y => m / 2 * ‖y - x₀‖ ^ 2 := by
  rw [strongConvexOn_iff_convex]
  refine ⟨hK, fun x _ y _ a b _ _ hab => ?_⟩
  simp only [norm_sub_sq_real, smul_eq_mul, inner_add_left, real_inner_smul_left]
  linear_combination (-(m / 2 * ‖x₀‖ ^ 2)) * hab

end InnerProductSpace
