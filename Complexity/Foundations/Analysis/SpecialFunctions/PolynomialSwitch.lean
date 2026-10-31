/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial switches with Lipschitz fourth roots

The fourth-moment workstream of complexitylib issue #1721 needs a monotone switch whose fourth
root and complementary fourth root are Lipschitz. The switch of [OpenAI2026LogSpace, Section 5.1]
is a rescaled normalized integral of `t^(s-1) (1-t)^(s-1)` on `[0,1]`.
For the fourth-moment route (`s = 4`), its polynomial
is `35 t^4 - 84 t^5 + 70 t^6 - 20 t^7`.

We give that polynomial as the equivalent factored expression
`t^4 * (1 + 4(1-t) + 10(1-t)^2 + 20(1-t)^3)` and clamp its input to `[0,1]`.
The polynomial, clamped transition and rescaled switch use only field arithmetic and min/max;
their definitions also specialize to computable functions on `ℚ`. The cast lemmas identify those
exact rational evaluations with the real functions used by the analysis. They assert no machine
resource bound or rational approximation to the fourth root.

The factor after `t^4` is at least one on `[0,1]`. Thus the fourth root is `t` times the fourth
root of a positive polynomial, which is continuously differentiable on that interval and hence
Lipschitz there. Composing with clamping gives a global Lipschitz bound. The complement follows
by reflection. These primitives do not yet provide the complete admissible hierarchy parameters,
their threshold ladder, or the regularity of the unbounded correction ramp.

## Main definitions

* `Cslib.transitionPolynomial4`: the polynomial whose value at zero and complement at one
  vanish to fourth order.
* `Cslib.polynomialTransition4`: its clamped transition from zero to one.
* `Cslib.polynomialSwitch4`: its rescaling to an arbitrary nondegenerate interval.

## Main results

* `Cslib.polynomialSwitch4_nonneg`, `Cslib.polynomialSwitch4_le_one`: range bounds.
* `Cslib.polynomialSwitch4_eq_zero_iff`, `Cslib.polynomialSwitch4_eq_one_iff`: exact endpoints.
* `Cslib.monotone_polynomialSwitch4`: monotonicity.
* `Cslib.exists_lipschitzWith_polynomialSwitch4_root`,
  `Cslib.exists_lipschitzWith_one_sub_polynomialSwitch4_root`: Lipschitz fourth roots.
* `Cslib.polynomialSwitch4_ratCast`: exact compatibility with rational evaluation.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 5.1 (23 September 2026, revision `7ef5c0cc`, not peer reviewed). The paper uses `s = 8`;
  this module gives the same normalized-integral construction for the project's `s = 4` route.
-/

public section

namespace Cslib

/-- The normalized integral polynomial for the fourth-moment switch, in a form displaying its
fourth-order zero and a positive remaining factor on `[0,1]`. -/
@[expose] def transitionPolynomial4 {R : Type*} [CommRing R] (t : R) : R :=
  t ^ 4 * (1 + 4 * (1 - t) + 10 * (1 - t) ^ 2 + 20 * (1 - t) ^ 3)

/-- The degree-seven transition polynomial, clamped to the unit interval. Its generic definition
can be evaluated exactly on rational inputs. -/
@[expose] def polynomialTransition4 {R : Type*} [CommRing R] [LinearOrder R] (t : R) : R :=
  transitionPolynomial4 (max 0 (min 1 t))

/-- Rescale the fourth-moment polynomial transition from `[0,1]` to `[α,β]`. The switch laws
assume `α < β`; the arithmetic expression itself is defined for all endpoints. -/
@[expose] def polynomialSwitch4 {R : Type*} [Field R] [LinearOrder R] (α β t : R) : R :=
  polynomialTransition4 ((t - α) / (β - α))

section Polynomial

variable {R : Type*} [CommRing R]

theorem transitionPolynomial4_expanded (t : R) :
    transitionPolynomial4 t = 35 * t ^ 4 - 84 * t ^ 5 + 70 * t ^ 6 - 20 * t ^ 7 := by
  unfold transitionPolynomial4
  ring

@[simp] theorem transitionPolynomial4_zero : transitionPolynomial4 (0 : R) = 0 := by
  simp [transitionPolynomial4]

@[simp] theorem transitionPolynomial4_one : transitionPolynomial4 (1 : R) = 1 := by
  simp [transitionPolynomial4]

/-- Reflection interchanges the transition polynomial and its complement. -/
theorem one_sub_transitionPolynomial4 (t : R) :
    1 - transitionPolynomial4 t = transitionPolynomial4 (1 - t) := by
  unfold transitionPolynomial4
  ring

end Polynomial

private theorem factor_pos {t : ℝ} (ht : t ≤ 1) :
    0 < 1 + 4 * (1 - t) + 10 * (1 - t) ^ 2 + 20 * (1 - t) ^ 3 := by
  have h : 0 ≤ 1 - t := sub_nonneg.mpr ht
  positivity

/-- The derivative identifies the normalization of the integral `t^3 (1-t)^3`. -/
theorem hasDerivAt_transitionPolynomial4 (t : ℝ) :
    HasDerivAt transitionPolynomial4 (140 * t ^ 3 * (1 - t) ^ 3) t := by
  convert (((hasDerivAt_pow 4 t).const_mul 35).sub
    ((hasDerivAt_pow 5 t).const_mul 84) |>.add ((hasDerivAt_pow 6 t).const_mul 70)).sub
      ((hasDerivAt_pow 7 t).const_mul 20) using 1
  · funext x
    exact transitionPolynomial4_expanded x
  · ring

theorem monotoneOn_transitionPolynomial4 :
    MonotoneOn (transitionPolynomial4 : ℝ → ℝ) (Set.Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (fun x _ => (hasDerivAt_transitionPolynomial4 x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_transitionPolynomial4 x).differentiableAt.differentiableWithinAt)
    fun x hx => ?_
  rw [(hasDerivAt_transitionPolynomial4 x).deriv]
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
  have h0 : 0 ≤ x := hx'.1
  have h1 : 0 ≤ 1 - x := sub_nonneg.mpr hx'.2
  positivity

private theorem clamp_mem (t : ℝ) : max 0 (min 1 t) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem polynomialTransition4_nonneg (t : ℝ) : 0 ≤ polynomialTransition4 t := by
  have h := monotoneOn_transitionPolynomial4 (Set.left_mem_Icc.mpr zero_le_one) (clamp_mem t)
    (clamp_mem t).1
  simpa only [polynomialTransition4, transitionPolynomial4_zero] using h

theorem polynomialTransition4_le_one (t : ℝ) : polynomialTransition4 t ≤ 1 := by
  have h := monotoneOn_transitionPolynomial4 (clamp_mem t) (Set.right_mem_Icc.mpr zero_le_one)
    (clamp_mem t).2
  simpa only [polynomialTransition4, transitionPolynomial4_one] using h

theorem polynomialTransition4_of_nonpos {t : ℝ} (ht : t ≤ 0) : polynomialTransition4 t = 0 := by
  rw [polynomialTransition4, min_eq_right (ht.trans zero_le_one), max_eq_left ht]
  exact transitionPolynomial4_zero

theorem polynomialTransition4_of_one_le {t : ℝ} (ht : 1 ≤ t) : polynomialTransition4 t = 1 := by
  rw [polynomialTransition4, min_eq_left ht, max_eq_right zero_le_one]
  exact transitionPolynomial4_one

theorem polynomialTransition4_of_mem {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    polynomialTransition4 t = transitionPolynomial4 t := by
  rw [polynomialTransition4, min_eq_right ht.2, max_eq_right ht.1]

theorem monotone_polynomialTransition4 : Monotone (polynomialTransition4 : ℝ → ℝ) :=
  fun x y hxy => monotoneOn_transitionPolynomial4 (clamp_mem x) (clamp_mem y)
    (max_le_max le_rfl (min_le_min le_rfl hxy))

/-- Reflection interchanges the clamped transition and its complement. -/
theorem one_sub_polynomialTransition4 (t : ℝ) :
    1 - polynomialTransition4 t = polynomialTransition4 (1 - t) := by
  by_cases ht0 : t ≤ 0
  · rw [polynomialTransition4_of_nonpos ht0,
      polynomialTransition4_of_one_le (by linarith : 1 ≤ 1 - t), sub_zero]
  by_cases ht1 : 1 ≤ t
  · rw [polynomialTransition4_of_one_le ht1,
      polynomialTransition4_of_nonpos (by linarith : 1 - t ≤ 0), sub_self]
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨(not_le.mp ht0).le, (not_le.mp ht1).le⟩
  have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [polynomialTransition4_of_mem ht, polynomialTransition4_of_mem ht',
    one_sub_transitionPolynomial4]

theorem polynomialTransition4_eq_zero_iff {t : ℝ} : polynomialTransition4 t = 0 ↔ t ≤ 0 := by
  refine ⟨fun h => ?_, polynomialTransition4_of_nonpos⟩
  by_contra ht
  have hp : 0 < max 0 (min 1 t) :=
    (lt_min zero_lt_one (lt_of_not_ge ht)).trans_le (le_max_right _ _)
  have hf := factor_pos (clamp_mem t).2
  have : 0 < polynomialTransition4 t := by
    unfold polynomialTransition4 transitionPolynomial4
    positivity
  exact this.ne' h

theorem polynomialTransition4_eq_one_iff {t : ℝ} : polynomialTransition4 t = 1 ↔ 1 ≤ t := by
  refine ⟨fun h => ?_, polynomialTransition4_of_one_le⟩
  have hz : polynomialTransition4 (1 - t) = 0 := by
    rw [← one_sub_polynomialTransition4, h, sub_self]
  have := polynomialTransition4_eq_zero_iff.mp hz
  linarith

/-! ## Fourth-root regularity -/

private theorem root_eq {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    transitionPolynomial4 t ^ (4⁻¹ : ℝ) =
      t * (1 + 4 * (1 - t) + 10 * (1 - t) ^ 2 + 20 * (1 - t) ^ 3) ^ (4⁻¹ : ℝ) := by
  rw [transitionPolynomial4, Real.mul_rpow (pow_nonneg ht.1 _) (factor_pos ht.2).le]
  congr 1
  convert Real.pow_rpow_inv_natCast ht.1 (by norm_num : (4 : ℕ) ≠ 0) using 1

/-- The fourth root is Lipschitz globally; the transition has fourth-order vanishing at zero. -/
theorem exists_lipschitzWith_polynomialTransition4_root :
    ∃ K, LipschitzWith K fun t : ℝ => polynomialTransition4 t ^ (4⁻¹ : ℝ) := by
  have hf : ContDiffOn ℝ 1 (fun t : ℝ =>
      t * (1 + 4 * (1 - t) + 10 * (1 - t) ^ 2 + 20 * (1 - t) ^ 3) ^ (4⁻¹ : ℝ))
        (Set.Icc 0 1) := by
    apply contDiffOn_id.mul
    apply ContDiffOn.rpow_const_of_ne (by fun_prop)
    exact fun t ht => (factor_pos ht.2).ne'
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hproj := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul x y
  have hb := hK.dist_le_mul _ (clamp_mem x) _ (clamp_mem y)
  rw [← root_eq (clamp_mem x), ← root_eq (clamp_mem y)] at hb
  refine hb.trans ?_
  simp only [Subtype.dist_eq, NNReal.coe_one, one_mul, Set.coe_projIcc] at hproj
  exact mul_le_mul_of_nonneg_left hproj K.2

/-- The fourth root of the complement is Lipschitz, by reflection at `1/2`. -/
theorem exists_lipschitzWith_one_sub_polynomialTransition4_root :
    ∃ K, LipschitzWith K fun t : ℝ => (1 - polynomialTransition4 t) ^ (4⁻¹ : ℝ) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_polynomialTransition4_root
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [one_sub_polynomialTransition4]
  simpa only [dist_sub_left] using hK.dist_le_mul (1 - x) (1 - y)

/-! ## Rescaling and exact rational values -/

variable {α β t : ℝ}

theorem polynomialSwitch4_nonneg (α β t : ℝ) : 0 ≤ polynomialSwitch4 α β t :=
  polynomialTransition4_nonneg _

theorem polynomialSwitch4_le_one (α β t : ℝ) : polynomialSwitch4 α β t ≤ 1 :=
  polynomialTransition4_le_one _

theorem polynomialSwitch4_eq_zero_iff (hαβ : α < β) :
    polynomialSwitch4 α β t = 0 ↔ t ≤ α := by
  rw [polynomialSwitch4, polynomialTransition4_eq_zero_iff, div_le_iff₀ (sub_pos.mpr hαβ),
    zero_mul, sub_nonpos]

theorem polynomialSwitch4_eq_one_iff (hαβ : α < β) :
    polynomialSwitch4 α β t = 1 ↔ β ≤ t := by
  rw [polynomialSwitch4, polynomialTransition4_eq_one_iff, one_le_div (sub_pos.mpr hαβ),
    sub_le_sub_iff_right]

theorem polynomialSwitch4_of_le (hαβ : α < β) (ht : t ≤ α) : polynomialSwitch4 α β t = 0 :=
  (polynomialSwitch4_eq_zero_iff hαβ).mpr ht

theorem polynomialSwitch4_of_ge (hαβ : α < β) (ht : β ≤ t) : polynomialSwitch4 α β t = 1 :=
  (polynomialSwitch4_eq_one_iff hαβ).mpr ht

theorem monotone_polynomialSwitch4 (hαβ : α ≤ β) : Monotone (polynomialSwitch4 α β) :=
  fun _ _ h => monotone_polynomialTransition4
    (div_le_div_of_nonneg_right (sub_le_sub_right h α) (sub_nonneg.mpr hαβ))

/-- Rescaled switches have Lipschitz fourth roots, even for reversed or equal endpoints. -/
theorem exists_lipschitzWith_polynomialSwitch4_root (α β : ℝ) :
    ∃ K, LipschitzWith K fun t => polynomialSwitch4 α β t ^ (4⁻¹ : ℝ) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_polynomialTransition4_root
  refine ⟨K * (‖(β - α)⁻¹‖₊ * 1), ?_⟩
  simpa only [polynomialSwitch4, Function.comp_def, smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv,
    mul_comm] using hK.comp
    ((lipschitzWith_smul (β - α)⁻¹).comp (isometry_add_right (-α)).lipschitzWith)

/-- The complementary rescaled switches also have Lipschitz fourth roots. -/
theorem exists_lipschitzWith_one_sub_polynomialSwitch4_root (α β : ℝ) :
    ∃ K, LipschitzWith K fun t => (1 - polynomialSwitch4 α β t) ^ (4⁻¹ : ℝ) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_one_sub_polynomialTransition4_root
  refine ⟨K * (‖(β - α)⁻¹‖₊ * 1), ?_⟩
  simpa only [polynomialSwitch4, Function.comp_def, smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv,
    mul_comm] using hK.comp
    ((lipschitzWith_smul (β - α)⁻¹).comp (isometry_add_right (-α)).lipschitzWith)

@[simp, norm_cast]
theorem transitionPolynomial4_ratCast (t : ℚ) :
    transitionPolynomial4 (t : ℝ) = (transitionPolynomial4 t : ℚ) := by
  simp [transitionPolynomial4]

@[simp, norm_cast]
theorem polynomialTransition4_ratCast (t : ℚ) :
    polynomialTransition4 (t : ℝ) = (polynomialTransition4 t : ℚ) := by
  simp only [polynomialTransition4, ← transitionPolynomial4_ratCast, Rat.cast_max, Rat.cast_min,
    Rat.cast_zero, Rat.cast_one]

@[simp, norm_cast]
theorem polynomialSwitch4_ratCast (α β t : ℚ) :
    polynomialSwitch4 (α : ℝ) β t = (polynomialSwitch4 α β t : ℚ) := by
  simp only [polynomialSwitch4, ← polynomialTransition4_ratCast, Rat.cast_div, Rat.cast_sub]

end Cslib
