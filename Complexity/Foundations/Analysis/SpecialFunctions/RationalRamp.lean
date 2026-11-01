/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A rational correction ramp with Lipschitz fourth root

For `a > 0`, put `u = max 0 ((t - θ) / a)` and `Q t = a * u^4 / (1 + u)^3`.
This gives a monotone, one-Lipschitz correction ramp with
`t - (θ + 3a) ≤ Q t ≤ max (t - θ) 0`. Its fourth root is globally Lipschitz.
The definitions specialize to exact rational arithmetic; this is not a machine-space bound.

This is an alternative rational witness for the ramp conditions in
[OpenAI2026LogSpace, Section 4.1, (4.2)], adapted to the fourth-moment workstream of complexitylib
issue #1721. The pinned preprint requires eighth-root regularity and gives a piecewise-polynomial
example; this module proves fourth-root regularity for the displayed rational construction.

## Main definitions

* `Cslib.rationalRamp4Unit`: the normalized ramp, zero on nonpositive inputs.
* `Cslib.rationalRamp4`: translation and rescaling of the normalized ramp.

## Main results

* `Cslib.rationalRamp4_nonneg`, `Cslib.rationalRamp4_le`, `Cslib.le_rationalRamp4`: ramp bounds.
* `Cslib.monotone_rationalRamp4`, `Cslib.lipschitzWith_rationalRamp4`: monotonicity and Lipschitz
  constant one.
* `Cslib.lipschitzWith_rationalRamp4_root`: global fourth-root regularity.
* `Cslib.rationalRamp4_ratCast`: compatibility with exact rational evaluation.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4.1 (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib

open scoped NNReal

/-- The normalized rational ramp, with fourth-order vanishing at zero. -/
@[expose] def rationalRamp4Unit {R : Type*} [Field R] [LinearOrder R] (t : R) : R :=
  (max 0 t) ^ 4 / (1 + max 0 t) ^ 3

/-- A rational correction ramp with lower support threshold `θ` and width parameter `a`.
The analytic ramp laws assume `0 < a`. -/
@[expose] def rationalRamp4 {R : Type*} [Field R] [LinearOrder R] (θ a t : R) : R :=
  a * rationalRamp4Unit ((t - θ) / a)

private theorem core_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => t ^ 4 / (1 + t) ^ 3)
      (t ^ 3 * (t + 4) / (1 + t) ^ 4) t := by
  have hp : 0 < 1 + t := by positivity
  convert (hasDerivAt_pow 4 t).div (((hasDerivAt_id t).const_add 1).pow 3)
    (pow_ne_zero _ hp.ne') using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq]
    field_simp
    ring

private theorem core_deriv_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ 3 * (t + 4) / (1 + t) ^ 4 := by positivity

private theorem core_deriv_le_one {t : ℝ} (ht : 0 ≤ t) :
    t ^ 3 * (t + 4) / (1 + t) ^ 4 ≤ 1 := by
  apply (div_le_one (by positivity : 0 < (1 + t) ^ 4)).2
  nlinarith [sq_nonneg t]

private theorem core_monotoneOn :
    MonotoneOn (fun t : ℝ => t ^ 4 / (1 + t) ^ 3) (Set.Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t ht => (core_hasDerivAt ht).continuousAt.continuousWithinAt)
    (fun t ht => (core_hasDerivAt (interior_subset ht)).hasDerivWithinAt) ?_
  exact fun t ht => core_deriv_nonneg (interior_subset ht)

private theorem core_lipschitzOnWith :
    LipschitzOnWith 1 (fun t : ℝ => t ^ 4 / (1 + t) ^ 3) (Set.Ici 0) := by
  refine (convex_Ici 0).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (core_hasDerivAt ht).hasDerivWithinAt) ?_
  intro t ht
  change |t ^ 3 * (t + 4) / (1 + t) ^ 4| ≤ (1 : ℝ)
  rw [abs_of_nonneg (core_deriv_nonneg ht)]
  exact core_deriv_le_one ht

theorem rationalRamp4Unit_nonneg (t : ℝ) : 0 ≤ rationalRamp4Unit t := by
  unfold rationalRamp4Unit
  positivity

theorem rationalRamp4Unit_le (t : ℝ) : rationalRamp4Unit t ≤ max 0 t := by
  have hu : 0 ≤ max 0 t := le_max_left _ _
  have hpow : 0 ≤ (max 0 t) ^ 3 := by positivity
  apply (div_le_iff₀ (by positivity : 0 < (1 + max 0 t) ^ 3)).2
  nlinarith [sq_nonneg (max 0 t)]

theorem sub_three_le_rationalRamp4Unit (t : ℝ) : t - 3 ≤ rationalRamp4Unit t := by
  have hu : 0 ≤ max 0 t := le_max_left _ _
  apply (le_div_iff₀ (by positivity : 0 < (1 + max 0 t) ^ 3)).2
  have h := mul_le_mul_of_nonneg_right (sub_le_sub_right (le_max_right 0 t) 3)
    (show 0 ≤ (1 + max 0 t) ^ 3 by positivity)
  nlinarith [sq_nonneg (max 0 t)]

theorem rationalRamp4Unit_of_nonpos {t : ℝ} (ht : t ≤ 0) : rationalRamp4Unit t = 0 := by
  simp [rationalRamp4Unit, max_eq_left ht]

theorem monotone_rationalRamp4Unit : Monotone (rationalRamp4Unit : ℝ → ℝ) :=
  fun _ _ h => core_monotoneOn (le_max_left _ _) (le_max_left _ _) (max_le_max le_rfl h)

theorem lipschitzWith_rationalRamp4Unit : LipschitzWith 1 (rationalRamp4Unit : ℝ → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := core_lipschitzOnWith.dist_le_mul (max 0 x) (le_max_left _ _)
    (max 0 y) (le_max_left _ _)
  simp only [NNReal.coe_one, one_mul] at h
  have hc := (LipschitzWith.id.const_max (0 : ℝ)).dist_le_mul x y
  exact h.trans hc

/-! ## Fourth roots -/

private theorem core_root_eq {t : ℝ} (ht : 0 ≤ t) :
    (t ^ 4 / (1 + t) ^ 3) ^ (4⁻¹ : ℝ) = t * (1 + t) ^ (-(3 / 4 : ℝ)) := by
  have hfour : (t ^ 4) ^ (4⁻¹ : ℝ) = t := by
    convert Real.pow_rpow_inv_natCast ht (by norm_num : (4 : ℕ) ≠ 0) using 1
  rw [Real.div_rpow (by positivity) (by positivity), hfour,
    ← Real.rpow_natCast_mul (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv]
  norm_num

private theorem root_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => t * (1 + t) ^ (-(3 / 4 : ℝ)))
      ((1 + t) ^ (-(7 / 4 : ℝ)) * (1 + t / 4)) t := by
  have hp : 0 < 1 + t := by positivity
  have he : (1 + t) ^ (-(3 / 4 : ℝ)) = (1 + t) ^ (-(7 / 4 : ℝ)) * (1 + t) := by
    rw [← Real.rpow_add_one hp.ne']
    norm_num
  convert (hasDerivAt_id t).mul (((hasDerivAt_id t).const_add 1).rpow_const
    (p := -(3 / 4 : ℝ)) (Or.inl hp.ne'))
    using 1
  · rfl
  · simp only [id_eq, one_mul]
    rw [he]
    norm_num
    ring

private theorem root_deriv_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (1 + t) ^ (-(7 / 4 : ℝ)) * (1 + t / 4) := by positivity

private theorem root_deriv_le_one {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ (-(7 / 4 : ℝ)) * (1 + t / 4) ≤ 1 := by
  have hp : 0 < 1 + t := by positivity
  calc (1 + t) ^ (-(7 / 4 : ℝ)) * (1 + t / 4) ≤
      (1 + t) ^ (-(7 / 4 : ℝ)) * (1 + t) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hp.le _)
    _ = (1 + t) ^ (-(3 / 4 : ℝ)) := by rw [← Real.rpow_add_one hp.ne']; norm_num
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)

private theorem root_lipschitzOnWith :
    LipschitzOnWith 1 (fun t : ℝ => t * (1 + t) ^ (-(3 / 4 : ℝ))) (Set.Ici 0) := by
  refine (convex_Ici 0).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (root_hasDerivAt ht).hasDerivWithinAt) ?_
  intro t ht
  change |(1 + t) ^ (-(7 / 4 : ℝ)) * (1 + t / 4)| ≤ (1 : ℝ)
  rw [abs_of_nonneg (root_deriv_nonneg ht)]
  exact root_deriv_le_one ht

/-- The normalized ramp's fourth root has global Lipschitz constant one. -/
theorem lipschitzWith_rationalRamp4Unit_root :
    LipschitzWith 1 fun t : ℝ => rationalRamp4Unit t ^ (4⁻¹ : ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := root_lipschitzOnWith.dist_le_mul (max 0 x) (le_max_left _ _)
    (max 0 y) (le_max_left _ _)
  rw [← core_root_eq (le_max_left _ _), ← core_root_eq (le_max_left _ _)] at h
  simp only [NNReal.coe_one, one_mul] at h
  exact h.trans ((LipschitzWith.id.const_max (0 : ℝ)).dist_le_mul x y)

/-! ## Translation and rescaling -/

variable {θ a t : ℝ}

theorem rationalRamp4_nonneg (ha : 0 ≤ a) (θ t : ℝ) : 0 ≤ rationalRamp4 θ a t :=
  mul_nonneg ha (rationalRamp4Unit_nonneg _)

theorem rationalRamp4_le (ha : 0 < a) (θ t : ℝ) :
    rationalRamp4 θ a t ≤ max (t - θ) 0 := by
  calc rationalRamp4 θ a t ≤ a * max 0 ((t - θ) / a) :=
      mul_le_mul_of_nonneg_left (rationalRamp4Unit_le _) ha.le
    _ = max (t - θ) 0 := by
      rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
      simp [mul_div_cancel₀, ha.ne', max_comm]

theorem le_rationalRamp4 (ha : 0 < a) (θ t : ℝ) :
    t - (θ + 3 * a) ≤ rationalRamp4 θ a t := by
  calc t - (θ + 3 * a) = a * ((t - θ) / a - 3) := by field_simp; ring
    _ ≤ rationalRamp4 θ a t :=
      mul_le_mul_of_nonneg_left (sub_three_le_rationalRamp4Unit _) ha.le

theorem rationalRamp4_of_le (ha : 0 < a) (ht : t ≤ θ) : rationalRamp4 θ a t = 0 := by
  rw [rationalRamp4, rationalRamp4Unit_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ht) ha.le), mul_zero]

theorem monotone_rationalRamp4 (ha : 0 < a) (θ : ℝ) : Monotone (rationalRamp4 θ a) :=
  fun _ _ h => mul_le_mul_of_nonneg_left (monotone_rationalRamp4Unit
    (div_le_div_of_nonneg_right (sub_le_sub_right h θ) ha.le)) ha.le

/-- The scale factor cancels the input rescaling, preserving Lipschitz constant one. -/
theorem lipschitzWith_rationalRamp4 (ha : 0 < a) (θ : ℝ) :
    LipschitzWith 1 (rationalRamp4 θ a) := by
  change LipschitzWith 1 (fun t : ℝ => a * rationalRamp4Unit ((t - θ) / a))
  have h := (lipschitzWith_smul a).comp (lipschitzWith_rationalRamp4Unit.comp
    ((lipschitzWith_smul a⁻¹).comp (isometry_add_right (-θ)).lipschitzWith))
  simpa only [mul_one, one_mul, ← nnnorm_mul, mul_inv_cancel₀ ha.ne', nnnorm_one,
    Function.comp_def, smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
    using h

/-- The rescaled ramp's fourth root is globally Lipschitz, including arbitrarily large inputs. -/
theorem lipschitzWith_rationalRamp4_root (ha : 0 < a) (θ : ℝ) :
    LipschitzWith (‖a ^ (4⁻¹ : ℝ)‖₊ * ‖a⁻¹‖₊)
      fun t : ℝ => rationalRamp4 θ a t ^ (4⁻¹ : ℝ) := by
  have h := (lipschitzWith_smul (a ^ (4⁻¹ : ℝ))).comp (lipschitzWith_rationalRamp4Unit_root.comp
    ((lipschitzWith_smul a⁻¹).comp (isometry_add_right (-θ)).lipschitzWith))
  simpa only [mul_one, one_mul, rationalRamp4, Real.mul_rpow ha.le (rationalRamp4Unit_nonneg _),
    Function.comp_def, smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv, mul_comm] using h

@[simp, norm_cast]
theorem rationalRamp4Unit_ratCast (t : ℚ) :
    rationalRamp4Unit (t : ℝ) = (rationalRamp4Unit t : ℚ) := by
  simp [rationalRamp4Unit, Rat.cast_max]

@[simp, norm_cast]
theorem rationalRamp4_ratCast (θ a t : ℚ) :
    rationalRamp4 (θ : ℝ) a t = (rationalRamp4 θ a t : ℚ) := by
  simp only [rationalRamp4, Rat.cast_mul, ← rationalRamp4Unit_ratCast, Rat.cast_div, Rat.cast_sub]

end Cslib
