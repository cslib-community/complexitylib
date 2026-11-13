/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/Calculus/ParametricIntegralExp.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smoothness of exponential parametric integrals

Let `φ : α → V →L[ℝ] ℝ` be a family of continuous linear functionals and `g : α → E`. The
*Laplace transform* `w ↦ ∫ a, exp (φ a w) • g a ∂μ` is `C^∞` on `V` as soon as
`exp (c ‖φ a‖) ‖g a‖` is integrable for every `c` (`contDiff_integral_exp_smul`). Its derivative is
the Laplace transform of `a ↦ (φ a).smulRight (g a)` (`hasFDerivAt_integral_exp_smul`), which
satisfies the same integrability hypothesis, so smoothness follows by induction on the order.

## Main results

* `hasFDerivAt_integral_exp_smul`: differentiation under the integral sign.
* `contDiff_integral_exp_smul`: the Laplace transform is `C^∞`.
-/

public section

open MeasureTheory Real
open scoped ContDiff

universe uV uE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Type uV} [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- The bound `exp (φ w) ≤ exp (‖w‖ ‖φ‖)` for a continuous linear functional `φ`. -/
private theorem exp_apply_le (φ : V →L[ℝ] ℝ) (w : V) : rexp (φ w) ≤ rexp (‖w‖ * ‖φ‖) := by
  gcongr
  exact (le_abs_self _).trans ((φ.le_opNorm w).trans_eq (mul_comm _ _))

/-- The derivative integrand `(φ a).smulRight (g a)` inherits the exponential integrability of
`g`. -/
private theorem integrable_exp_mul_norm_smulRight {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : α → V →L[ℝ] ℝ} {g : α → E} (hφ : AEStronglyMeasurable φ μ)
    (hg : AEStronglyMeasurable g μ)
    (hint : ∀ c : ℝ, Integrable (fun a => rexp (c * ‖φ a‖) * ‖g a‖) μ) (c : ℝ) :
    Integrable (fun a => rexp (c * ‖φ a‖) * ‖(φ a).smulRight (g a)‖) μ := by
  refine (hint (c + 1)).mono' ?_ (ae_of_all _ fun a => ?_)
  · exact (continuous_exp.comp_aestronglyMeasurable (hφ.norm.const_mul c)).mul
      ((ContinuousLinearMap.smulRightL ℝ V E).continuous₂.comp_aestronglyMeasurable₂ hφ hg).norm
  · rw [ContinuousLinearMap.norm_smulRight_apply, norm_mul, norm_of_nonneg (exp_nonneg _),
      norm_mul, norm_norm, norm_norm, add_mul, one_mul, exp_add, mul_assoc]
    gcongr
    exact (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _)

/-- **Differentiation of a Laplace transform under the integral sign**: if `exp (c ‖φ a‖) ‖g a‖`
is integrable for every `c`, then `w ↦ ∫ a, exp (φ a w) • g a ∂μ` has derivative
`∫ a, exp (φ a w) • (φ a).smulRight (g a) ∂μ` at every `w`. -/
theorem hasFDerivAt_integral_exp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : α → V →L[ℝ] ℝ} {g : α → E} (hφ : AEStronglyMeasurable φ μ)
    (hg : AEStronglyMeasurable g μ)
    (hint : ∀ c : ℝ, Integrable (fun a => rexp (c * ‖φ a‖) * ‖g a‖) μ) (w : V) :
    HasFDerivAt (fun w => ∫ a, rexp (φ a w) • g a ∂μ)
      (∫ a, rexp (φ a w) • (φ a).smulRight (g a) ∂μ) w := by
  have hmeas (x : V) : AEStronglyMeasurable (fun a => rexp (φ a x) • g a) μ :=
    (continuous_exp.comp_aestronglyMeasurable (hφ.apply_continuousLinearMap x)).smul hg
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds w zero_lt_one)
    (F' := fun x a => rexp (φ a x) • (φ a).smulRight (g a))
    (bound := fun a => rexp ((‖w‖ + 1) * ‖φ a‖) * ‖(φ a).smulRight (g a)‖)
    (Filter.Eventually.of_forall hmeas) ?_ ?_ ?_
    (integrable_exp_mul_norm_smulRight hφ hg hint _) (ae_of_all _ fun a x _ => ?_)
  · refine (hint ‖w‖).mono' (hmeas w) (ae_of_all _ fun a => ?_)
    rw [norm_smul, norm_of_nonneg (exp_nonneg _)]
    exact mul_le_mul_of_nonneg_right (exp_apply_le _ _) (norm_nonneg _)
  · exact (continuous_exp.comp_aestronglyMeasurable (hφ.apply_continuousLinearMap w)).smul
      ((ContinuousLinearMap.smulRightL ℝ V E).continuous₂.comp_aestronglyMeasurable₂ hφ hg)
  · filter_upwards with a x hx
    rw [norm_smul, norm_of_nonneg (exp_nonneg _)]
    refine mul_le_mul_of_nonneg_right (exp_le_exp.2 ?_) (norm_nonneg _)
    calc (φ a) x ≤ ‖φ a‖ * ‖x‖ := (le_abs_self _).trans ((φ a).le_opNorm x)
      _ ≤ ‖φ a‖ * (‖w‖ + 1) := by
        gcongr
        linarith [norm_sub_norm_le x w, mem_ball_iff_norm.1 hx]
      _ = (‖w‖ + 1) * ‖φ a‖ := mul_comm _ _
  · have h := ((φ a).hasFDerivAt (x := x)).exp.smul_const (g a)
    convert h using 1
    ext v
    simp [smul_smul, mul_comm]

/-- Smoothness of order `n` of the Laplace transform, for values in a universe that contains
the derivatives (`V →L[ℝ] E` lies in the same universe as `E`). -/
private theorem contDiff_integral_exp_smul_aux (φ : α → V →L[ℝ] ℝ) (hφ : AEStronglyMeasurable φ μ)
    (n : ℕ) : ∀ {E : Type (max uV uE)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : α → E}, AEStronglyMeasurable g μ →
      (∀ c : ℝ, Integrable (fun a => rexp (c * ‖φ a‖) * ‖g a‖) μ) →
      ContDiff ℝ n (fun w => ∫ a, rexp (φ a w) • g a ∂μ) := by
  induction n with
  | zero =>
    intro E _ _ _ g hg hint
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun w =>
      (hasFDerivAt_integral_exp_smul hφ hg hint w).continuousAt)
  | succ n ih =>
    intro E _ _ _ g hg hint
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih ?_ (integrable_exp_mul_norm_smulRight hφ hg hint),
      hasFDerivAt_integral_exp_smul hφ hg hint⟩
    exact (ContinuousLinearMap.smulRightL ℝ V E).continuous₂.comp_aestronglyMeasurable₂ hφ hg

/-- **Laplace transforms are smooth**: if `exp (c ‖φ a‖) ‖g a‖` is integrable for every `c`, then
`w ↦ ∫ a, exp (φ a w) • g a ∂μ` is `C^∞`. -/
theorem contDiff_integral_exp_smul {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {φ : α → V →L[ℝ] ℝ} {g : α → E} (hφ : AEStronglyMeasurable φ μ)
    (hg : AEStronglyMeasurable g μ)
    (hint : ∀ c : ℝ, Integrable (fun a => rexp (c * ‖φ a‖) * ‖g a‖) μ) :
    ContDiff ℝ ∞ (fun w => ∫ a, rexp (φ a w) • g a ∂μ) := by
  let e : ULift.{uV} E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  have h (n : ℕ) : ContDiff ℝ n (fun w => ∫ a, rexp (φ a w) • e.symm (g a) ∂μ) :=
    contDiff_integral_exp_smul_aux (E := ULift.{uV} E) φ hφ n
      (e.symm.continuous.comp_aestronglyMeasurable hg) hint
  refine contDiff_infty.2 fun n => ?_
  convert e.toContinuousLinearEquiv.contDiff.comp (h n) using 1
  funext w
  simp only [Function.comp_apply, ← map_smul, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have he := e.symm.toLinearIsometry.integral_comp_comm (μ := μ) fun a => rexp (φ a w) • g a
  simp only [LinearIsometryEquiv.coe_toLinearIsometry] at he
  rw [he, LinearIsometryEquiv.apply_symm_apply]
