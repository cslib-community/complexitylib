/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.LossMinimization.StochasticGradientDescent

/-! Checks for stochastic gradient descent and the convex online-to-batch conversion on the
absolute loss `|w - z|` on `ℝ` (median estimation): the subgradient and Lipschitz hypotheses, a
concrete iterate, and the bound `𝔼 L_D(w̄) ≤ L_D(u) + 1 / 2` for four unconstrained steps from `0`
with step size `1 / 2`, for every distribution `D` with a first moment and every `|u| ≤ 1`. -/

namespace CslibFrontierTests.StochasticGradientDescent

open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning.OCO MeasureTheory
open scoped RealInnerProductSpace

/-- The absolute loss of the prediction `w` on the example `z`. -/
noncomputable def absLoss (w z : ℝ) : ℝ := |w - z|

/-- A subgradient of `absLoss · z` at `w`: `-1` for `w ≤ z` and `1` otherwise. -/
noncomputable def absGrad (w z : ℝ) : ℝ := if w ≤ z then -1 else 1

theorem absLoss_add_inner_le (z w y : ℝ) : absLoss w z + ⟪absGrad w z, y - w⟫ ≤ absLoss y z := by
  rw [Real.inner_apply]
  unfold absLoss absGrad
  split_ifs with h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [neg_abs_le (y - z)]
  · rw [abs_of_pos (sub_pos.mpr (not_le.mp h))]
    linarith [le_abs_self (y - z)]

theorem norm_absGrad_le (w z : ℝ) : ‖absGrad w z‖ ≤ 1 := by
  unfold absGrad
  split_ifs <;> simp

theorem measurable_absLoss : Measurable (Function.uncurry absLoss) :=
  show Measurable fun p : ℝ × ℝ => |p.1 - p.2| from
    (continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable

theorem measurable_absGrad : Measurable (Function.uncurry absGrad) :=
  show Measurable fun p : ℝ × ℝ => if p.1 ≤ p.2 then (-1 : ℝ) else 1 from
    Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
      measurable_const

/-- SGD follows the sample: from `0`, after the example `1` the iterate moves to `1 / 2`. -/
example : sgd id (fun _ => (1 : ℝ) / 2) absGrad 0 ![(1 : ℝ), -1] 1 = 1 / 2 := by
  rw [sgd_def, ogd_succ, ogd_zero]
  norm_num [absGrad]

/-- Four unconstrained steps of SGD from `0` with step size `1 / 2` on the absolute loss: for every
distribution `D` with a first moment and every comparator `|u| ≤ 1`, the average iterate has
expected true risk at most `L_D(u) + 1 / 2`. -/
example (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable id D) {u : ℝ} (hu : |u| ≤ 1) :
    ∫ S : Fin 4 → ℝ, trueRisk absLoss D
        ((4 : ℝ)⁻¹ • ∑ t : Fin 4, sgd id (fun _ => 1 / 2) absGrad 0 S t) ∂Measure.pi (fun _ => D) ≤
      trueRisk absLoss D u + 1 / 2 := by
  have hint : Integrable (absLoss 0) D := by
    have e : absLoss 0 = fun z => |id z| := funext fun z => by simp [absLoss]
    rw [e]
    exact hD.abs
  have h := integral_trueRisk_sgd_average_le (T := 4) (by norm_num) convex_univ
    isPythagoreanProjection_id measurable_id measurable_absLoss measurable_absGrad
    (fun z x _ y _ => absLoss_add_inner_le z x y) one_pos (fun z x _ => norm_absGrad_le x z)
    (Set.mem_univ 0) hint (Set.mem_univ u) one_pos (by simpa using hu)
  have hs : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  simpa only [Nat.cast_ofNat, hs, one_mul, mul_one] using h

/-- Projected SGD on `[-1, 1]` with high probability: four steps from `0` with step size `1 / 2`
on the absolute loss, projecting onto `[-1, 1]`, whose diameter is `2`. For every distribution
`D` with a first moment, every comparator `u ∈ [-1, 1]` and every `δ ∈ (0, 1]`, outside an event
of probability at most `δ` the average iterate has true risk at most
`L_D(u) + 1 / 2 + √(2 ln (1 / δ))`. -/
example (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable id D) {u : ℝ}
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ => D).real {S : Fin 4 → ℝ |
      trueRisk absLoss D u + 1 / 2 + √(2 * Real.log (1 / δ)) <
        trueRisk absLoss D ((4 : ℝ)⁻¹ • ∑ t : Fin 4,
          sgd (Cslib.metricProjection (Set.Icc (-1) 1)) (fun _ => 1 / 2) absGrad 0 S t)} ≤
      δ := by
  have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := Set.nonempty_Icc.2 (by norm_num)
  have hc : IsComplete (Set.Icc (-1 : ℝ) 1) := isClosed_Icc.isComplete
  have hint : Integrable (absLoss 0) D := by
    have e : absLoss 0 = fun z => |id z| := funext fun z => by simp [absLoss]
    rw [e]
    exact hD.abs
  have hd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, ‖x - y‖ ≤ 2 := fun x hx y hy => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hx₀u : ‖(0 : ℝ) - u‖ ≤ 1 := by
    rw [zero_sub, norm_neg, Real.norm_eq_abs, abs_le]
    exact hu
  have h := measureReal_trueRisk_sgd_average_gt_le (T := 4) (by norm_num) (convex_Icc _ _)
    (isPythagoreanProjection_metricProjection hne hc (convex_Icc _ _))
    (Cslib.lipschitzWith_metricProjection hne hc (convex_Icc _ _)).continuous.measurable
    measurable_absLoss measurable_absGrad (fun z x _ y _ => absLoss_add_inner_le z x y) one_pos
    (fun z x _ => norm_absGrad_le x z) (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) hint hu
    one_pos hx₀u hd hδ hδ1
  have hs : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hdev : 1 * 2 * √(2 * Real.log (1 / δ) / ((4 : ℕ) : ℝ)) = √(2 * Real.log (1 / δ)) := by
    rw [Real.sqrt_div' _ (by norm_num), Nat.cast_ofNat, hs]
    ring
  have hrate : (1 : ℝ) * 1 / √((4 : ℕ) : ℝ) = 1 / 2 := by
    rw [Nat.cast_ofNat, hs, one_mul]
  have hstep : (1 : ℝ) / (1 * √((4 : ℕ) : ℝ)) = 1 / 2 := by
    rw [Nat.cast_ofNat, hs, one_mul]
  rw [hdev, hrate, hstep] at h
  simpa only [Nat.cast_ofNat] using h

/-- The absolute loss regularized by `w ^ 2 / 2`, which is `1`-strongly convex. -/
noncomputable def regAbsLoss (w z : ℝ) : ℝ := |w - z| + w ^ 2 / 2

/-- A subgradient of `regAbsLoss · z` at `w`. -/
noncomputable def regAbsGrad (w z : ℝ) : ℝ := absGrad w z + w

theorem regAbsLoss_strongConvex (z x y : ℝ) :
    regAbsLoss x z + ⟪regAbsGrad x z, y - x⟫ + 1 / 2 * ‖y - x‖ ^ 2 ≤ regAbsLoss y z := by
  have h := absLoss_add_inner_le z x y
  rw [Real.inner_apply] at h ⊢
  simp only [regAbsLoss, regAbsGrad, absLoss, Real.norm_eq_abs, sq_abs] at h ⊢
  linear_combination h

/-- SGD for strongly convex losses on `[-1, 1]`: `T ≥ 1` steps from `0` with step sizes
`1 / (t + 1)` on the regularized absolute loss, whose subgradients have norm at most `2` there.
For every distribution `D` with a first moment and every `u ∈ [-1, 1]`, the average iterate has
expected true risk at most `L_D(u) + 2 (1 + log T) / T`. -/
example (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable id D) {u : ℝ}
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) {T : ℕ} (hT : 0 < T) :
    ∫ S : Fin T → ℝ, trueRisk regAbsLoss D ((T : ℝ)⁻¹ • ∑ t : Fin T,
        sgd (Cslib.metricProjection (Set.Icc (-1) 1)) (fun t => 1 / ((t : ℝ) + 1)) regAbsGrad 0
          S t) ∂Measure.pi (fun _ => D) ≤
      trueRisk regAbsLoss D u + 2 * (1 + Real.log T) / T := by
  have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := Set.nonempty_Icc.2 (by norm_num)
  have hc : IsComplete (Set.Icc (-1 : ℝ) 1) := isClosed_Icc.isComplete
  have hint : Integrable (regAbsLoss 0) D := by
    have e : regAbsLoss 0 = fun z => |id z| := funext fun z => by simp [regAbsLoss]
    rw [e]
    exact hD.abs
  have hℓ : Measurable (Function.uncurry regAbsLoss) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => |p.1 - p.2| + p.1 ^ 2 / 2).measurable
  have hg : Measurable (Function.uncurry regAbsGrad) :=
    show Measurable fun p : ℝ × ℝ => absGrad p.1 p.2 + p.1 from
      measurable_absGrad.add measurable_fst
  have hgρ : ∀ z, ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖regAbsGrad x z‖ ≤ 2 := fun z x hx => by
    have h1 := norm_absGrad_le x z
    have h2 : ‖x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; exact hx
    exact (norm_add_le _ _).trans (by linarith)
  have h := integral_trueRisk_sgd_average_le_of_strongConvex hT (convex_Icc _ _)
    (isPythagoreanProjection_metricProjection hne hc (convex_Icc _ _))
    (Cslib.lipschitzWith_metricProjection hne hc (convex_Icc _ _)).continuous.measurable hℓ hg
    one_pos (fun z x _ y _ => regAbsLoss_strongConvex z x y) hgρ
    (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) hint hu
  have e : trueRisk regAbsLoss D u + 2 ^ 2 * (1 + Real.log T) / (2 * 1 * T) =
      trueRisk regAbsLoss D u + 2 * (1 + Real.log T) / T := by
    ring
  rw [e] at h
  simpa only [one_mul] using h

end CslibFrontierTests.StochasticGradientDescent
