/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.RLM

/-!
# The hinge loss and Soft-SVM

The *hinge loss* of a linear predictor `w` on a point `x` with label `y` is
`max 0 (1 - y ⟪w, x⟫)` [ShalevShwartzBenDavid2014, Section 12.3]. It is convex
in `w` and `|y| ‖x‖`-Lipschitz [ShalevShwartzBenDavid2014, Claim 15.6], so *Soft-SVM*, Tikhonov
regularized minimization of the empirical hinge risk [ShalevShwartzBenDavid2014, (15.6)], inherits
the stability and oracle inequality of `Cslib.MachineLearning.IsRLM`.

Examples `z` are described by a feature map `φ : Z → E` and real labels `y : Z → ℝ`. The source
uses labels `±1` and points of norm at most `ρ`; here `|y z| ≤ 1` and `‖φ z‖ ≤ ρ` for every `z`.

## Main definitions

* `Cslib.MachineLearning.hingeLoss`: the hinge loss `max 0 (1 - y ⟪w, x⟫)`.

## Main results

* `Cslib.MachineLearning.convexOn_hingeLoss`: the hinge loss is convex in `w`.
* `Cslib.MachineLearning.lipschitzWith_hingeLoss`: the hinge loss is `|y| ‖x‖`-Lipschitz in `w`
  [ShalevShwartzBenDavid2014, Claim 15.6].
* `Cslib.MachineLearning.IsRLM.integral_trueRisk_hingeLoss_le`: the Soft-SVM oracle inequality
  `𝔼_S [L_D(A S)] ≤ L_D(u) + r‖u‖² + 2ρ² / (r m)` [ShalevShwartzBenDavid2014, Corollary 15.7].

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 12.3 and Chapter 15
-/

public section

open MeasureTheory

namespace Cslib.MachineLearning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **hinge loss** `max 0 (1 - y ⟪w, x⟫)` of the linear predictor `w` on the point `x` with
label `y` [ShalevShwartzBenDavid2014, Section 12.3]. -/
noncomputable def hingeLoss (w x : E) (y : ℝ) : ℝ :=
  max 0 (1 - y * inner ℝ w x)

theorem hingeLoss_def (w x : E) (y : ℝ) : hingeLoss w x y = max 0 (1 - y * inner ℝ w x) := by
  rw [hingeLoss]

theorem hingeLoss_nonneg (w x : E) (y : ℝ) : 0 ≤ hingeLoss w x y := by
  rw [hingeLoss_def]
  exact le_max_left _ _

/-- The hinge loss vanishes when the margin `y ⟪w, x⟫` is at least `1`. -/
theorem hingeLoss_eq_zero {w x : E} {y : ℝ} (h : 1 ≤ y * inner ℝ w x) : hingeLoss w x y = 0 := by
  rw [hingeLoss_def]
  exact max_eq_left (by linarith)

/-- The hinge loss is convex in the predictor. -/
theorem convexOn_hingeLoss (x : E) (y : ℝ) : ConvexOn ℝ Set.univ fun w => hingeLoss w x y := by
  have haff : ConvexOn ℝ Set.univ fun w : E => 1 - y * inner ℝ w x := by
    refine ⟨convex_univ, fun a _ b _ s t _ _ hst => le_of_eq ?_⟩
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
    linear_combination (-1 : ℝ) * hst
  convert (convexOn_const 0 convex_univ).sup haff using 1
  funext w
  rw [hingeLoss_def]
  rfl

/-- The hinge loss is `|y| ‖x‖`-Lipschitz in the predictor [ShalevShwartzBenDavid2014,
Claim 15.6]. -/
theorem lipschitzWith_hingeLoss (x : E) (y : ℝ) :
    LipschitzWith ⟨|y| * ‖x‖, by positivity⟩ fun w => hingeLoss w x y := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  simp only [dist_eq_norm, hingeLoss_def]
  calc |max 0 (1 - y * inner ℝ w x) - max 0 (1 - y * inner ℝ w' x)|
      ≤ |(1 - y * inner ℝ w x) - (1 - y * inner ℝ w' x)| := by
        rw [max_comm 0, max_comm 0]
        exact abs_max_sub_max_le_abs _ _ _
    _ = |y * inner ℝ (w - w') x| := by
        rw [inner_sub_left, ← abs_neg]
        congr 1
        ring
    _ = |y| * |inner ℝ (w - w') x| := abs_mul _ _
    _ ≤ |y| * (‖w - w'‖ * ‖x‖) := by
        gcongr
        exact abs_real_inner_le_norm _ _
    _ = |y| * ‖x‖ * ‖w - w'‖ := by ring

/-- With `|y| ≤ 1` and `‖x‖ ≤ ρ`, the hinge loss is `ρ`-Lipschitz in the predictor. -/
theorem lipschitzWith_hingeLoss_of_le {x : E} {y : ℝ} {ρ : NNReal} (hx : ‖x‖ ≤ ρ)
    (hy : |y| ≤ 1) : LipschitzWith ρ fun w => hingeLoss w x y :=
  (lipschitzWith_hingeLoss x y).weaken <| by
    change |y| * ‖x‖ ≤ (ρ : ℝ)
    calc |y| * ‖x‖ ≤ 1 * ρ := by gcongr
      _ = ρ := one_mul _

theorem continuous_hingeLoss (x : E) (y : ℝ) : Continuous fun w => hingeLoss w x y :=
  (lipschitzWith_hingeLoss x y).continuous

/-- **The Soft-SVM oracle inequality** [ShalevShwartzBenDavid2014, Corollary 15.7]: let `A` be a
Soft-SVM rule, a minimizer of the empirical hinge risk plus `r‖w‖²` with `r > 0` over all of `E`.
If every example `z` has label `|y z| ≤ 1` and feature vector `‖φ z‖ ≤ ρ`, then for `m > 0`
i.i.d. examples from `D` and every `u`, `𝔼_S [L_D(A S)] ≤ L_D(u) + r‖u‖² + 2ρ² / (r m)`, where
`L_D` is the true hinge risk.

The integrability hypotheses are those of
`Cslib.MachineLearning.integral_trueRisk_sub_empiricalRisk`; they hold automatically when `Z` is
finite with measurable singletons. -/
theorem IsRLM.integral_trueRisk_hingeLoss_le {Z : Type*} [MeasurableSpace Z] {φ : Z → E}
    {y : Z → ℝ} {ρ : NNReal} (hφ : ∀ z, ‖φ z‖ ≤ ρ) (hy : ∀ z, |y z| ≤ 1) {m : ℕ} {r : ℝ}
    (hr : 0 < r) {A : (Fin m → Z) → E}
    (hA : IsRLM (fun w z => hingeLoss w (φ z) (y z)) (fun w => r * ‖w‖ ^ 2) Set.univ A)
    (D : Measure Z) [IsProbabilityMeasure D] (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => hingeLoss (A p.1) (φ p.2) (y p.2))
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => hingeLoss (A S) (φ (S i)) (y (S i)))
      (Measure.pi fun _ : Fin m => D))
    (u : E) (huint : Integrable (fun z => hingeLoss u (φ z) (y z)) D) :
    ∫ S, trueRisk (fun w z => hingeLoss w (φ z) (y z)) D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
      trueRisk (fun w z => hingeLoss w (φ z) (y z)) D u + r * ‖u‖ ^ 2 + 2 * ρ ^ 2 / (r * m) :=
  hA.integral_trueRisk_le_tikhonov convex_univ hr (fun z => convexOn_hingeLoss (φ z) (y z))
    (fun z => (lipschitzWith_hingeLoss_of_le (hφ z) (hy z)).lipschitzOnWith) D hm hint hint'
    (Set.mem_univ u) huint

end Cslib.MachineLearning
