/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.Smooth
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The squared loss and ridge regression

The *squared loss* of a linear predictor `w` on a point `x` with label `y` is
`(⟪w, x⟫ - y)² / 2` [ShalevShwartzBenDavid2014, (13.3)]. It is convex and nonnegative in `w`,
and its derivative `(⟪w, x⟫ - y) ⟪x, ·⟫` is `‖x‖²`-Lipschitz [ShalevShwartzBenDavid2014,
Example 12.6]. *Ridge regression*, Tikhonov regularized minimization of the empirical squared risk
over all of `E` [ShalevShwartzBenDavid2014, Section 13.1.1], therefore inherits the oracle
inequality of `Cslib.MachineLearning.IsRLM` for smooth losses.

Examples `z` are described by a feature map `φ : Z → E` and real labels `y : Z → ℝ`, with
`‖φ z‖ ≤ 1` and `|y z| ≤ 1` as in the source.

## Main definitions

* `Cslib.MachineLearning.squaredLoss`: the squared loss `(⟪w, x⟫ - y)² / 2`.

## Main results

* `Cslib.MachineLearning.convexOn_squaredLoss`: the squared loss is convex in `w`.
* `Cslib.MachineLearning.hasFDerivAt_squaredLoss`: its derivative at `w` is
  `(⟪w, x⟫ - y) ⟪x, ·⟫`.
* `Cslib.MachineLearning.lipschitzWith_fderiv_squaredLoss`: the derivative is `‖x‖²`-Lipschitz
  [ShalevShwartzBenDavid2014, Example 12.6].
* `Cslib.MachineLearning.IsRLM.integral_trueRisk_squaredLoss_le_add`: ridge regression with
  `r = ε / (3 B²)` on `m ≥ 150 B² / ε²` examples has expected squared risk within `ε` of every
  predictor of norm at most `B` [ShalevShwartzBenDavid2014, Theorem 13.1].

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Sections 12.1.3 and 13.1.1
-/

public section

open MeasureTheory

namespace Cslib.MachineLearning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **squared loss** `(⟪w, x⟫ - y)² / 2` of the linear predictor `w` on the point `x` with
label `y` [ShalevShwartzBenDavid2014, (13.3)]. -/
noncomputable def squaredLoss (w x : E) (y : ℝ) : ℝ :=
  (inner ℝ w x - y) ^ 2 / 2

theorem squaredLoss_def (w x : E) (y : ℝ) : squaredLoss w x y = (inner ℝ w x - y) ^ 2 / 2 := by
  rw [squaredLoss]

theorem squaredLoss_nonneg (w x : E) (y : ℝ) : 0 ≤ squaredLoss w x y := by
  rw [squaredLoss_def]
  positivity

theorem squaredLoss_zero (x : E) (y : ℝ) : squaredLoss 0 x y = y ^ 2 / 2 := by
  simp [squaredLoss_def]

/-- The squared loss is convex in the predictor. -/
theorem convexOn_squaredLoss (x : E) (y : ℝ) :
    ConvexOn ℝ Set.univ fun w => squaredLoss w x y := by
  refine ⟨convex_univ, fun w _ w' _ a b ha hb hab => ?_⟩
  simp only [squaredLoss_def, inner_add_left, real_inner_smul_left, smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_nonneg ha hb, sq_nonneg (inner ℝ w x - inner ℝ w' x),
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg (inner ℝ w x - inner ℝ w' x))]

/-- The derivative of the squared loss at `w` is `(⟪w, x⟫ - y) ⟪x, ·⟫`. -/
theorem hasFDerivAt_squaredLoss (w x : E) (y : ℝ) :
    HasFDerivAt (fun w => squaredLoss w x y) ((inner ℝ w x - y) • innerSL ℝ x) w := by
  have hlin : HasFDerivAt (fun w : E => inner ℝ w x - y) (innerSL ℝ x) w := by
    have h : HasFDerivAt (fun w : E => inner ℝ x w) (innerSL ℝ x) w := by
      simpa only [coe_innerSL_apply] using (innerSL ℝ x).hasFDerivAt (x := w)
    have hf : (fun w : E => inner ℝ w x - y) = fun w => inner ℝ x w - y := by
      funext w
      rw [real_inner_comm]
    rw [hf]
    exact h.sub_const y
  have h := (hlin.mul hlin).const_mul (1 / 2 : ℝ)
  convert h using 1
  · funext w
    rw [squaredLoss_def, Pi.mul_apply]
    ring
  · rw [← two_smul ℝ ((inner ℝ w x - y) • innerSL ℝ x), smul_smul]
    norm_num

theorem fderiv_squaredLoss (w x : E) (y : ℝ) :
    fderiv ℝ (fun w => squaredLoss w x y) w = (inner ℝ w x - y) • innerSL ℝ x :=
  (hasFDerivAt_squaredLoss w x y).fderiv

theorem differentiable_squaredLoss (x : E) (y : ℝ) :
    Differentiable ℝ fun w => squaredLoss w x y :=
  fun w => (hasFDerivAt_squaredLoss w x y).differentiableAt

/-- The derivative of the squared loss is `‖x‖²`-Lipschitz, so the squared loss is
`‖x‖²`-smooth [ShalevShwartzBenDavid2014, Example 12.6]. -/
theorem lipschitzWith_fderiv_squaredLoss (x : E) (y : ℝ) :
    LipschitzWith ⟨‖x‖ ^ 2, by positivity⟩ (fderiv ℝ fun w => squaredLoss w x y) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  change dist _ _ ≤ ‖x‖ ^ 2 * dist w w'
  rw [fderiv_squaredLoss, fderiv_squaredLoss, dist_eq_norm, ← sub_smul, norm_smul,
    innerSL_apply_norm, Real.norm_eq_abs, dist_eq_norm]
  calc |inner ℝ w x - y - (inner ℝ w' x - y)| * ‖x‖ = |inner ℝ (w - w') x| * ‖x‖ := by
        rw [inner_sub_left, sub_sub_sub_cancel_right]
    _ ≤ ‖w - w'‖ * ‖x‖ * ‖x‖ := by
        gcongr
        exact abs_real_inner_le_norm _ _
    _ = ‖x‖ ^ 2 * ‖w - w'‖ := by ring

/-- With `‖x‖ ≤ 1`, the derivative of the squared loss is `1`-Lipschitz. -/
theorem lipschitzWith_fderiv_squaredLoss_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) (y : ℝ) :
    LipschitzWith 1 (fderiv ℝ fun w => squaredLoss w x y) :=
  (lipschitzWith_fderiv_squaredLoss x y).weaken <| by
    change ‖x‖ ^ 2 ≤ ((1 : NNReal) : ℝ)
    rw [NNReal.coe_one]
    exact pow_le_one₀ (norm_nonneg x) hx

/-- **Learnability by ridge regression** [ShalevShwartzBenDavid2014, Theorem 13.1]: let `A` be a
ridge regression rule, a minimizer of the empirical squared risk plus `r‖w‖²` over all of `E`. If
every example `z` has feature vector `‖φ z‖ ≤ 1` and label `|y z| ≤ 1`, then for `ε ∈ (0, 1)`,
`B > 0`, `r = ε / (3 B²)`, `m ≥ 150 B² / ε²` i.i.d. examples from `D` and every `w` with
`‖w‖ ≤ B`, `𝔼_S [L_D(A S)] ≤ L_D(w) + ε`, where `L_D` is the true squared risk.

The integrability hypotheses are those of
`Cslib.MachineLearning.integral_trueRisk_sub_empiricalRisk`; they hold automatically when `Z` is
finite with measurable singletons. -/
theorem IsRLM.integral_trueRisk_squaredLoss_le_add {Z : Type*} [MeasurableSpace Z] {φ : Z → E}
    {y : Z → ℝ} (hφ : ∀ z, ‖φ z‖ ≤ 1) (hy : ∀ z, |y z| ≤ 1) {ε B : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hB : 0 < B) {m : ℕ} (hm : 150 * B ^ 2 / ε ^ 2 ≤ m) {r : ℝ} (hr : r = ε / (3 * B ^ 2))
    {A : (Fin m → Z) → E}
    (hA : IsRLM (fun w z => squaredLoss w (φ z) (y z)) (fun w => r * ‖w‖ ^ 2) Set.univ A)
    (D : Measure Z) [IsProbabilityMeasure D]
    (hint : Integrable (fun p : (Fin m → Z) × Z => squaredLoss (A p.1) (φ p.2) (y p.2))
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => squaredLoss (A S) (φ (S i)) (y (S i)))
      (Measure.pi fun _ : Fin m => D))
    {w : E} (hwB : ‖w‖ ≤ B) (hwint : Integrable (fun z => squaredLoss w (φ z) (y z)) D) :
    ∫ S, trueRisk (fun w z => squaredLoss w (φ z) (y z)) D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
      trueRisk (fun w z => squaredLoss w (φ z) (y z)) D w + ε := by
  have hm0 : 0 < m := by
    have : 0 < 150 * B ^ 2 / ε ^ 2 := by positivity
    exact_mod_cast this.trans_le hm
  refine hA.integral_trueRisk_le_add_of_lipschitzWith_fderiv (β := 1) convex_univ
    (Set.mem_univ 0) (fun z => convexOn_squaredLoss (φ z) (y z))
    (fun z => differentiable_squaredLoss (φ z) (y z))
    (fun z => lipschitzWith_fderiv_squaredLoss_of_norm_le_one (hφ z) (y z))
    (fun w z => squaredLoss_nonneg w (φ z) (y z)) (fun z => ?_) hε hε1 hB hm0
    (by rwa [NNReal.coe_one, mul_one]) hr D hint hint' (Set.mem_univ w) hwB hwint
  rw [squaredLoss_zero]
  have : y z ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hy z)
  linarith

end Cslib.MachineLearning
