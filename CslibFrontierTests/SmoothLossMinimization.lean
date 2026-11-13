/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.LossMinimization.Squared
import CslibFrontierTests.RegularizedLossMinimization
import Mathlib.Algebra.Order.BigOperators.Expect

/-! Checks for regularized loss minimization with smooth losses: the source's constant `48` in
Corollaries 13.7 and 13.10 follows from the constant `5` proved, ridge regression rules exist, and
the oracle inequality and Theorem 13.1 are evaluated with concrete numbers on a two-point
problem. -/

namespace CslibFrontierTests.SmoothLossMinimization

open Cslib.MachineLearning MeasureTheory
open CslibFrontierTests.RegularizedLossMinimization

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Z]

/-! ### The source's constants -/

/-- [ShalevShwartzBenDavid2014, Corollary 13.7] with the source's factor `48β / (r m)`. -/
example {ℓ : E → Z → ℝ} {K : Set E} {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E}
    (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A) (hK : Convex ℝ K) (hr : 0 < r)
    (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    {β : NNReal} (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z))
    (hnonneg : ∀ w z, 0 ≤ ℓ w z) (hβ : 2 * (β : ℝ) ≤ r * m) (D : Measure Z)
    [IsProbabilityMeasure D]
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D)) :
    replaceOneGap ℓ D A ≤
      48 * β / (r * m) * ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) := by
  have hE : 0 ≤ ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_nonneg fun S => Finset.expect_nonneg fun j _ => hnonneg _ _
  refine (hA.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv hK hr hconv hdiff hsmooth hnonneg
    hβ D hint').trans ?_
  gcongr
  linarith [β.2]

/-- [ShalevShwartzBenDavid2014, Corollary 13.10] with the source's factor `1 + 48β / (r m)`. -/
example {ℓ : E → Z → ℝ} {K : Set E} {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E}
    (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A) (hK : Convex ℝ K) (hr : 0 < r)
    (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    {β : NNReal} (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z))
    (hnonneg : ∀ w z, 0 ≤ ℓ w z) (hβ : 2 * (β : ℝ) ≤ r * m) (D : Measure Z)
    [IsProbabilityMeasure D] (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    {w : E} (hw : w ∈ K) (hwint : Integrable (ℓ w) D) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
        (1 + 48 * β / (r * m)) * ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) ∧
      (1 + 48 * β / (r * m)) * ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
        (1 + 48 * β / (r * m)) * (trueRisk ℓ D w + r * ‖w‖ ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hE : 0 ≤ ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_nonneg fun S => Finset.expect_nonneg fun j _ => hnonneg _ _
  have hc : 5 * (β : ℝ) / (r * m) ≤ 48 * β / (r * m) := by
    gcongr
    linarith [β.2]
  obtain ⟨h1, h2⟩ := hA.integral_trueRisk_le_tikhonov_of_lipschitzWith_fderiv hK hr hconv hdiff
    hsmooth hnonneg hβ D hm hint hint' hw hwint
  have hfit := hA.integral_empiricalRisk_le (fun _ _ => by positivity) D hm hint' hw hwint
  refine ⟨h1.trans (by gcongr), ?_⟩
  exact mul_le_mul_of_nonneg_left hfit (by positivity)

/-! ### Ridge regression on two points -/

/-- Each point is labelled by its own feature, so the predictor `1` has squared loss `0`. -/
theorem squaredLoss_one_feature (z : Bool) : squaredLoss (1 : ℝ) (feature z) (feature z) = 0 := by
  cases z <;> norm_num [squaredLoss_def, feature]

theorem norm_feature_le_one (z : Bool) : ‖feature z‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_feature]

/-- Ridge regression rules exist on samples of any size. -/
theorem exists_ridge {r : ℝ} (hr : 0 < r) (m : ℕ) : ∃ A : (Fin m → Bool) → ℝ,
    IsRLM (fun w z => squaredLoss w (feature z) (feature z)) (fun w => r * ‖w‖ ^ 2) Set.univ A :=
  exists_isRLM_tikhonov isClosed_univ Set.univ_nonempty
    (fun _ => (differentiable_squaredLoss _ _).continuous.continuousOn)
    (fun w _ _ => squaredLoss_nonneg w _ _) hr m

/-- On `100` examples, ridge regression with `r = 1 / 10` has expected squared risk at most
`(1 + 1 / 2) (0 + 1 / 10) = 3 / 20` under every distribution, by the oracle inequality
(Corollary 13.10) at the predictor `1`. -/
example (D : Measure Bool) [IsProbabilityMeasure D] (A : (Fin 100 → Bool) → ℝ)
    (hA : IsRLM (fun w z => squaredLoss w (feature z) (feature z)) (fun w => 1 / 10 * ‖w‖ ^ 2)
      Set.univ A) :
    ∫ S, trueRisk (fun w z => squaredLoss w (feature z) (feature z)) D (A S)
      ∂(Measure.pi fun _ : Fin 100 => D) ≤ 3 / 20 := by
  obtain ⟨h1, h2⟩ := hA.integral_trueRisk_le_tikhonov_of_lipschitzWith_fderiv (β := 1)
    convex_univ (by norm_num) (fun z => convexOn_squaredLoss _ _)
    (fun z => differentiable_squaredLoss _ _)
    (fun z => lipschitzWith_fderiv_squaredLoss_of_norm_le_one (norm_feature_le_one z) _)
    (fun w z => squaredLoss_nonneg _ _ _) (by norm_num) D (by norm_num) Integrable.of_finite
    (fun _ => Integrable.of_finite) (Set.mem_univ 1) Integrable.of_finite
  have h0 : trueRisk (fun w z => squaredLoss w (feature z) (feature z)) D 1 = 0 := by
    simp only [trueRisk_def, squaredLoss_one_feature, integral_zero]
  rw [h0] at h2
  norm_num at h1 h2
  linarith

/-- [ShalevShwartzBenDavid2014, Theorem 13.1] at `ε = 1 / 10` and `B = 1`: on `15000` examples,
ridge regression with `r = 1 / 30` has expected squared risk within `1 / 10` of every predictor in
the unit ball. -/
example (D : Measure Bool) [IsProbabilityMeasure D] (A : (Fin 15000 → Bool) → ℝ)
    (hA : IsRLM (fun w z => squaredLoss w (feature z) (feature z)) (fun w => 1 / 30 * ‖w‖ ^ 2)
      Set.univ A) {w : ℝ} (hw : ‖w‖ ≤ 1) :
    ∫ S, trueRisk (fun w z => squaredLoss w (feature z) (feature z)) D (A S)
      ∂(Measure.pi fun _ : Fin 15000 => D) ≤
      trueRisk (fun w z => squaredLoss w (feature z) (feature z)) D w + 1 / 10 :=
  hA.integral_trueRisk_squaredLoss_le_add norm_feature_le_one (fun z => (abs_feature z).le)
    (by norm_num) (by norm_num) one_pos (by norm_num) (by norm_num) D Integrable.of_finite
    (fun _ => Integrable.of_finite) hw Integrable.of_finite

end CslibFrontierTests.SmoothLossMinimization
