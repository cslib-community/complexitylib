/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.Rademacher.Linear
public import CslibFrontier.MachineLearning.PACLearning.Halfspaces
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Checks for linear predictors and halfspaces

Exercises `CslibFrontier.MachineLearning.Rademacher.Linear` and
`CslibFrontier.MachineLearning.PACLearning.Halfspaces`:

* **A two-point sample in the plane:** for the points `3 e₀` and `4 e₁` of
  `EuclideanSpace ℝ (Fin 2)` and `B = 1`, the trace bound gives empirical Rademacher complexity at
  most `5 / 2`, below the uniform bound `4 / √2 = 2 √2` from `R = 4`.
* **A nonvacuous margin bound:** for unit features, `B = 1`, `ρ = 1 / 2` and `m = 10000`, the
  complexity term of `linearPredictors_margin_bound` is `1 / 25`.
* **Halfspaces:** homogeneous halfspaces in `ℝ²` have VC dimension `2` and affine ones `3`; the
  standard basis is shattered, two points on one open ray are not, and no three points of the plane
  are shattered by homogeneous halfspaces.
-/

public section

namespace CslibFrontierTests.LinearPredictors

open Cslib.MachineLearning Cslib.MachineLearning.PACLearning Cslib.BitString

/-! ### A two-point sample in the plane -/

/-- The sample `(3 e₀, 4 e₁)` in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def planeSample : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  ![EuclideanSpace.single 0 3, EuclideanSpace.single 1 4]

theorem sum_norm_sq_planeSample : ∑ i, ‖planeSample i‖ ^ 2 = 25 := by
  norm_num [planeSample, Fin.sum_univ_two, PiLp.norm_single]

/-- The trace bound: complexity at most `5 / 2`. -/
theorem empiricalRademacherComplexity_planeSample_le :
    empiricalRademacherComplexity (linearPredictors id 1) planeSample ≤ 5 / 2 := by
  refine (empiricalRademacherComplexity_linearPredictors_le_sqrt id zero_le_one
    planeSample).trans_eq ?_
  simp only [id, sum_norm_sq_planeSample]
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The uniform bound with `R = 4` is `4 / √2`, which exceeds the trace bound `5 / 2`. -/
theorem empiricalRademacherComplexity_planeSample_le_uniform :
    empiricalRademacherComplexity (linearPredictors id 1) planeSample ≤ 1 * 4 / √2 := by
  have h := empiricalRademacherComplexity_linearPredictors_le id (B := 1) (R := 4) zero_le_one
    planeSample fun i => by fin_cases i <;> norm_num [planeSample, PiLp.norm_single]
  simpa using h

theorem five_div_two_lt_four_div_sqrt_two : (5 / 2 : ℝ) < 1 * 4 / √2 := by
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [one_mul, lt_div_iff₀ h2]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
    show √2 < 8 / 5 by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num]

/-! ### A nonvacuous margin bound -/

/-- Unit features on `Bool`: `b ↦ signVal b • e₀`. -/
noncomputable def unitFeature (b : Bool) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 (signVal b)

theorem norm_unitFeature_le (b : Bool) : ‖unitFeature b‖ ≤ 1 := by
  simp [unitFeature, PiLp.norm_single]

/-- The complexity term `2 B R / (ρ √m)` at `B = R = 1`, `ρ = 1 / 2`, `m = 10000`. -/
theorem margin_gap_eq : 2 * 1 * 1 / ((1 / 2 : ℝ) * √((10000 : ℕ) : ℝ)) = 1 / 25 := by
  rw [show ((10000 : ℕ) : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The margin bound for unit features with `B = 1`, `ρ = 1 / 2` and `m = 10000`: with
probability at least `1 - 1 / 20`, every `‖w‖ ≤ 1` has error at most its empirical margin loss
plus `1 / 25 + √(log 20 / 20000)`. -/
theorem unitFeature_margin_bound (D : PMF (Bool × Bool)) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 10000 => D).toOuterMeasure
      {S | ∃ w : EuclideanSpace ℝ (Fin 1), ‖w‖ ≤ 1 ∧
        empiricalMarginLoss (1 / 2) (fun z => inner ℝ w (unitFeature z)) S + 1 / 25 +
          √(Real.log (1 / (1 / 20)) / (2 * ((10000 : ℕ) : ℝ))) <
          (D.toOuterMeasure {p | signVal p.2 * inner ℝ w (unitFeature p.1) ≤ 0}).toReal}).toReal ≤
      1 / 20 := by
  have h := linearPredictors_margin_bound D (by norm_num : 0 < 10000) unitFeature zero_le_one
    norm_unitFeature_le (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 20)
  rwa [margin_gap_eq] at h

/-! ### Halfspaces -/

example : vcDim (homogeneousHalfspaces 2) = 2 := vcDim_homogeneousHalfspaces 2

example : vcDim (affineHalfspaces 2) = 3 := vcDim_affineHalfspaces 2

/-- Homogeneous halfspaces shatter the standard basis of `ℝ²`. -/
theorem setShatters_basis :
    SetShatters (homogeneousHalfspaces 2) (Set.range fun k : Fin 2 => Pi.single k (1 : ℝ)) :=
  homogeneousHalfspaces_eq_positivityClass ▸
    setShatters_positivityClass_range (homogeneousForm 2) _ fun t =>
      ⟨t, fun i => by simp [dotProduct_single]⟩

/-- Two points on one open ray are not shattered by homogeneous halfspaces: a halfspace containing
`(2, 0)` also contains `(1, 0)`. -/
theorem not_setShatters_ray :
    ¬ SetShatters (homogeneousHalfspaces 2) {![1, 0], ![2, 0]} := by
  intro h
  obtain ⟨c, hc, hcW⟩ := h {![2, 0]} (by simp)
  obtain ⟨w, rfl⟩ := mem_homogeneousHalfspaces.1 hc
  have h2 := congrArg (fun s => (![2, 0] : Fin 2 → ℝ) ∈ s) hcW
  have h1 := congrArg (fun s => (![1, 0] : Fin 2 → ℝ) ∈ s) hcW
  simp only [dotProduct, Fin.sum_univ_two, Fin.isValue, Set.mem_inter_iff, Set.mem_preimage,
    Matrix.cons_val_zero, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero,
    Set.mem_singleton_iff, decide_eq_true_eq, Set.mem_insert_iff, Matrix.vecCons_inj,
    OfNat.one_ne_ofNat, and_true, or_false, eq_iff_iff, iff_false, not_lt, Nat.ofNat_pos,
    mul_pos_iff_of_pos_right, OfNat.ofNat_ne_one, or_true, iff_true] at h1 h2
  linarith

/-- No three points of the plane are shattered by homogeneous halfspaces. -/
theorem not_setShatters_three {W : Finset (Fin 2 → ℝ)} (hW : W.card = 3) :
    ¬ SetShatters (homogeneousHalfspaces 2) ↑W := fun h => by
  rw [homogeneousHalfspaces_eq_positivityClass] at h
  have := card_le_finrank_of_setShatters_positivityClass (homogeneousForm 2) h
  rw [hW, Module.finrank_fin_fun] at this
  omega

end CslibFrontierTests.LinearPredictors
