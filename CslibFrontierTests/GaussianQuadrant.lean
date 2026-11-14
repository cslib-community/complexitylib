/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import CslibFrontier.Foundations.Probability.Gaussian.Quadrant

/-! # Tests for the Gaussian quadrant probability function

Sheppard's value `Λ_{1/2}(1 / 2) = 1 / 3`, the independent and identical cases `ρ = 0` and
`ρ = 1`, the antipodal case `ρ = -1`, the book's form, symmetry, clamping, both reflection
formulas, the comparison with independence in both directions, instances of the Lipschitz bound,
the noise stability of a concrete halfspace, and the probability integral transform at a
non-unit variance. -/

public section

namespace CslibFrontierTests.GaussianQuadrant

open MeasureTheory ProbabilityTheory Real Set

/-- `arccos (1 / 2) = π / 3`. -/
theorem arccos_one_half : arccos (1 / 2) = π / 3 := by
  rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- Sheppard's value at `ρ = 1 / 2`: `Λ_{1/2}(1 / 2) = 1 / 2 - (π / 3) / (2π) = 1 / 3`. -/
example : gaussianQuadrant (1 / 2) (1 / 2) (1 / 2) = 1 / 3 := by
  rw [gaussianQuadrant_half_half (by norm_num [abs_of_pos]), arccos_one_half]
  field_simp
  ring

-- Independent Gaussians: `Λ_0(1 / 3, 3 / 4) = 1 / 4`.
example : gaussianQuadrant 0 (1 / 3) (3 / 4) = 1 / 4 := by
  rw [gaussianQuadrant_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- Identical Gaussians: `Λ_1(1 / 3, 3 / 4) = 1 / 3`.
example : gaussianQuadrant 1 (1 / 3) (3 / 4) = 1 / 3 := by
  rw [gaussianQuadrant_one (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- Antipodal Gaussians: `Λ_{-1}(1 / 3, 3 / 4) = 1 / 12` and `Λ_{-1}(1 / 3, 1 / 2) = 0`.
example : gaussianQuadrant (-1) (1 / 3) (3 / 4) = 1 / 12 := by
  rw [gaussianQuadrant_neg_one (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : gaussianQuadrant (-1) (1 / 3) (1 / 2) = 0 := by
  rw [gaussianQuadrant_neg_one (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- The book's form: `Λ_ρ(Φ 0, Φ 0)` is the probability that both coordinates are nonpositive,
-- here at `ρ = 0`, where it is `1 / 4`.
example : (correlatedGaussian 0).real {p | p.1 ≤ 0 ∧ p.2 ≤ 0} = 1 / 4 := by
  rw [← gaussianQuadrant_cdf_cdf, cdf_gaussianReal_zero_zero one_ne_zero,
    gaussianQuadrant_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- Symmetry and the value at `α = 1`: `Λ_{1/2}(3 / 4, 1) = Λ_{1/2}(1, 3 / 4) = 3 / 4`.
example : gaussianQuadrant (1 / 2) (3 / 4) 1 = 3 / 4 := by
  rw [gaussianQuadrant_comm (by norm_num [abs_of_pos]),
    gaussianQuadrant_one_left (by norm_num [abs_of_pos]) (by norm_num) (by norm_num)]

-- Arguments act as if clamped to `[0, 1]`: `Λ_ρ(2, β) = Λ_ρ(1, β) = β`.
example (ρ β : ℝ) (hρ : |ρ| ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    gaussianQuadrant ρ 2 β = β := by
  rw [gaussianQuadrant_eq_clamp_left, show max (min (2 : ℝ) 1) 0 = 1 by norm_num,
    gaussianQuadrant_one_left hρ hβ0 hβ1]

-- Reflection at `ρ = 1 / 2`: `Λ_{-1/2}(1 / 2) = 1 / 2 - Λ_{1/2}(1 / 2) = 1 / 6`.
example : gaussianQuadrant (-(1 / 2)) (1 / 2) (1 / 2) = 1 / 6 := by
  rw [gaussianQuadrant_neg (by norm_num [abs_of_pos]) (by norm_num) (by norm_num),
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, gaussianQuadrant_half_half
      (by norm_num [abs_of_pos]), arccos_one_half]
  field_simp
  ring

-- The second reflection: `Λ_{-1/2}(1 / 2) = 1 / 2 - Λ_{1/2}(1 / 2) = 1 / 6`, now reflecting `α`.
example : gaussianQuadrant (-(1 / 2)) (1 / 2) (1 / 2) = 1 / 6 := by
  rw [gaussianQuadrant_neg_eq_sub_one_sub_left (by norm_num [abs_of_pos]) _ (by norm_num)
      (by norm_num),
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, gaussianQuadrant_half_half
      (by norm_num [abs_of_pos]), arccos_one_half]
  field_simp
  ring

-- Positive correlation makes the lower quadrant at least as likely as under independence.
example : 1 / 4 ≤ gaussianQuadrant (1 / 2) (1 / 2) (1 / 2) := by
  have h := mul_le_gaussianQuadrant (ρ := 1 / 2) (α := 1 / 2) (β := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- Negative correlation makes it at most as likely: `Λ_{-1/2}(1 / 2) ≤ 1 / 4`.
example : gaussianQuadrant (-(1 / 2)) (1 / 2) (1 / 2) ≤ 1 / 4 := by
  have h := gaussianQuadrant_le_mul (ρ := -(1 / 2)) (α := 1 / 2) (β := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- The Lipschitz bound: moving `α` by `1 / 10` and `β` by `1 / 5` moves `Λ_ρ` by at most `3 / 10`.
example (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    |gaussianQuadrant ρ (1 / 2) (1 / 2) - gaussianQuadrant ρ (3 / 5) (3 / 10)| ≤ 3 / 10 := by
  refine (abs_gaussianQuadrant_sub_le hρ _ _ _ _).trans ?_
  norm_num [abs_of_neg, abs_of_pos]

-- The diagonal `Λ_ρ(α)` is `2`-Lipschitz.
example (ρ α α' : ℝ) (hρ : |ρ| ≤ 1) :
    dist (gaussianQuadrant ρ α α) (gaussianQuadrant ρ α' α') ≤ 2 * dist α α' := by
  exact_mod_cast (lipschitzWith_gaussianQuadrant_diag hρ).dist_le_mul α α'

-- The halfspace `z 0 + z 1 ≤ 0` has Gaussian volume `1 / 2`, so its indicator has noise
-- stability `Λ_ρ(1 / 2)`.
example (ρ : ℝ) :
    gaussianNoiseStability ρ ({z : Fin 2 → ℝ | (fun _ => 1) ⬝ᵥ z ≤ 0}.indicator 1) =
      gaussianQuadrant ρ (1 / 2) (1 / 2) := by
  have ha : (fun _ => 1 : Fin 2 → ℝ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  rw [gaussianNoiseStability_indicator_setOf_dotProduct_le ρ ha,
    measureReal_pi_gaussianReal_setOf_dotProduct_le ha, zero_div,
    cdf_gaussianReal_zero_zero one_ne_zero, one_div]

-- The probability integral transform at variance `4`: `Φ_{0,4}(x) ≤ 1 / 3` with probability
-- `1 / 3`.
example : (gaussianReal 0 4).real {x | cdf (gaussianReal 0 4) x ≤ 1 / 3} = 1 / 3 :=
  measureReal_setOf_cdf_gaussianReal_le 0 (by norm_num) (by norm_num) (by norm_num)

end CslibFrontierTests.GaussianQuadrant
