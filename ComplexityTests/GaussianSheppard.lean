/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import Complexity.Foundations.Probability.Gaussian.Sheppard

/-! # Tests for Sheppard's formula

A non-right angle with vectors of unequal norm, orthogonal vectors, opposite vectors, and the
complementary identity for `v` and `-v`. -/

namespace ComplexityTests.GaussianSheppard

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Interval

local notation "e" i => (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin 2))

/-- `e₀` and `e₀ + e₁` are at angle `π / 4` and have unequal norms: the projections differ in
sign with probability `1/4`. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 2))).real
    {x | (0 : ℝ) ∈ Ι ⟪e 0, x⟫ ⟪(e 0) + (e 1), x⟫} = 1 / 4 := by
  have hn : ‖(e 0) + (e 1)‖ = √2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    norm_num
  have hangle : InnerProductGeometry.angle (e 0) ((e 0) + (e 1)) = π / 4 := by
    rw [InnerProductGeometry.angle, hn, inner_add_right, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left, ← arccos_cos (by positivity : 0 ≤ π / 4)
      (by linarith [pi_pos]), cos_pi_div_four]
    congr 1
    simp only [Fin.isValue, conj_trivial, PiLp.single_eq_same, mul_one, ne_eq, zero_ne_one,
      not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, add_zero, PiLp.norm_single, norm_one,
      one_mul, one_div]
    rw [eq_div_iff two_ne_zero, inv_mul_eq_div, div_sqrt]
  rw [measureReal_stdGaussian_zero_mem_uIoc_eq_angle (by simp)
    (norm_ne_zero_iff.1 (by rw [hn]; positivity)), hangle]
  field_simp

/-- Orthogonal unit vectors, in the correlation form: probability `arccos 0 / π = 1/2`. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 2))).real
    {x | (0 : ℝ) ∈ Ι ⟪e 0, x⟫ ⟪e 1, x⟫} = 1 / 2 := by
  rw [measureReal_stdGaussian_zero_mem_uIoc_eq_arccos (by simp) (by simp),
    EuclideanSpace.inner_single_left]
  simp [arccos_zero]
  field_simp

/-- Opposite vectors: the projections differ in sign with probability `1`. -/
example (u : EuclideanSpace ℝ (Fin 3)) (hu : u ≠ 0) :
    (stdGaussian (EuclideanSpace ℝ (Fin 3))).real {x | (0 : ℝ) ∈ Ι ⟪u, x⟫ ⟪-u, x⟫} = 1 := by
  rw [measureReal_stdGaussian_zero_mem_uIoc_eq_angle hu (neg_ne_zero.2 hu),
    InnerProductGeometry.angle_self_neg_of_ne_zero hu, div_self pi_ne_zero]

/-- Replacing `v` by `-v` turns "differ in sign" into "agree in sign" up to a null set. -/
example (u v : EuclideanSpace ℝ (Fin 3)) (hu : u ≠ 0) (hv : v ≠ 0) :
    (stdGaussian (EuclideanSpace ℝ (Fin 3))).real {x | (0 : ℝ) ∈ Ι ⟪u, x⟫ ⟪v, x⟫} +
      (stdGaussian (EuclideanSpace ℝ (Fin 3))).real {x | (0 : ℝ) ∈ Ι ⟪u, x⟫ ⟪-v, x⟫} = 1 := by
  rw [measureReal_stdGaussian_zero_mem_uIoc_eq_angle hu hv,
    measureReal_stdGaussian_zero_mem_uIoc_eq_angle hu (neg_ne_zero.2 hv),
    InnerProductGeometry.angle_neg_right]
  field_simp
  ring

end ComplexityTests.GaussianSheppard
