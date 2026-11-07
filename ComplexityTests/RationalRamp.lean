/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Analysis.SpecialFunctions.RationalRamp
import Mathlib.Tactic.NormNum

/-!
# Tests for the rational correction ramp

Exact rational evaluations exercise the transition and large inputs. The real examples use the
proved defect, one-Lipschitz bound and the nontrivial fourth-root rescaling constant.
-/

namespace ComplexityTests.RationalRamp

open Cslib

example : rationalRamp4Unit (1 : ℚ) = 1 / 8 := by
  norm_num [rationalRamp4Unit]

example : rationalRamp4Unit (10 : ℚ) = 10000 / 1331 := by
  norm_num [rationalRamp4Unit]

example : rationalRamp4 (1 : ℚ) 2 9 = 512 / 125 := by
  norm_num [rationalRamp4, rationalRamp4Unit]

example : rationalRamp4 (1 : ℚ) 2 (-5) = 0 ∧ rationalRamp4 (1 : ℚ) 2 1 = 0 := by
  norm_num [rationalRamp4, rationalRamp4Unit]

example : rationalRamp4 (1 : ℝ) 2 9 = 512 / 125 := by
  have h : rationalRamp4 (1 : ℚ) 2 9 = 512 / 125 := by
    norm_num [rationalRamp4, rationalRamp4Unit]
  have hc := rationalRamp4_ratCast (1 : ℚ) 2 9
  rw [h] at hc
  norm_num at hc ⊢
  exact hc

-- The upper and lower bounds are uniform on the whole real line.
example (t : ℝ) : t - 7 ≤ rationalRamp4 1 2 t ∧ rationalRamp4 1 2 t ≤ max (t - 1) 0 := by
  constructor
  · have h := le_rationalRamp4 (by norm_num : (0 : ℝ) < 2) 1 t
    norm_num at h
    exact (sub_le_iff_le_add).mpr h
  · exact rationalRamp4_le (by norm_num) 1 t

example (x y : ℝ) : |rationalRamp4 1 2 x - rationalRamp4 1 2 y| ≤ |x - y| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (lipschitzWith_rationalRamp4 (by norm_num : (0 : ℝ) < 2) 1).dist_le_mul x y

-- A width of `1/16` gives the explicit fourth-root Lipschitz constant `8`.
example (θ x y : ℝ) :
    |rationalRamp4 θ (1 / 16) x ^ (4⁻¹ : ℝ) -
      rationalRamp4 θ (1 / 16) y ^ (4⁻¹ : ℝ)| ≤ 8 * |x - y| := by
  have h := (lipschitzWith_rationalRamp4_root (by norm_num : (0 : ℝ) < 1 / 16) θ).dist_le_mul x y
  have hr : (1 / 16 : ℝ) ^ (4⁻¹ : ℝ) = 1 / 2 := by
    rw [show (1 / 16 : ℝ) = (1 / 2) ^ 4 by norm_num]
    convert Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (4 : ℕ) ≠ 0) using 1
  rw [hr] at h
  norm_num [Real.dist_eq] at h ⊢
  exact h

end ComplexityTests.RationalRamp
