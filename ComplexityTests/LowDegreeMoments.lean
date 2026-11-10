/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.LowDegreeMoments
import Complexity.Foundations.BooleanAnalysis.PolynomialThresholdWeight
import ComplexityTests.BooleanAnalysisPolynomialThreshold

/-!
# Moments of low-degree functions and the Gotsman–Linial Theorem

Instances for `Complexity.Foundations.Data.Finset.Holder`,
`Complexity.Foundations.BooleanAnalysis.LowDegreeMoments` and
`Complexity.Foundations.BooleanAnalysis.PolynomialThresholdWeight`. The coordinate sign `x ↦ x_0`
has degree one, mean zero and variance one, so Theorems 9.22 (also with `p = 1 / 2`, below the
book's range), 9.23 and 9.24 apply to it. The hypothesis `‖f‖_2 > 0` of the tail bound cannot be
dropped: for `f = 0` the event `|f| ≥ t ‖f‖_2` is everything. Khintchine's inequality applies to
`x_0 + x_1`, whose `L^2` norm is `√2`. The majority of three bits is a
linear threshold function, so the Gotsman–Linial Theorem bounds its weight of degree at most one.
-/

namespace ComplexityTests.LowDegreeMoments

open Finset Cslib Cslib.BitString
open scoped BigOperators

/-! ### The coordinate sign -/

/-- The coordinate sign `x ↦ x_0` has degree one. -/
theorem signVal_apply_mem_lowDegree :
    (fun x : Fin 2 → Bool => signVal (x 0)) ∈ lowDegree ℝ (Fin 2) 1 := by
  rw [show (fun z : Fin 2 → Bool => signVal (z 0)) = chi ℝ {0} from
    funext fun z => (chi_singleton 0 z).symm]
  exact chi_mem_lowDegree (F := ℝ) ({0} : Finset (Fin 2))

/-- The coordinate sign has mean `0` and variance `1`. -/
theorem expect_sub_expect_sq_signVal_apply :
    𝔼 x : Fin 2 → Bool, (signVal (x 0) - 𝔼 y : Fin 2 → Bool, signVal (y 0)) ^ 2 = 1 := by
  simp only [← chi_singleton, expect_chi, singleton_ne_empty, ite_false, sub_zero, sq,
    chi_mul_chi, symmDiff_self, bot_eq_empty, ite_true]

/-- The coordinate sign has `L^2` norm `1`. -/
theorem lpNorm_two_signVal_apply : lpNorm 2 (fun x : Fin 2 → Bool => signVal (x 0)) = 1 := by
  rw [lpNorm_two]
  simp only [sq, signVal_mul_self, Fintype.expect_const, Real.sqrt_one]

-- Theorem 9.22 with `p = 1` and with `p = 1 / 2`.
example : lpNorm 2 (fun x : Fin 2 → Bool => signVal (x 0)) ≤
    Real.exp 1 * lpNorm 1 (fun x : Fin 2 → Bool => signVal (x 0)) := by
  simpa only [Nat.cast_one] using lpNorm_two_le_exp_mul_lpNorm_one signVal_apply_mem_lowDegree

example : lpNorm 2 (fun x : Fin 2 → Bool => signVal (x 0)) ≤
    Real.exp (1 * (2 / (1 / 2) - 1)) * lpNorm (1 / 2) (fun x : Fin 2 → Bool => signVal (x 0)) := by
  simpa only [Nat.cast_one] using
    lpNorm_two_le_exp_mul_lpNorm (by norm_num) (by norm_num) signVal_apply_mem_lowDegree

-- Theorem 9.24: the coordinate sign exceeds its mean with probability at least `e ^ (-2) / 4`.
example : Real.exp (-(2 * 1)) / 4 ≤
    (dens {x : Fin 2 → Bool | 𝔼 y : Fin 2 → Bool, signVal (y 0) < signVal (x 0)} : ℝ) := by
  simpa only [Nat.cast_one] using exp_neg_two_mul_div_four_le_dens_lt signVal_apply_mem_lowDegree
    (by rw [expect_sub_expect_sq_signVal_apply]; norm_num)

-- Theorem 9.23 at the threshold `t = √(2 e)`.
example : (dens {x : Fin 2 → Bool | √(2 * Real.exp 1) *
      lpNorm 2 (fun x : Fin 2 → Bool => signVal (x 0)) ≤ |signVal (x 0)|} : ℝ) ≤
    Real.exp (-(1 / (2 * Real.exp 1) * √(2 * Real.exp 1) ^ (2 / 1 : ℝ))) := by
  simpa only [Nat.cast_one] using dens_le_exp_neg_mul_rpow signVal_apply_mem_lowDegree
    (by rw [lpNorm_two_signVal_apply]; exact one_pos) (by rw [pow_one])

/-! ### The tail bound needs `f ≢ 0` -/

-- For `f = 0`, the event of the tail bound is everything, while the bound is `e⁻¹ < 1`.
example : ¬ (dens {x : Fin 1 → Bool | √(2 * Real.exp 1) * lpNorm 2 (0 : (Fin 1 → Bool) → ℝ) ≤
      |(0 : (Fin 1 → Bool) → ℝ) x|} : ℝ) ≤
    Real.exp (-(1 / (2 * Real.exp 1) * √(2 * Real.exp 1) ^ (2 / 1 : ℝ))) := by
  have he : 0 < 2 * Real.exp 1 := by positivity
  have hrhs : 1 / (2 * Real.exp 1) * √(2 * Real.exp 1) ^ (2 / 1 : ℝ) = 1 := by
    rw [div_one, Real.rpow_two, Real.sq_sqrt he.le, one_div_mul_cancel he.ne']
  have hset : ({x : Fin 1 → Bool | √(2 * Real.exp 1) * lpNorm 2 (0 : (Fin 1 → Bool) → ℝ) ≤
      |(0 : (Fin 1 → Bool) → ℝ) x|} : Finset (Fin 1 → Bool)) = univ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, lpNorm_two, Pi.zero_apply, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Fintype.expect_const, Real.sqrt_zero,
      mul_zero, abs_zero, le_refl]
  rw [hrhs, hset, dens_univ, NNRat.cast_one, not_le]
  exact Real.exp_lt_one_iff.2 (by norm_num)

/-! ### Khintchine's inequality -/

-- `x_0 + x_1` has `‖·‖_2 = √2`, and Khintchine's inequality bounds its `L^4` and `L^1` norms.
example : lpNorm 2 (fun x : Fin 2 → Bool => ∑ i, (1 : ℝ) * signVal (x i)) = √2 := by
  rw [lpNorm_two_sum_mul_signVal]
  norm_num

example : lpNorm 4 (fun x : Fin 2 → Bool => ∑ i, (1 : ℝ) * signVal (x i)) ≤
    √(4 - 1) * √(∑ _i : Fin 2, (1 : ℝ) ^ 2) :=
  lpNorm_sum_mul_signVal_le (by norm_num) _

example : √(∑ _i : Fin 2, (1 : ℝ) ^ 2) ≤
    Real.exp (2 / 1 - 1) * lpNorm 1 (fun x : Fin 2 → Bool => ∑ i, (1 : ℝ) * signVal (x i)) :=
  sqrt_sum_sq_le_exp_mul_lpNorm one_pos one_le_two _

/-! ### The Gotsman–Linial Theorem -/

-- The majority of three bits has weight at least `e ^ (-2)` on the levels `0` and `1`.
example : Real.exp (-(2 * 1)) ≤
    ∑ S with #S ≤ 1, fourierCoeff (fun x => signVal (majority 3 x)) S ^ 2 := by
  simpa only [Nat.cast_one] using IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq
    BooleanAnalysisPolynomialThreshold.isPTF_one_majority_three

end ComplexityTests.LowDegreeMoments
