/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Foundations.Probability.Gaussian.ExpSq
import CslibFrontier.Probability.KWiseIndependent
import CslibFrontier.Probability.KWiseIndependent.TugOfWar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.Basic

/-!
# Rademacher sums

A **Rademacher sum** is `Y = ∑ i, a i * signVal (x i)` for a uniformly random `x : ι → Bool`,
that is, a weighted sum of independent uniform signs. This file proves the moment and
moment-generating-function bounds used for random sign projections.

* **Moments.** `𝔼 Y² = ∑ a²` and `𝔼 Y⁴ = 3 (∑ a²)² - 2 ∑ a⁴ ≤ 3 (∑ a²)²`. These are the tug-of-war
  moments of `CslibFrontier.Probability.KWiseIndependent.TugOfWar` for the fully independent family
  of
  all functions `ι → Bool`. The second moment also holds for vector coefficients in a real inner
  product space: `𝔼 ‖∑ i, signVal (x i) • v i‖² = ∑ i, ‖v i‖²`.
* **Exponential moments.** The coordinates factor, so `𝔼 exp (s Y) = ∏ i, cosh (s a i)`. Since
  `cosh u ≤ exp (u² / 2)`, `Y` is sub-Gaussian: `𝔼 exp (s Y) ≤ exp (s² ∑ a² / 2)`.
* **Gaussian comparison.** For `0 ≤ t` and `t ∑ a² < 1 / 2`,
  `𝔼 exp (t Y²) ≤ 1 / √(1 - 2 t ∑ a²)`, which is `𝔼 exp (t (∑ a²) Z²)` for a standard Gaussian `Z`.
  Linearize the square with the Gaussian moment generating function,
  `exp (t y²) = 𝔼 exp (√(2t) y Z)`. Exchange the two averages and apply the sub-Gaussian bound to
  the inner one. What remains is the chi-squared moment generating function
  (`ProbabilityTheory.integral_exp_mul_sq_gaussianReal`). This is the standard comparison of the
  squares of sub-Gaussian and Gaussian variables; Gupta's lecture notes [Gupta2023, §11.6.2,
  Lemma 11.9] apply it to Rademacher projection matrices. Achlioptas proves the same bound
  [Achlioptas2003, Lemma 5.2] by comparing the even moments of `Y` with those of a Gaussian. For
  Gaussian entries `Y` is itself Gaussian and the bound is an equality, the case of
  [Achlioptas2003, Lemma 4.1]. Dasgupta and Gupta use the same chi-squared moment generating
  function for projections onto a random subspace [DasguptaGupta2003, Lemma 2.2].

## Main results

* `Cslib.BitString.expect_sq_sum_mul_signVal`, `Cslib.BitString.expect_sum_mul_signVal_pow_four`,
  `Cslib.BitString.expect_sum_mul_signVal_pow_four_le`: the second and fourth moments.
* `Cslib.BitString.expect_norm_sum_signVal_smul_sq`: the second moment of a vector Rademacher sum.
* `Cslib.BitString.expect_exp_mul_sum_mul_signVal`: `𝔼 exp (s Y) = ∏ i, cosh (s a i)`.
* `Cslib.BitString.expect_exp_mul_sum_mul_signVal_le`: `𝔼 exp (s Y) ≤ exp (s² ∑ a² / 2)`.
* `Cslib.BitString.expect_exp_mul_sq_sum_mul_signVal_le`: `𝔼 exp (t Y²) ≤ 1 / √(1 - 2 t ∑ a²)`.

## References

* [D. Achlioptas, *Database-friendly random projections: Johnson–Lindenstrauss with binary
  coins*][Achlioptas2003]
* [S. Dasgupta, A. Gupta, *An elementary proof of a theorem of Johnson and
  Lindenstrauss*][DasguptaGupta2003]
* [A. Gupta, *Dimension Reduction and the JL Lemma*, CMU 15-850 lecture notes][Gupta2023]
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A uniform sign has mean zero. -/
theorem expect_bool_signVal : 𝔼 b : Bool, signVal b = 0 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, signVal_true, signVal_false]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
/-- A sign squares to one. -/
theorem signVal_sq (b : Bool) : signVal b ^ 2 = 1 := by
  rw [sq, signVal_mul_self]

/-- **The second moment of a Rademacher sum**: `𝔼 (∑ i, a i signVal (x i))² = ∑ i, a i ²`. -/
theorem expect_sq_sum_mul_signVal (a : ι → ℝ) :
    𝔼 x : ι → Bool, (∑ i, a i * signVal (x i)) ^ 2 = ∑ i, a i ^ 2 :=
  (Probability.isKWiseIndependentHash_id 2).expect_sq_sum_mul_sign signVal_sq expect_bool_signVal
    univ a

/-- **The second moment of a vector Rademacher sum**: for vectors `v i` in a real inner product
space, `𝔼 ‖∑ i, signVal (x i) • v i‖² = ∑ i, ‖v i‖²`, because distinct signs are uncorrelated. -/
theorem expect_norm_sum_signVal_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) : 𝔼 x : ι → Bool, ‖∑ i, signVal (x i) • v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have hpair (i j : ι) :
      𝔼 x : ι → Bool, signVal (x i) * signVal (x j) = if i = j then 1 else 0 := by
    split_ifs with hij
    · subst hij
      simp only [signVal_mul_self, Fintype.expect_const]
    · exact (Probability.isKWiseIndependentHash_id (X := ι) (Y := Bool) 2).expect_sign_mul_sign
        expect_bool_signVal hij
  have hexp (x : ι → Bool) : ‖∑ i, signVal (x i) • v i‖ ^ 2 =
      ∑ i, ∑ j, signVal (x i) * signVal (x j) * inner ℝ (v i) (v j) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [hexp]
  rw [expect_sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [expect_sum_comm]
  simp only [← expect_mul, hpair, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
    real_inner_self_eq_norm_sq]

/-- **The fourth moment of a Rademacher sum**:
`𝔼 (∑ i, a i signVal (x i))⁴ = 3 (∑ i, a i ²)² - 2 ∑ i, a i ⁴`. -/
theorem expect_sum_mul_signVal_pow_four (a : ι → ℝ) :
    𝔼 x : ι → Bool, (∑ i, a i * signVal (x i)) ^ 4 = 3 * (∑ i, a i ^ 2) ^ 2 - 2 * ∑ i, a i ^ 4 :=
  (Probability.isKWiseIndependentHash_id 4).expect_sum_mul_sign_pow_four signVal_sq
    expect_bool_signVal univ a

/-- The fourth moment of a Rademacher sum is at most that of a Gaussian with the same variance:
`𝔼 (∑ i, a i signVal (x i))⁴ ≤ 3 (∑ i, a i ²)²`. -/
theorem expect_sum_mul_signVal_pow_four_le (a : ι → ℝ) :
    𝔼 x : ι → Bool, (∑ i, a i * signVal (x i)) ^ 4 ≤ 3 * (∑ i, a i ^ 2) ^ 2 := by
  rw [expect_sum_mul_signVal_pow_four]
  have : 0 ≤ ∑ i, a i ^ 4 := sum_nonneg fun i _ => by positivity
  linarith

/-- **The moment generating function of a Rademacher sum**:
`𝔼 exp (s ∑ i, a i signVal (x i)) = ∏ i, cosh (s a i)`. -/
theorem expect_exp_mul_sum_mul_signVal (a : ι → ℝ) (s : ℝ) :
    𝔼 x : ι → Bool, exp (s * ∑ i, a i * signVal (x i)) = ∏ i, cosh (s * a i) := by
  have h (x : ι → Bool) :
      exp (s * ∑ i, a i * signVal (x i)) = ∏ i, exp (s * a i * signVal (x i)) := by
    rw [mul_sum, exp_sum]
    simp only [mul_assoc]
  simp only [h]
  refine ((Probability.isKWiseIndependentHash_id (Fintype.card ι)).expect_prod (T := univ)
    card_univ.le fun i b => exp (s * a i * signVal b)).trans (prod_congr rfl fun i _ => ?_)
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, signVal_true, signVal_false, cosh_eq,
    Fintype.card_bool]
  simp only [mul_neg, mul_one, Nat.cast_ofNat]
  ring

/-- **Rademacher sums are sub-Gaussian**:
`𝔼 exp (s ∑ i, a i signVal (x i)) ≤ exp (s² ∑ i, a i ² / 2)`. -/
theorem expect_exp_mul_sum_mul_signVal_le (a : ι → ℝ) (s : ℝ) :
    𝔼 x : ι → Bool, exp (s * ∑ i, a i * signVal (x i)) ≤ exp (s ^ 2 * (∑ i, a i ^ 2) / 2) := by
  rw [expect_exp_mul_sum_mul_signVal, mul_sum, sum_div, exp_sum]
  refine prod_le_prod₀ (fun i _ => (cosh_pos _).le) fun i _ => ?_
  calc cosh (s * a i) ≤ exp ((s * a i) ^ 2 / 2) := cosh_le_exp_half_sq _
    _ = exp (s ^ 2 * a i ^ 2 / 2) := by rw [mul_pow]

open MeasureTheory ProbabilityTheory in
/-- **Gaussian comparison for the square of a Rademacher sum**: for `0 ≤ t` and
`t ∑ i, a i ² < 1 / 2`, `𝔼 exp (t (∑ i, a i signVal (x i))²) ≤ 1 / √(1 - 2 t ∑ i, a i ²)`. The
right side is `𝔼 exp (t (∑ i, a i ²) Z²)` for a standard Gaussian `Z`. -/
theorem expect_exp_mul_sq_sum_mul_signVal_le (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hta : t * ∑ i, a i ^ 2 < 1 / 2) :
    𝔼 x : ι → Bool, exp (t * (∑ i, a i * signVal (x i)) ^ 2) ≤
      (√(1 - 2 * (t * ∑ i, a i ^ 2)))⁻¹ := by
  set Y : (ι → Bool) → ℝ := fun x => ∑ i, a i * signVal (x i)
  set γ := gaussianReal 0 1
  have h2t : (0 : ℝ) ≤ 2 * t := by linarith
  have hta' : (t * ∑ i, a i ^ 2) * ((1 : NNReal) : ℝ) < 1 / 2 := by
    rwa [NNReal.coe_one, mul_one]
  -- Linearize the square with the Gaussian moment generating function.
  have hlin (y : ℝ) : exp (t * y ^ 2) = ∫ z, exp (√(2 * t) * y * z) ∂γ := by
    have := mgf_gaussianReal (μ := 0) (v := 1) (p := γ) (X := id) (by simp [γ]) (√(2 * t) * y)
    rw [mgf] at this
    simp only [id, zero_mul, zero_add, NNReal.coe_one, one_mul, mul_pow,
      Real.sq_sqrt h2t] at this
    rw [this]
    congr 1
    ring
  calc 𝔼 x, exp (t * Y x ^ 2)
      = 𝔼 x, ∫ z, exp (√(2 * t) * Y x * z) ∂γ := by simp only [hlin]
    _ = ∫ z, 𝔼 x, exp (√(2 * t) * Y x * z) ∂γ := by
        simp only [Fintype.expect_eq_sum_div_card]
        rw [integral_div, integral_finsetSum _ fun x _ => integrable_exp_mul_gaussianReal _]
    _ ≤ ∫ z, exp ((t * ∑ i, a i ^ 2) * z ^ 2) ∂γ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => ?_)
          (integrable_exp_mul_sq_gaussianReal hta') (ae_of_all _ fun z => ?_)
        · exact expect_nonneg fun x _ => (exp_pos _).le
        · calc 𝔼 x, exp (√(2 * t) * Y x * z) = 𝔼 x, exp ((√(2 * t) * z) * Y x) := by
                simp only [mul_right_comm]
            _ ≤ _ := expect_exp_mul_sum_mul_signVal_le a _
            _ = _ := by
                rw [mul_pow, Real.sq_sqrt h2t]
                ring_nf
    _ = (√(1 - 2 * (t * ∑ i, a i ^ 2)))⁻¹ := by
        rw [integral_exp_mul_sq_gaussianReal hta', NNReal.coe_one, mul_one]

end Cslib.BitString
