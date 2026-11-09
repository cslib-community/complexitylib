/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.BitString.Rademacher
import CslibFrontier.Probability.KWiseIndependent
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Order.Interval.Finset.Fin

/-!
# The Johnson–Lindenstrauss lemma for random sign matrices

Fix `n` points of a finite-dimensional Euclidean space `EuclideanSpace ℝ ι`. A uniformly random
`k × ι` matrix of independent signs `±1`, scaled by `1 / √k`, keeps every squared pairwise distance
within a factor `1 ± ε`, with probability at least `1 - n^(-β)`, once
`k ≥ (4 + 2β) / (ε² / 2 - ε³ / 3) · log n`. This is Achlioptas's theorem for the `±1` distribution
[Achlioptas2003, Theorem 1.1]. The union bound fails with probability at most
`n (n - 1) exp (-(k / 2) (ε² / 2 - ε³ / 3))`, and `n (n - 1) < n²`, so the threshold for `β = 0`
already gives a positive probability of success. This is the Johnson–Lindenstrauss lemma
[JohnsonLindenstrauss1984] with the constant of Dasgupta and Gupta [DasguptaGupta2003, Theorem 2.1]:
`n` points embed into dimension `k ≥ 4 log n / (ε² / 2 - ε³ / 3)` with distortion `1 ± ε`. For
`ε ≤ 1`, `k ≥ 24 log n / ε²` suffices.

Achlioptas states the theorem for every `ε > 0`. Here `ε < 3 / 2`, which makes `ε² / 2 - ε³ / 3`
positive, and some restriction is needed. For `ε = 2`, `β = 10` and the two points `0` and
`(1, 1, 1, 1)` the threshold is negative, so `k = 1` meets it. But the single row maps
`(1, 1, 1, 1)` to the squared norm `16 > (1 + ε) · 4` with probability `1 / 8 > 2^(-10)`.

The seed is `b : Fin k → ι → Bool`, drawn uniformly. `signProjection b` is the linear map with
matrix `(1 / √k) signVal (b j i)`. Probabilities are densities of finsets of seeds.

## Proof

For a fixed vector `x` with `S = ‖x‖²`, the rows give independent Rademacher sums
`Y_j = ∑ i, x i signVal (b j i)`, each with `𝔼 Y_j² = S`, and `k ‖signProjection b x‖² = ∑ j, Y_j²`.

* **Upper tail.** By Markov's inequality applied to `exp (t ∑ Y_j²)`, independence of the rows and
  the Gaussian comparison `𝔼 exp (t Y²) ≤ 1 / √(1 - 2tS)`
  (`Cslib.BitString.expect_exp_mul_sq_sum_mul_signVal_le`),
  `Pr[∑ Y_j² > k (1 + ε) S] ≤ ((1 - 2tS)^(-1/2) exp (-t (1 + ε) S))^k`. The choice
  `tS = ε / (2 (1 + ε))` gives `(√(1 + ε) exp (-ε / 2))^k`, and
  `1 + ε ≤ exp (ε - ε² / 2 + ε³ / 3)` bounds this by `exp (-(k / 2) (ε² / 2 - ε³ / 3))`.
* **Lower tail.** Markov's inequality applied to `exp (-t ∑ Y_j²)`, with
  `exp (-u) ≤ 1 - u + u² / 2` and `𝔼 Y⁴ ≤ 3 S²`, gives
  `Pr[∑ Y_j² < k (1 - ε) S] ≤ ((1 - tS + 3 (tS)² / 2) exp (tS (1 - ε)))^k`. The same choice of `tS`
  gives the same bound for `ε ≤ 1`, by an explicit polynomial inequality. For `ε > 1` the event is
  empty.
* **Union bound.** The `n (n - 1) / 2` pairs fail with probability at most `2 e` each, where
  `e = exp (-(k / 2) (ε² / 2 - ε³ / 3))`. The hypothesis on `k` gives `e ≤ n^(-(2 + β))`.

Achlioptas compares the even moments of `Y_j` with those of a Gaussian
[Achlioptas2003, Lemma 5.2]. Here the comparison goes through the moment generating function:
`Y_j` is sub-Gaussian, so `exp (t Y_j²)` is dominated by `exp (t S Z²)` for a standard Gaussian
`Z`. This is the standard sub-Gaussian comparison [Gupta2023, Lemma 11.9]. Both arguments give the
same per-vector bound [Achlioptas2003, Lemma 5.1].

## Main definitions

* `Cslib.Probability.signProjection`: the scaled random sign projection
  `EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin k)`.

## Main results

* `Cslib.Probability.dens_lt_norm_signProjection_sq_le`,
  `Cslib.Probability.dens_norm_signProjection_sq_lt_le`: each tail for a fixed vector is at most
  `exp (-(k / 2) (ε² / 2 - ε³ / 3))`.
* `Cslib.Probability.dens_lt_abs_norm_signProjection_sq_sub_le`: the two-sided bound
  `2 exp (-(k / 2) (ε² / 2 - ε³ / 3))`.
* `Cslib.Probability.one_sub_le_dens_forall_norm_signProjection_sq_mem_Icc`: all pairwise squared
  distances among `n` points are preserved with probability at least
  `1 - n (n - 1) exp (-(k / 2) (ε² / 2 - ε³ / 3))`.
* `Cslib.Probability.one_sub_rpow_le_dens_forall_norm_signProjection_sq_mem_Icc`: Achlioptas's
  theorem, with probability at least `1 - n^(-β)`.
* `Cslib.Probability.exists_signProjection_forall_norm_sq_mem_Icc`,
  `Cslib.Probability.exists_linearMap_forall_norm_sq_mem_Icc`: the Johnson–Lindenstrauss lemma.

## References

* [D. Achlioptas, *Database-friendly random projections: Johnson–Lindenstrauss with binary
  coins*][Achlioptas2003]
* [S. Dasgupta, A. Gupta, *An elementary proof of a theorem of Johnson and
  Lindenstrauss*][DasguptaGupta2003]
* [A. Gupta, *Dimension Reduction and the JL Lemma*, CMU 15-850 lecture notes][Gupta2023]
* [W. B. Johnson, J. Lindenstrauss, *Extensions of Lipschitz mappings into a Hilbert
  space*][JohnsonLindenstrauss1984]
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Probability

open BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Scalar inequalities -/

/-- The per-row factor of the upper tail: `√(1 + ε) exp (-ε / 2) ≤ exp (-(ε² / 4 - ε³ / 6))`. -/
private theorem sqrt_one_add_mul_exp_neg_le {ε : ℝ} (hε : 0 ≤ ε) :
    √(1 + ε) * exp (-(ε / 2)) ≤ exp (-(ε ^ 2 / 4 - ε ^ 3 / 6)) := by
  set z := ε - ε ^ 2 / 2 + ε ^ 3 / 3
  have hsq : √(1 + ε) ≤ exp (z / 2) := by
    rw [Real.sqrt_le_left (exp_pos _).le, ← exp_nat_mul]
    convert one_add_le_exp_sub_sq_div_two_add_cube_div_three hε using 2
    push_cast
    ring
  calc √(1 + ε) * exp (-(ε / 2)) ≤ exp (z / 2) * exp (-(ε / 2)) :=
        mul_le_mul_of_nonneg_right hsq (exp_pos _).le
    _ = exp (-(ε ^ 2 / 4 - ε ^ 3 / 6)) := by
        rw [← exp_add]
        congr 1
        simp only [z]
        ring

/-- The per-row factor of the lower tail: with `τ = ε / (2 (1 + ε))` and `0 ≤ ε ≤ 1`,
`(1 - τ + 3 τ² / 2) exp (τ (1 - ε)) ≤ exp (-(ε² / 4 - ε³ / 6))`. Multiplying by `exp x`, where
`x = τ (1 - ε) + ε² / 4 - ε³ / 6 ∈ [0, 1]`, and bounding `exp x` by its cubic Taylor polynomial
with remainder reduces this to a polynomial in `ε` with nonnegative value on `[0, 1]`. -/
private theorem lower_tail_factor_le {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε / (2 * (1 + ε)) + 3 / 2 * (ε / (2 * (1 + ε))) ^ 2) *
      exp (ε / (2 * (1 + ε)) * (1 - ε)) ≤ exp (-(ε ^ 2 / 4 - ε ^ 3 / 6)) := by
  set τ := ε / (2 * (1 + ε)) with hτdef
  set x := τ * (1 - ε) + (ε ^ 2 / 4 - ε ^ 3 / 6) with hx
  have hτ0 : 0 ≤ τ := by positivity
  have hτ : τ ≤ 1 / 4 := by
    rw [hτdef, div_le_iff₀ (by positivity)]
    linarith
  have hx0 : 0 ≤ x := by
    have : 0 ≤ ε ^ 2 / 4 - ε ^ 3 / 6 := by nlinarith [sq_nonneg ε]
    have : 0 ≤ τ * (1 - ε) := mul_nonneg hτ0 (by linarith)
    linarith
  have hx1 : x ≤ 1 := by
    have : τ * (1 - ε) ≤ 1 / 4 := by nlinarith
    have : ε ^ 2 / 4 - ε ^ 3 / 6 ≤ 1 / 4 := by nlinarith [sq_nonneg ε]
    linarith
  have hb := Real.exp_bound' hx0 hx1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have hA : 0 ≤ 1 - τ + 3 / 2 * τ ^ 2 := by nlinarith
  rw [show -(ε ^ 2 / 4 - ε ^ 3 / 6) = τ * (1 - ε) - x by rw [hx]; ring, Real.exp_sub,
    le_div_iff₀ (exp_pos _), mul_comm (1 - τ + 3 / 2 * τ ^ 2) (exp _), mul_assoc]
  refine mul_le_of_le_one_right (exp_pos _).le ((mul_le_mul_of_nonneg_left hb hA).trans ?_)
  -- `1 - A (1 + x + x² / 2 + 2 x³ / 9) = P / (2 (1 + ε))⁵` for an explicit polynomial `P`.
  set P : ℝ := 4/9 * ε^3 + 55/6 * ε^4 + 455/18 * ε^5 + 241/8 * ε^6 + 3851/216 * ε^7 +
    181/36 * ε^8 - 911/486 * ε^9 - 49/72 * ε^10 - 1111/1944 * ε^11 + 107/972 * ε^12 +
    1/162 * ε^13 + 7/243 * ε^14 with hP
  have hD : 0 < 2 * (1 + ε) := by positivity
  have hid : 1 - (1 - τ + 3 / 2 * τ ^ 2) * (1 + x + x ^ 2 / 2 + x ^ 3 * 4 / 18) =
      P / (2 * (1 + ε)) ^ 5 := by
    simp only [hx, hP, hτdef]
    field_simp
    ring
  have hPnn : 0 ≤ P := by
    have e9 : ε ^ 9 ≤ ε ^ 8 := pow_le_pow_of_le_one hε hε1 (by norm_num)
    have e10 : ε ^ 10 ≤ ε ^ 8 := pow_le_pow_of_le_one hε hε1 (by norm_num)
    have e11 : ε ^ 11 ≤ ε ^ 8 := pow_le_pow_of_le_one hε hε1 (by norm_num)
    have := pow_nonneg hε 3
    have := pow_nonneg hε 4
    have := pow_nonneg hε 5
    have := pow_nonneg hε 6
    have := pow_nonneg hε 7
    have := pow_nonneg hε 8
    have := pow_nonneg hε 12
    have := pow_nonneg hε 13
    have := pow_nonneg hε 14
    rw [hP]
    linarith
  have := div_nonneg hPnn (pow_nonneg hD.le 5)
  linarith

/-! ### Tails of sums of squared Rademacher sums -/

omit [DecidableEq ι] in
/-- A Rademacher sum with zero weights vanishes. -/
private theorem sum_mul_signVal_eq_zero {a : ι → ℝ} (h : ∑ i, a i ^ 2 = 0) (x : ι → Bool) :
    ∑ i, a i * signVal (x i) = 0 := by
  have ha (i : ι) : a i = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.1 <|
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (a i)).1 h i (mem_univ _)
  simp only [ha, zero_mul, sum_const_zero]

/-- The rows of a uniformly random sign matrix are independent. -/
private theorem expect_prod_row {k : ℕ} (g : (ι → Bool) → ℝ) :
    𝔼 b : Fin k → ι → Bool, ∏ j, g (b j) = (𝔼 x : ι → Bool, g x) ^ k := by
  refine ((isKWiseIndependentHash_id (X := Fin k) (Y := ι → Bool) k).expect_prod
    (T := univ) (by simp) fun _ x => g x).trans ?_
  rw [prod_const, card_univ, Fintype.card_fin]

/-- **Upper tail**: for `k` independent Rademacher sums `Y_j = ∑ i, a i signVal (b j i)` and
`0 ≤ ε`, `Pr[k (1 + ε) ∑ a² < ∑ j, Y_j²] ≤ exp (-(k / 2) (ε² / 2 - ε³ / 3))`. -/
theorem dens_mul_lt_sum_sq_sum_mul_signVal_le (a : ι → ℝ) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (dens ({b | k * (1 + ε) * ∑ i, a i ^ 2 < ∑ j, (∑ i, a i * signVal (b j i)) ^ 2} :
        Finset (Fin k → ι → Bool)) : ℝ) ≤
      exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  rcases (sum_nonneg fun i (_ : i ∈ univ) => sq_nonneg (a i)).eq_or_lt with hS | hS
  · rw [filter_false_of_mem fun b _ => ?_, dens_empty, NNRat.cast_zero]
    · positivity
    simp only [← hS, sum_mul_signVal_eq_zero hS.symm, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sum_const_zero, lt_irrefl]
  set S := ∑ i, a i ^ 2 with hSdef
  set τ := ε / (2 * (1 + ε)) with hτdef
  set t := τ / S with htdef
  have ht0 : 0 ≤ t := by positivity
  have htS : t * S = τ := by
    rw [htdef]
    field_simp
  have hτ : τ < 1 / 2 := by
    rw [hτdef, div_lt_iff₀ (by positivity)]
    linarith
  set f : (Fin k → ι → Bool) → ℝ := fun b => exp (t * ∑ j, (∑ i, a i * signVal (b j i)) ^ 2)
  have hsub : ({b | k * (1 + ε) * S < ∑ j, (∑ i, a i * signVal (b j i)) ^ 2} :
      Finset (Fin k → ι → Bool)) ⊆ ({b | exp (t * (k * (1 + ε) * S)) ≤ f b} : Finset _) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hb.le ht0)
  have hfac : 𝔼 b, f b = (𝔼 x : ι → Bool, exp (t * (∑ i, a i * signVal (x i)) ^ 2)) ^ k := by
    simp only [f, mul_sum, exp_sum]
    exact expect_prod_row fun x => exp (t * (∑ i, a i * signVal (x i)) ^ 2)
  have hrow := expect_exp_mul_sq_sum_mul_signVal_le a ht0 (by rw [← hSdef, htS]; exact hτ)
  rw [← hSdef, htS] at hrow
  have hM := Fintype.mul_dens_filter_le_expect (fun b => (exp_pos _).le : ∀ b, 0 ≤ f b)
    (exp (t * (k * (1 + ε) * S)))
  have h1 : 1 - 2 * τ = (1 + ε)⁻¹ := by
    rw [hτdef]
    field_simp
    ring
  have h2 : t * (k * (1 + ε) * S) = k * (ε / 2) := by
    rw [show t * (k * (1 + ε) * S) = k * (1 + ε) * (t * S) by ring, htS, hτdef]
    field_simp
  calc (dens ({b | k * (1 + ε) * S < ∑ j, (∑ i, a i * signVal (b j i)) ^ 2} :
          Finset (Fin k → ι → Bool)) : ℝ)
      ≤ dens ({b | exp (t * (k * (1 + ε) * S)) ≤ f b} : Finset _) := by
        exact_mod_cast dens_le_dens hsub
    _ ≤ (𝔼 b, f b) / exp (t * (k * (1 + ε) * S)) := by
        rw [le_div_iff₀ (exp_pos _), mul_comm]
        exact hM
    _ ≤ ((√(1 - 2 * τ))⁻¹) ^ k / exp (t * (k * (1 + ε) * S)) := by
        rw [hfac]
        gcongr
    _ = (√(1 + ε) * exp (-(ε / 2))) ^ k := by
        rw [h2, h1, Real.sqrt_inv, inv_inv, exp_nat_mul, mul_pow, div_eq_mul_inv, ← inv_pow,
          ← exp_neg]
    _ ≤ (exp (-(ε ^ 2 / 4 - ε ^ 3 / 6))) ^ k := by
        gcongr
        exact sqrt_one_add_mul_exp_neg_le hε
    _ = exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
        rw [← exp_nat_mul]
        congr 1
        ring

/-- For the lower tail: `𝔼 exp (-t Y²) ≤ 1 - t ∑ a² + 3 (t ∑ a²)² / 2` for a Rademacher sum `Y`
and `0 ≤ t`, from `exp (-u) ≤ 1 - u + u² / 2`, `𝔼 Y² = ∑ a²` and `𝔼 Y⁴ ≤ 3 (∑ a²)²`. -/
private theorem expect_exp_neg_mul_sq_sum_mul_signVal_le (a : ι → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    𝔼 x : ι → Bool, exp (-(t * (∑ i, a i * signVal (x i)) ^ 2)) ≤
      1 - t * ∑ i, a i ^ 2 + 3 / 2 * (t * ∑ i, a i ^ 2) ^ 2 := by
  calc 𝔼 x : ι → Bool, exp (-(t * (∑ i, a i * signVal (x i)) ^ 2))
      ≤ 𝔼 x : ι → Bool, (1 - t * (∑ i, a i * signVal (x i)) ^ 2 +
          t ^ 2 / 2 * (∑ i, a i * signVal (x i)) ^ 4) :=
        expect_le_expect fun x _ => by
          have := exp_neg_le_one_sub_add_sq_div_two
            (by positivity : 0 ≤ t * (∑ i, a i * signVal (x i)) ^ 2)
          linarith [show (t * (∑ i, a i * signVal (x i)) ^ 2) ^ 2 =
            t ^ 2 * (∑ i, a i * signVal (x i)) ^ 4 by ring]
    _ = 1 - t * 𝔼 x : ι → Bool, (∑ i, a i * signVal (x i)) ^ 2 +
          t ^ 2 / 2 * 𝔼 x : ι → Bool, (∑ i, a i * signVal (x i)) ^ 4 := by
        rw [expect_add_distrib, expect_sub_distrib, Fintype.expect_const, ← mul_expect,
          ← mul_expect]
    _ ≤ 1 - t * ∑ i, a i ^ 2 + 3 / 2 * (t * ∑ i, a i ^ 2) ^ 2 := by
        rw [expect_sq_sum_mul_signVal]
        have := mul_le_mul_of_nonneg_left (expect_sum_mul_signVal_pow_four_le a)
          (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
        nlinarith

/-- **Lower tail**: for `k` independent Rademacher sums `Y_j = ∑ i, a i signVal (b j i)` and
`0 ≤ ε`, `Pr[∑ j, Y_j² < k (1 - ε) ∑ a²] ≤ exp (-(k / 2) (ε² / 2 - ε³ / 3))`. -/
theorem dens_sum_sq_sum_mul_signVal_lt_mul_le (a : ι → ℝ) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (dens ({b | ∑ j, (∑ i, a i * signVal (b j i)) ^ 2 < k * (1 - ε) * ∑ i, a i ^ 2} :
        Finset (Fin k → ι → Bool)) : ℝ) ≤
      exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  have hS0 : 0 ≤ ∑ i, a i ^ 2 := sum_nonneg fun i _ => sq_nonneg (a i)
  rcases le_or_gt 1 ε with hε1 | hε1
  · rw [filter_false_of_mem fun b _ => not_lt.2 ?_, dens_empty, NNRat.cast_zero]
    · positivity
    have : (k : ℝ) * (1 - ε) * ∑ i, a i ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
        (by linarith)) hS0
    exact this.trans (sum_nonneg fun j _ => sq_nonneg _)
  rcases hS0.eq_or_lt with hS | hS
  · rw [filter_false_of_mem fun b _ => ?_, dens_empty, NNRat.cast_zero]
    · positivity
    simp only [← hS, sum_mul_signVal_eq_zero hS.symm, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sum_const_zero, lt_irrefl]
  set S := ∑ i, a i ^ 2 with hSdef
  set τ := ε / (2 * (1 + ε)) with hτdef
  set t := τ / S with htdef
  have hτ0 : 0 ≤ τ := by positivity
  have ht0 : 0 ≤ t := by positivity
  have htS : t * S = τ := by
    rw [htdef]
    field_simp
  set f : (Fin k → ι → Bool) → ℝ :=
    fun b => exp (-(t * ∑ j, (∑ i, a i * signVal (b j i)) ^ 2))
  have hsub : ({b | ∑ j, (∑ i, a i * signVal (b j i)) ^ 2 < k * (1 - ε) * S} :
      Finset (Fin k → ι → Bool)) ⊆ ({b | exp (-(t * (k * (1 - ε) * S))) ≤ f b} : Finset _) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hb.le ht0))
  have hfac : 𝔼 b, f b =
      (𝔼 x : ι → Bool, exp (-(t * (∑ i, a i * signVal (x i)) ^ 2))) ^ k := by
    simp only [f, mul_sum, ← sum_neg_distrib, exp_sum]
    exact expect_prod_row fun x => exp (-(t * (∑ i, a i * signVal (x i)) ^ 2))
  have hrow := expect_exp_neg_mul_sq_sum_mul_signVal_le a ht0
  rw [← hSdef, htS] at hrow
  have hA : 0 ≤ 1 - τ + 3 / 2 * τ ^ 2 := by nlinarith [sq_nonneg (τ - 1 / 3)]
  have hM := Fintype.mul_dens_filter_le_expect (fun b => (exp_pos _).le : ∀ b, 0 ≤ f b)
    (exp (-(t * (k * (1 - ε) * S))))
  have h2 : t * (k * (1 - ε) * S) = k * (τ * (1 - ε)) := by
    rw [show t * (k * (1 - ε) * S) = k * (1 - ε) * (t * S) by ring, htS]
    ring
  calc (dens ({b | ∑ j, (∑ i, a i * signVal (b j i)) ^ 2 < k * (1 - ε) * S} :
          Finset (Fin k → ι → Bool)) : ℝ)
      ≤ dens ({b | exp (-(t * (k * (1 - ε) * S))) ≤ f b} : Finset _) := by
        exact_mod_cast dens_le_dens hsub
    _ ≤ (𝔼 b, f b) / exp (-(t * (k * (1 - ε) * S))) := by
        rw [le_div_iff₀ (exp_pos _), mul_comm]
        exact hM
    _ ≤ (1 - τ + 3 / 2 * τ ^ 2) ^ k / exp (-(t * (k * (1 - ε) * S))) := by
        rw [hfac]
        gcongr
    _ = ((1 - τ + 3 / 2 * τ ^ 2) * exp (τ * (1 - ε))) ^ k := by
        rw [h2, exp_neg, div_inv_eq_mul, exp_nat_mul, mul_pow]
    _ ≤ (exp (-(ε ^ 2 / 4 - ε ^ 3 / 6))) ^ k :=
        pow_le_pow_left₀ (mul_nonneg hA (exp_pos _).le) (lower_tail_factor_le hε hε1.le) k
    _ = exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
        rw [← exp_nat_mul]
        congr 1
        ring

/-! ### Random sign projections -/

/-- The **random sign projection** with seed `b : Fin k → ι → Bool`: the linear map
`EuclideanSpace ℝ ι → EuclideanSpace ℝ (Fin k)` whose matrix has entries `signVal (b j i) / √k`.
For a uniformly random seed the entries are independent uniform signs `±1 / √k`, Achlioptas's
`±1` distribution [Achlioptas2003]. -/
noncomputable def signProjection {k : ℕ} (b : Fin k → ι → Bool) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  Matrix.toEuclideanLin (Matrix.of fun j i => (√k)⁻¹ * signVal (b j i))

theorem signProjection_apply {k : ℕ} (b : Fin k → ι → Bool) (x : EuclideanSpace ℝ ι)
    (j : Fin k) : signProjection b x j = (√k)⁻¹ * ∑ i, x i * signVal (b j i) := by
  simp only [signProjection, Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- `‖signProjection b x‖² = (1 / k) ∑ j, (∑ i, x i signVal (b j i))²`. -/
theorem norm_signProjection_sq {k : ℕ} (b : Fin k → ι → Bool) (x : EuclideanSpace ℝ ι) :
    ‖signProjection b x‖ ^ 2 = (∑ j, (∑ i, x i * signVal (b j i)) ^ 2) / k := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [signProjection_apply, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg k), ← mul_sum]
  rw [inv_mul_eq_div]

/-- **Upper tail for a vector** [Achlioptas2003]: for `0 ≤ ε`,
`Pr[(1 + ε) ‖x‖² < ‖signProjection b x‖²] ≤ exp (-(k / 2) (ε² / 2 - ε³ / 3))`. -/
theorem dens_lt_norm_signProjection_sq_le (k : ℕ) (x : EuclideanSpace ℝ ι) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (dens ({b | (1 + ε) * ‖x‖ ^ 2 < ‖signProjection b x‖ ^ 2} : Finset (Fin k → ι → Bool)) : ℝ) ≤
      exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [CharP.cast_eq_zero, zero_div, neg_zero, zero_mul, exp_zero]
    exact_mod_cast dens_le_one
  refine le_trans ?_ (dens_mul_lt_sum_sq_sum_mul_signVal_le (fun i => x i) k hε)
  refine NNRat.cast_le.2 (dens_le_dens fun b hb => ?_)
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  rw [norm_signProjection_sq, EuclideanSpace.real_norm_sq_eq,
    lt_div_iff₀ (by positivity : (0 : ℝ) < k)] at hb
  linarith

/-- **Lower tail for a vector** [Achlioptas2003]: for `0 ≤ ε`,
`Pr[‖signProjection b x‖² < (1 - ε) ‖x‖²] ≤ exp (-(k / 2) (ε² / 2 - ε³ / 3))`. -/
theorem dens_norm_signProjection_sq_lt_le (k : ℕ) (x : EuclideanSpace ℝ ι) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (dens ({b | ‖signProjection b x‖ ^ 2 < (1 - ε) * ‖x‖ ^ 2} : Finset (Fin k → ι → Bool)) : ℝ) ≤
      exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [CharP.cast_eq_zero, zero_div, neg_zero, zero_mul, exp_zero]
    exact_mod_cast dens_le_one
  refine le_trans ?_ (dens_sum_sq_sum_mul_signVal_lt_mul_le (fun i => x i) k hε)
  refine NNRat.cast_le.2 (dens_le_dens fun b hb => ?_)
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  rw [norm_signProjection_sq, EuclideanSpace.real_norm_sq_eq,
    div_lt_iff₀ (by positivity : (0 : ℝ) < k)] at hb
  linarith

/-- **The distributional Johnson–Lindenstrauss lemma for sign matrices** [Achlioptas2003]: for
`0 ≤ ε`, `Pr[ε ‖x‖² < |‖signProjection b x‖² - ‖x‖²|] ≤ 2 exp (-(k / 2) (ε² / 2 - ε³ / 3))`. -/
theorem dens_lt_abs_norm_signProjection_sq_sub_le (k : ℕ) (x : EuclideanSpace ℝ ι) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (dens ({b | ε * ‖x‖ ^ 2 < |‖signProjection b x‖ ^ 2 - ‖x‖ ^ 2|} :
        Finset (Fin k → ι → Bool)) : ℝ) ≤
      2 * exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  have hsub : ({b | ε * ‖x‖ ^ 2 < |‖signProjection b x‖ ^ 2 - ‖x‖ ^ 2|} :
      Finset (Fin k → ι → Bool)) ⊆
      ({b | (1 + ε) * ‖x‖ ^ 2 < ‖signProjection b x‖ ^ 2} : Finset (Fin k → ι → Bool)) ∪
        ({b | ‖signProjection b x‖ ^ 2 < (1 - ε) * ‖x‖ ^ 2} : Finset (Fin k → ι → Bool)) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union, lt_abs] at hb ⊢
    rcases hb with hb | hb
    · left
      linarith
    · right
      linarith
  calc (dens ({b | ε * ‖x‖ ^ 2 < |‖signProjection b x‖ ^ 2 - ‖x‖ ^ 2|} :
          Finset (Fin k → ι → Bool)) : ℝ)
      ≤ dens ({b | (1 + ε) * ‖x‖ ^ 2 < ‖signProjection b x‖ ^ 2} : Finset (Fin k → ι → Bool)) +
        dens ({b | ‖signProjection b x‖ ^ 2 < (1 - ε) * ‖x‖ ^ 2} :
          Finset (Fin k → ι → Bool)) := by
        exact_mod_cast (dens_le_dens hsub).trans (dens_union_le _ _)
    _ ≤ _ := by
        rw [two_mul]
        exact add_le_add (dens_lt_norm_signProjection_sq_le k x hε)
          (dens_norm_signProjection_sq_lt_le k x hε)

/-! ### Finite point sets -/

/-- There are `n (n - 1) / 2` pairs `i < j` in `Fin n`. -/
private theorem sum_card_Ioi_mul_two (n : ℕ) :
    ((∑ i : Fin n, #(Ioi i) : ℕ) : ℝ) * 2 = n * (n - 1) := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n, sum_range_reflect (fun i => i) n]
  rcases n with _ | n
  · simp
  · have h := sum_range_id_mul_two (n + 1)
    rw [Nat.add_sub_cancel] at h
    have h' : ((∑ j ∈ range (n + 1), j : ℕ) : ℝ) * 2 = ((n + 1) * n : ℕ) := by
      exact_mod_cast h
    rw [h']
    push_cast
    ring

/-- **The Johnson–Lindenstrauss union bound** [Achlioptas2003]: for `n` points and `0 ≤ ε`, a
random sign projection keeps every squared pairwise distance in `[1 - ε, 1 + ε]` times its original
value with probability at least `1 - n (n - 1) exp (-(k / 2) (ε² / 2 - ε³ / 3))`. -/
theorem one_sub_le_dens_forall_norm_signProjection_sq_mem_Icc {n : ℕ}
    (p : Fin n → EuclideanSpace ℝ ι) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - n * (n - 1) * exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) ≤
      (dens ({b | ∀ i j, ‖signProjection b (p i - p j)‖ ^ 2 ∈
          Set.Icc ((1 - ε) * ‖p i - p j‖ ^ 2) ((1 + ε) * ‖p i - p j‖ ^ 2)} :
        Finset (Fin k → ι → Bool)) : ℝ) := by
  set e := exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3))
  set G : Finset (Fin k → ι → Bool) := {b | ∀ i j, ‖signProjection b (p i - p j)‖ ^ 2 ∈
    Set.Icc ((1 - ε) * ‖p i - p j‖ ^ 2) ((1 + ε) * ‖p i - p j‖ ^ 2)}
  set D : Fin n → Fin n → Finset (Fin k → ι → Bool) := fun i j =>
    {b | ε * ‖p i - p j‖ ^ 2 < |‖signProjection b (p i - p j)‖ ^ 2 - ‖p i - p j‖ ^ 2|}
  set B : Finset (Fin k → ι → Bool) := univ.biUnion fun i : Fin n => (Ioi i).biUnion (D i)
  have hgood (b : Fin k → ι → Bool) (i j : Fin n)
      (h : |‖signProjection b (p i - p j)‖ ^ 2 - ‖p i - p j‖ ^ 2| ≤ ε * ‖p i - p j‖ ^ 2) :
      ‖signProjection b (p i - p j)‖ ^ 2 ∈
        Set.Icc ((1 - ε) * ‖p i - p j‖ ^ 2) ((1 + ε) * ‖p i - p j‖ ^ 2) := by
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  -- Seeds outside the union of the failure events over pairs `i < j` are good.
  have hsub : univ \ B ⊆ G := by
    intro b hb
    simp only [B, D, mem_sdiff, mem_univ, true_and, mem_biUnion, mem_Ioi, mem_filter, not_exists,
      not_and, not_lt] at hb
    simp only [G, mem_filter, mem_univ, true_and]
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact hgood b i j (hb i j hij)
    · simp only [sub_self, map_zero, norm_zero]
      norm_num
    · have := hgood b j i (hb j i hij)
      rwa [norm_sub_rev (p j), ← neg_sub (p i) (p j), map_neg, norm_neg] at this
  have hB : (dens B : ℝ) ≤ n * (n - 1) * e := by
    have h1 : dens B ≤ ∑ i : Fin n, ∑ j ∈ Ioi i, dens (D i j) :=
      dens_biUnion_le.trans (sum_le_sum fun i _ => dens_biUnion_le)
    have h1' : (dens B : ℝ) ≤ ∑ i : Fin n, ∑ j ∈ Ioi i, (dens (D i j) : ℝ) := by
      simpa only [NNRat.cast_sum] using (NNRat.cast_le (K := ℝ)).2 h1
    calc (dens B : ℝ) ≤ ∑ i : Fin n, ∑ j ∈ Ioi i, (2 * e) :=
          h1'.trans (sum_le_sum fun i _ => sum_le_sum fun j _ =>
            dens_lt_abs_norm_signProjection_sq_sub_le k (p i - p j) hε)
      _ = n * (n - 1) * e := by
          simp only [sum_const, nsmul_eq_mul]
          rw [← sum_mul, ← Nat.cast_sum, show ((∑ i : Fin n, #(Ioi i) : ℕ) : ℝ) * (2 * e) =
            ((∑ i : Fin n, #(Ioi i) : ℕ) : ℝ) * 2 * e by ring, sum_card_Ioi_mul_two]
  have h1 : dens (univ : Finset (Fin k → ι → Bool)) ≤ dens (univ \ B) + dens B :=
    dens_le_dens_sdiff_add_dens
  rw [dens_univ] at h1
  have h1' : (1 : ℝ) ≤ dens (univ \ B) + dens B := by exact_mod_cast h1
  have h2 : (dens (univ \ B) : ℝ) ≤ dens G := by exact_mod_cast dens_le_dens hsub
  linarith

/-- The choice of `k`: `(4 + 2β) log n ≤ k (ε² / 2 - ε³ / 3)` gives
`exp (-(k / 2) (ε² / 2 - ε³ / 3)) ≤ exp (-(2 + β) log n) = n^(-(2 + β))`. -/
private theorem exp_le_exp_neg_mul_log {n k : ℕ} {ε β : ℝ} (hε : 0 < ε) (hε' : ε < 3 / 2)
    (hk : (4 + 2 * β) / (ε ^ 2 / 2 - ε ^ 3 / 3) * log n ≤ k) :
    exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) ≤ exp (-((2 + β) * log n)) := by
  have hD : 0 < ε ^ 2 / 2 - ε ^ 3 / 3 := by
    have := mul_pos (pow_pos hε 2) (by linarith : (0 : ℝ) < 1 / 2 - ε / 3)
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hD] at hk
  exact exp_le_exp.2 (by linarith)

/-- **Achlioptas's theorem for sign matrices** [Achlioptas2003, Theorem 1.1]: for `n` points,
`0 < ε < 3 / 2`, any real `β` and `k ≥ (4 + 2β) / (ε² / 2 - ε³ / 3) · log n`, a random sign
projection keeps every squared pairwise distance in `[1 - ε, 1 + ε]` times its original value with
probability at least `1 - n^(-β)`. The statement is informative for `β > 0`. -/
theorem one_sub_rpow_le_dens_forall_norm_signProjection_sq_mem_Icc {n : ℕ}
    (p : Fin n → EuclideanSpace ℝ ι) {k : ℕ} {ε β : ℝ} (hε : 0 < ε) (hε' : ε < 3 / 2)
    (hk : (4 + 2 * β) / (ε ^ 2 / 2 - ε ^ 3 / 3) * log n ≤ k) :
    1 - (n : ℝ) ^ (-β) ≤
      (dens ({b | ∀ i j, ‖signProjection b (p i - p j)‖ ^ 2 ∈
          Set.Icc ((1 - ε) * ‖p i - p j‖ ^ 2) ((1 + ε) * ‖p i - p j‖ ^ 2)} :
        Finset (Fin k → ι → Bool)) : ℝ) := by
  refine le_trans ?_ (one_sub_le_dens_forall_norm_signProjection_sq_mem_Icc p k hε.le)
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [CharP.cast_eq_zero, zero_mul, sub_zero]
    linarith [rpow_nonneg (le_refl (0 : ℝ)) (-β)]
  have hn' : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have he := exp_le_exp_neg_mul_log hε hε' hk
  have h2 : (n : ℝ) ^ (-β) = exp (log n) * exp (log n) * exp (-((2 + β) * log n)) := by
    rw [rpow_def_of_pos hn', ← exp_add, ← exp_add]
    congr 1
    ring
  rw [h2, exp_log hn']
  have : (n : ℝ) * (n - 1) * exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) ≤
      n * n * exp (-((2 + β) * log n)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hn'.le) he (exp_pos _).le
      (by positivity)
  linarith

/-- **The Johnson–Lindenstrauss lemma with sign matrices** [Achlioptas2003]
[DasguptaGupta2003]: for `n` points, `0 < ε < 3 / 2` and `k ≥ 4 log n / (ε² / 2 - ε³ / 3)`, some
sign projection keeps every squared pairwise distance in `[1 - ε, 1 + ε]` times its original value.
-/
theorem exists_signProjection_forall_norm_sq_mem_Icc {n : ℕ} (p : Fin n → EuclideanSpace ℝ ι)
    {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε' : ε < 3 / 2)
    (hk : 4 / (ε ^ 2 / 2 - ε ^ 3 / 3) * log n ≤ k) :
    ∃ b : Fin k → ι → Bool, ∀ i j, ‖signProjection b (p i - p j)‖ ^ 2 ∈
      Set.Icc ((1 - ε) * ‖p i - p j‖ ^ 2) ((1 + ε) * ‖p i - p j‖ ^ 2) := by
  have h := one_sub_le_dens_forall_norm_signProjection_sq_mem_Icc p k hε.le
  have hpos : (0 : ℝ) < 1 - n * (n - 1) * exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by positivity
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have he := exp_le_exp_neg_mul_log (β := 0) hε hε' (by rwa [mul_zero, add_zero])
    rw [add_zero] at he
    have h1 : exp (log n) * exp (log n) * exp (-(2 * log n)) = 1 := by
      rw [← exp_add, ← exp_add, ← exp_zero]
      congr 1
      ring
    rw [exp_log hn'] at h1
    have : (n : ℝ) * (n - 1) * exp (-(k / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) <
        n * n * exp (-(2 * log n)) :=
      (mul_le_mul_of_nonneg_left he (mul_nonneg hn'.le (by linarith))).trans_lt
        (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left (by linarith) hn') (exp_pos _))
    rw [h1] at this
    linarith
  obtain ⟨b, hb⟩ := Finset.dens_pos.1 (by exact_mod_cast hpos.trans_le h)
  exact ⟨b, (mem_filter.1 hb).2⟩

omit [DecidableEq ι] in
/-- **The Johnson–Lindenstrauss lemma** [JohnsonLindenstrauss1984] [DasguptaGupta2003]: for `n`
points of `EuclideanSpace ℝ ι`, `0 < ε ≤ 1` and `k ≥ 24 log n / ε²`, some linear map into
`EuclideanSpace ℝ (Fin k)` keeps every squared pairwise distance in `[1 - ε, 1 + ε]` times its
original value. -/
theorem exists_linearMap_forall_norm_sq_mem_Icc {n : ℕ} (p : Fin n → EuclideanSpace ℝ ι) {k : ℕ}
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 24 / ε ^ 2 * log n ≤ k) :
    ∃ f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin k), ∀ i j,
      ‖f (p i) - f (p j)‖ ^ 2 ∈
        Set.Icc ((1 - ε) * ‖p i - p j‖ ^ 2) ((1 + ε) * ‖p i - p j‖ ^ 2) := by
  classical
  have hD : 0 < ε ^ 2 / 2 - ε ^ 3 / 3 := by
    have := mul_pos (pow_pos hε 2) (by linarith : (0 : ℝ) < 1 / 2 - ε / 3)
    linarith
  have hk' : 4 / (ε ^ 2 / 2 - ε ^ 3 / 3) * log n ≤ k := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (log_natCast_nonneg n)) hk
    rw [div_le_div_iff₀ hD (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hε1 (sq_nonneg ε)]
  obtain ⟨b, hb⟩ := exists_signProjection_forall_norm_sq_mem_Icc p hε (by linarith) hk'
  exact ⟨signProjection b, fun i j => by rw [← map_sub]; exact hb i j⟩

end Cslib.Probability
