/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, new file `Mathlib/Analysis/Calculus/MovingAverage.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smoothing Lipschitz functions by repeated moving averages

The moving average `A_h φ (s) = h⁻¹ ∫₀ʰ φ(s + t) dt` of a continuous `φ : ℝ → ℝ` is
differentiable with derivative `D_h φ (s) = h⁻¹ (φ(s + h) - φ(s))`, and `A_h` commutes with
`D_h`. Hence the `m`-fold moving average `A_hᵐ φ` is of class `Cᵐ`, with
`(A_hᵐ φ)⁽ᵏ⁾ = A_hᵐ⁻ᵏ (D_hᵏ φ)` for `k ≤ m`. If `ψ` is `c`-Lipschitz, then `|D_h ψ| ≤ c`, every
further difference quotient multiplies the sup norm by at most `2 / h`, and `A_h` moves `ψ` by at
most `c h`. This gives **Proposition 11.58** of [O'Donnell, Proposition 11.58][ODonnell2014]
for derivatives of order at most `m`: for every `η > 0` there is a `Cᵐ` function `ψ̃` with
`|ψ̃ - ψ| ≤ c η` and `|ψ̃⁽ᵏ⁺¹⁾| ≤ (2m)ᵏ c / ηᵏ` for `k < m`.

The book smooths with a Gaussian, `ψ̃(s) = E[ψ(s + η g)]` (its Exercise 11.38), which gives a
single `C^∞` function. Here the smoothing variable is instead `h (U₁ + ⋯ + Uₘ)` for independent
`Uᵢ` uniform on `[0, 1]`, a bounded-support smoothing (cf. its Exercise 11.40); it yields `Cᵐ`
rather than `C^∞`, which suffices for the applications (`m = 4` for the Invariance Principle),
and all constants are explicit.

## Main definitions

* `Real.movingAverage`: the moving average `h⁻¹ ∫₀ʰ φ(s + t) dt`.

## Main results

* `Real.hasDerivAt_movingAverage`: the derivative of a moving average.
* `Real.continuous_movingAverage`: moving averages of continuous functions are continuous.
* `Real.contDiff_iterate_movingAverage`: `A_hᵐ φ` is of class `Cᵐ`.
* `LipschitzWith.movingAverage`: moving averages preserve `c`-Lipschitz functions.
* `LipschitzWith.abs_movingAverage_sub_le`: `|A_h ψ - ψ| ≤ c h`.
* `LipschitzWith.abs_iterate_movingAverage_sub_le`: `|A_hᵐ ψ - ψ| ≤ m c h`.
* `LipschitzWith.abs_iteratedDeriv_iterate_movingAverage_le`:
  `|(A_hᵐ ψ)⁽ᵏ⁺¹⁾| ≤ 2ᵏ c / hᵏ` for `k < m`.
* `LipschitzWith.exists_contDiff_smoothing`: a finite-order form of Proposition 11.58.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open intervalIntegral Set
open scoped Interval

namespace Real

/-- The **moving average** `h⁻¹ ∫₀ʰ φ(s + t) dt` of `φ : ℝ → ℝ` over windows of length `h`. -/
noncomputable def movingAverage (h : ℝ) (φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  h⁻¹ * ∫ t in (0 : ℝ)..h, φ (s + t)

/-- Unfolding `movingAverage`. -/
theorem movingAverage_def (h : ℝ) (φ : ℝ → ℝ) (s : ℝ) :
    movingAverage h φ s = h⁻¹ * ∫ t in (0 : ℝ)..h, φ (s + t) := by
  rw [movingAverage]

variable {h : ℝ} {φ : ℝ → ℝ}

/-- The forward difference quotient `h⁻¹ (φ(s + h) - φ(s))`. -/
private noncomputable def diffQuot (h : ℝ) (φ : ℝ → ℝ) (s : ℝ) : ℝ := h⁻¹ * (φ (s + h) - φ s)

private theorem intervalIntegrable_comp_add (hφ : Continuous φ) (c a b : ℝ) :
    IntervalIntegrable (fun t => φ (c + t)) MeasureTheory.volume a b :=
  (hφ.comp (continuous_const.add continuous_id)).intervalIntegrable a b

/-- A bound `C` on `|f|` over the window bounds the average `h⁻¹ ∫₀ʰ f`. -/
private theorem abs_inv_mul_integral_le {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t ∈ Ι 0 h, |f t| ≤ C) : |h⁻¹ * ∫ t in (0 : ℝ)..h, f t| ≤ C := by
  rcases eq_or_ne h 0 with rfl | hh
  · simpa using hC
  have := norm_integral_le_of_norm_le_const (a := 0) (b := h) (f := f) hf
  rw [Real.norm_eq_abs, sub_zero] at this
  rw [abs_mul, abs_inv]
  calc |h|⁻¹ * |∫ t in (0 : ℝ)..h, f t| ≤ |h|⁻¹ * (C * |h|) := by gcongr
    _ = C := by field_simp

/-- A moving average of a continuous function is a difference of antiderivatives. -/
private theorem movingAverage_eq (hφ : Continuous φ) (s : ℝ) :
    movingAverage h φ s = h⁻¹ * ((∫ t in (0 : ℝ)..s + h, φ t) - ∫ t in (0 : ℝ)..s, φ t) := by
  rw [movingAverage_def, integral_comp_add_left (fun t => φ t) s, add_zero,
    integral_interval_sub_left (hφ.intervalIntegrable _ _) (hφ.intervalIntegrable _ _)]

/-- The moving average of a continuous `φ` has derivative `h⁻¹ (φ(s + h) - φ(s))`. -/
theorem hasDerivAt_movingAverage (hφ : Continuous φ) (s : ℝ) :
    HasDerivAt (movingAverage h φ) (h⁻¹ * (φ (s + h) - φ s)) s := by
  have hΦ (u : ℝ) : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, φ t) (φ u) u :=
    (hφ.integral_hasStrictDerivAt 0 u).hasDerivAt
  have h1 : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u + h, φ t) (φ (s + h)) s :=
    (hΦ (s + h)).comp_add_const s h
  rw [show movingAverage h φ = _ from funext (movingAverage_eq hφ)]
  exact HasDerivAt.const_mul h⁻¹ (h1.sub (hΦ s))

/-- The moving average of a continuous function is continuous. -/
theorem continuous_movingAverage (hφ : Continuous φ) : Continuous (movingAverage h φ) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_movingAverage hφ s).continuousAt

private theorem deriv_movingAverage (hφ : Continuous φ) :
    deriv (movingAverage h φ) = diffQuot h φ :=
  funext fun s => (hasDerivAt_movingAverage hφ s).deriv

private theorem continuous_diffQuot (hφ : Continuous φ) : Continuous (diffQuot h φ) := by
  unfold diffQuot
  fun_prop

/-- Moving averages commute with difference quotients. -/
private theorem diffQuot_movingAverage (hφ : Continuous φ) :
    diffQuot h (movingAverage h φ) = movingAverage h (diffQuot h φ) := by
  funext s
  simp only [diffQuot, movingAverage_def, add_right_comm _ _ h]
  rw [integral_const_mul, integral_sub (intervalIntegrable_comp_add hφ _ _ _)
    (intervalIntegrable_comp_add hφ _ _ _)]
  ring

private theorem continuous_iterate_movingAverage (hφ : Continuous φ) (j : ℕ) :
    Continuous ((movingAverage h)^[j] φ) := by
  induction j with
  | zero => exact hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact continuous_movingAverage ih

private theorem diffQuot_iterate_movingAverage (j : ℕ) :
    ∀ φ, Continuous φ → diffQuot h ((movingAverage h)^[j] φ) =
      (movingAverage h)^[j] (diffQuot h φ) := by
  induction j with
  | zero => exact fun _ _ => rfl
  | succ j ih =>
    intro φ hφ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      diffQuot_movingAverage (continuous_iterate_movingAverage hφ j), ih φ hφ]

/-- The derivatives of `A_hᵐ φ`: `(A_hᵐ φ)⁽ᵏ⁾ = A_hᵐ⁻ᵏ (D_hᵏ φ)` for `k ≤ m`. -/
private theorem iteratedDeriv_iterate_movingAverage (k : ℕ) :
    ∀ m φ, Continuous φ → k ≤ m → iteratedDeriv k ((movingAverage h)^[m] φ) =
      (movingAverage h)^[m - k] ((diffQuot h)^[k] φ) := by
  induction k with
  | zero => intro m φ _ _; simp
  | succ k ih =>
    rintro (_ | m) φ hφ hkm
    · omega
    rw [iteratedDeriv_succ', Function.iterate_succ_apply',
      deriv_movingAverage (continuous_iterate_movingAverage hφ m),
      diffQuot_iterate_movingAverage m φ hφ, ih m _ (continuous_diffQuot hφ) (by omega),
      Function.iterate_succ_apply, Nat.add_sub_add_right]

/-- The `m`-fold moving average of a continuous function is of class `Cᵐ`. -/
theorem contDiff_iterate_movingAverage (hφ : Continuous φ) (m : ℕ) :
    ContDiff ℝ m ((movingAverage h)^[m] φ) := by
  have hcont (k : ℕ) : Continuous ((diffQuot h)^[k] φ) := by
    induction k with
    | zero => exact hφ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact continuous_diffQuot ih
  refine contDiff_iff_iteratedDeriv.2 ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hk : k ≤ m := by exact_mod_cast hk
    rw [iteratedDeriv_iterate_movingAverage k m φ hφ hk]
    exact continuous_iterate_movingAverage (hcont k) _
  · have hk : k < m := by exact_mod_cast hk
    rw [iteratedDeriv_iterate_movingAverage k m φ hφ hk.le,
      show m - k = (m - k - 1) + 1 by omega, Function.iterate_succ_apply']
    exact fun s => (hasDerivAt_movingAverage
      (continuous_iterate_movingAverage (hcont k) _) s).differentiableAt

/-- Moving averages preserve uniform bounds. -/
private theorem abs_iterate_movingAverage_le {M : ℝ} (hM : 0 ≤ M) (j : ℕ) :
    ∀ φ : ℝ → ℝ, (∀ s, |φ s| ≤ M) → ∀ s, |(movingAverage h)^[j] φ s| ≤ M := by
  induction j with
  | zero => exact fun φ hφ => hφ
  | succ j ih =>
    intro φ hφ s
    rw [Function.iterate_succ_apply]
    exact ih _ (fun s => abs_inv_mul_integral_le hM fun t _ => hφ _) s

end Real

open Real

namespace LipschitzWith

variable {c : NNReal} {ψ : ℝ → ℝ} {h : ℝ}

/-- A moving average of a `c`-Lipschitz function is `c`-Lipschitz. -/
protected theorem movingAverage (hψ : LipschitzWith c ψ) (h : ℝ) :
    LipschitzWith c (movingAverage h ψ) := by
  refine LipschitzWith.of_dist_le_mul fun s s' => ?_
  rw [Real.dist_eq, movingAverage_def, movingAverage_def, ← mul_sub,
    ← integral_sub (intervalIntegrable_comp_add hψ.continuous _ _ _)
      (intervalIntegrable_comp_add hψ.continuous _ _ _)]
  refine abs_inv_mul_integral_le (by positivity) fun t _ => ?_
  simpa [Real.dist_eq] using hψ.dist_le_mul (s + t) (s' + t)

/-- A moving average with window `h > 0` moves a `c`-Lipschitz function by at most `c h`. -/
theorem abs_movingAverage_sub_le (hψ : LipschitzWith c ψ) (hh : 0 < h) (s : ℝ) :
    |movingAverage h ψ s - ψ s| ≤ c * h := by
  have hint : (∫ t in (0 : ℝ)..h, ψ (s + t)) - h * ψ s =
      ∫ t in (0 : ℝ)..h, (ψ (s + t) - ψ s) := by
    rw [integral_sub (intervalIntegrable_comp_add hψ.continuous _ _ _)
      intervalIntegrable_const, integral_const, smul_eq_mul, sub_zero]
  have : movingAverage h ψ s - ψ s = h⁻¹ * ∫ t in (0 : ℝ)..h, (ψ (s + t) - ψ s) := by
    rw [← hint, movingAverage_def, mul_sub, inv_mul_cancel_left₀ hh.ne']
  rw [this]
  refine abs_inv_mul_integral_le (by positivity) fun t ht => ?_
  rw [uIoc_of_le hh.le] at ht
  calc |ψ (s + t) - ψ s| ≤ c * |s + t - s| := by
        simpa [Real.dist_eq] using hψ.dist_le_mul (s + t) s
    _ ≤ c * h := by
        rw [add_sub_cancel_left, abs_of_pos ht.1]
        exact mul_le_mul_of_nonneg_left ht.2 c.2

/-- The `m`-fold moving average with window `h > 0` moves a `c`-Lipschitz function by at most
`m c h`. -/
theorem abs_iterate_movingAverage_sub_le (hψ : LipschitzWith c ψ) (hh : 0 < h) (m : ℕ)
    (s : ℝ) : |(movingAverage h)^[m] ψ s - ψ s| ≤ m * c * h := by
  have hlip (j : ℕ) : LipschitzWith c ((movingAverage h)^[j] ψ) := by
    induction j with
    | zero => exact hψ
    | succ j ih =>
      rw [Function.iterate_succ']
      exact ih.movingAverage h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    calc _ ≤ |movingAverage h ((movingAverage h)^[m] ψ) s - (movingAverage h)^[m] ψ s| +
          |(movingAverage h)^[m] ψ s - ψ s| := abs_sub_le _ _ _
      _ ≤ c * h + m * c * h := add_le_add ((hlip m).abs_movingAverage_sub_le hh s) ih
      _ = (m + 1 : ℕ) * c * h := by push_cast; ring

/-- Iterated difference quotients of a `c`-Lipschitz function: `|D_hᵏ⁺¹ ψ| ≤ 2ᵏ c / hᵏ`. -/
private theorem abs_iterate_diffQuot_le (hψ : LipschitzWith c ψ) (hh : 0 < h) (k : ℕ) (s : ℝ) :
    |(diffQuot h)^[k + 1] ψ s| ≤ 2 ^ k * c / h ^ k := by
  induction k generalizing s with
  | zero =>
    rw [zero_add, Function.iterate_one, diffQuot, abs_mul, abs_inv, abs_of_pos hh]
    have := hψ.dist_le_mul (s + h) s
    rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left, abs_of_pos hh] at this
    calc h⁻¹ * |ψ (s + h) - ψ s| ≤ h⁻¹ * (c * h) := by gcongr
      _ = 2 ^ 0 * c / h ^ 0 := by field_simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', diffQuot, abs_mul, abs_inv, abs_of_pos hh]
    calc h⁻¹ * |_ - _| ≤ h⁻¹ * (2 ^ k * c / h ^ k + 2 ^ k * c / h ^ k) := by
          gcongr
          exact (abs_sub _ _).trans (add_le_add (ih _) (ih _))
      _ = 2 ^ (k + 1) * c / h ^ (k + 1) := by field_simp; ring

/-- The derivatives of the `m`-fold moving average of a `c`-Lipschitz function with window
`h > 0`: `|(A_hᵐ ψ)⁽ᵏ⁺¹⁾| ≤ 2ᵏ c / hᵏ` for `k < m`. -/
theorem abs_iteratedDeriv_iterate_movingAverage_le (hψ : LipschitzWith c ψ) (hh : 0 < h)
    {k m : ℕ} (hkm : k < m) (s : ℝ) :
    |iteratedDeriv (k + 1) ((movingAverage h)^[m] ψ) s| ≤ 2 ^ k * c / h ^ k := by
  rw [iteratedDeriv_iterate_movingAverage (k + 1) m ψ hψ.continuous hkm]
  exact abs_iterate_movingAverage_le (by positivity) _ _ (abs_iterate_diffQuot_le hψ hh k) s

/-- **A finite-order form of Proposition 11.58** [O'Donnell, Proposition 11.58][ODonnell2014]:
if `ψ : ℝ → ℝ` is `c`-Lipschitz, `η > 0` and `m : ℕ`, there is a `Cᵐ` function `ψ̃` with
`|ψ̃ - ψ| ≤ c η` and `|ψ̃⁽ᵏ⁺¹⁾| ≤ (2m)ᵏ c / ηᵏ` for every `k < m`. One may take the `m`-fold
moving average with window `η / m`. Unlike the book, which gives one `C^∞` function `ψ̃_η`
serving every order `k` with a constant depending only on `k`, here both `ψ̃` and the constant
`(2m)ᵏ` depend on the chosen order `m`. -/
theorem exists_contDiff_smoothing (hψ : LipschitzWith c ψ) (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ' : ℝ → ℝ, ContDiff ℝ m ψ' ∧ (∀ s, |ψ' s - ψ s| ≤ c * η) ∧
      ∀ k, k < m → ∀ s, |iteratedDeriv (k + 1) ψ' s| ≤ (2 * m) ^ k * c / η ^ k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨ψ, contDiff_zero.2 hψ.continuous, fun s => by simp only [sub_self, abs_zero]; positivity,
      fun k hk => absurd hk k.not_lt_zero⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < η / m := div_pos hη hm'
  refine ⟨(movingAverage (η / m))^[m] ψ, contDiff_iterate_movingAverage hψ.continuous m,
    fun s => ?_, fun k hk s => ?_⟩
  · refine (hψ.abs_iterate_movingAverage_sub_le hh m s).trans_eq ?_
    field_simp
  · refine (hψ.abs_iteratedDeriv_iterate_movingAverage_le hh hk s).trans_eq ?_
    rw [div_pow, mul_pow]
    field_simp

end LipschitzWith
