/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, constants of the derivative of formal power series)

public import CslibFrontier.Init
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.LinearCombination

/-!
# Constants of the derivative of formal power series

Over a field `F` of characteristic zero, the only power series with zero derivative are the
constants. In the fraction-free form used for Wronskians: if `b * a' = a * b'` with `b ≠ 0`, then
`a` is a scalar multiple of `b` (`PowerSeries.exists_eq_smul_of_mul_derivative_eq`). Indeed two
such nonzero series have the same order, by comparing the lowest coefficients of both sides, and
subtracting the right multiple of `b` from `a` raises the order of `a`.

The file also records that differentiation lowers divisibility by a power of `X` by at most one,
and how the derivative interacts with `PowerSeries.rescale`.

## Main results

* `PowerSeries.exists_eq_smul_of_mul_derivative_eq`: `b * a' = a * b'` forces `a ∈ F • b`.
* `PowerSeries.X_pow_dvd_derivative`: `X ^ B ∣ h → X ^ (B - 1) ∣ h'`.
* `PowerSeries.derivative_rescale`: `(rescale a f)' = a • rescale a f'`.
-/

public section

namespace PowerSeries

open Finset

variable {F : Type*}

/-- Differentiation lowers divisibility by a power of `X` by at most one. -/
theorem X_pow_dvd_derivative [CommSemiring F] {B : ℕ} {h : F⟦X⟧} (hB : X ^ B ∣ h) :
    X ^ (B - 1) ∣ d⁄dX h := by
  rw [X_pow_dvd_iff] at hB ⊢
  intro m hm
  rw [coeff_derivative, hB (m + 1) (by omega), zero_mul]

/-- The derivative of a rescaled power series. -/
theorem derivative_rescale [CommSemiring F] (a : F) (f : F⟦X⟧) :
    d⁄dX (rescale a f) = a • rescale a (d⁄dX f) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_smul, smul_eq_mul]
  ring

variable [Field F]

private theorem coeff_add_mul {p q : F⟦X⟧} {e e₁ : ℕ} (hp : ∀ i < e, coeff i p = 0)
    (hq : ∀ j < e₁, coeff j q = 0) : coeff (e + e₁) (p * q) = coeff e p * coeff e₁ q := by
  rw [coeff_mul, sum_eq_single (e, e₁)]
  · rintro ⟨i, j⟩ hij hne
    rw [mem_antidiagonal] at hij
    rcases lt_or_ge i e with hi | hi
    · rw [hp i hi, zero_mul]
    · have hj : j < e₁ := by
        rcases lt_or_ge j e₁ with hj | hj
        · exact hj
        · exact absurd (Prod.ext (by simp only at hij ⊢; omega) (by simp only at hij ⊢; omega)) hne
      rw [hq j hj, mul_zero]
  · intro h
    exact absurd (by simp) h

private theorem coeff_X_mul_derivative (h : F⟦X⟧) (k : ℕ) :
    coeff k (X * d⁄dX h) = k * coeff k h := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

private theorem order_toNat_eq [CharZero F] {a b : F⟦X⟧} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : b * d⁄dX a = a * d⁄dX b) : a.order.toNat = b.order.toNat := by
  have hX : b * (X * d⁄dX a) = a * (X * d⁄dX b) := by linear_combination X * h
  have hθ (g : F⟦X⟧) : ∀ j < g.order.toNat, coeff j (X * d⁄dX g) = 0 := fun j hj => by
    rw [coeff_X_mul_derivative, coeff_of_lt_order_toNat j hj, mul_zero]
  have h₁ := coeff_add_mul (fun i hi => coeff_of_lt_order_toNat i hi) (hθ a)
    (p := b) (q := X * d⁄dX a)
  have h₂ := coeff_add_mul (fun i hi => coeff_of_lt_order_toNat i hi) (hθ b)
    (p := a) (q := X * d⁄dX b)
  rw [hX, add_comm, h₂, coeff_X_mul_derivative, coeff_X_mul_derivative] at h₁
  have hne : coeff a.order.toNat a * coeff b.order.toNat b ≠ 0 :=
    mul_ne_zero (coeff_order ha) (coeff_order hb)
  have hcast : (a.order.toNat : F) = b.order.toNat := by
    have h₃ : ((a.order.toNat : F) - b.order.toNat) *
        (coeff a.order.toNat a * coeff b.order.toNat b) = 0 := by linear_combination -h₁
    exact sub_eq_zero.1 ((mul_eq_zero.1 h₃).resolve_right hne)
  exact_mod_cast hcast

/-- Over a field of characteristic zero, if `b * a' = a * b'` and `b ≠ 0` then `a` is a scalar
multiple of `b`: the field of constants of the derivative is the base field. -/
theorem exists_eq_smul_of_mul_derivative_eq [CharZero F] {a b : F⟦X⟧} (hb : b ≠ 0)
    (h : b * d⁄dX a = a * d⁄dX b) : ∃ c : F, a = c • b := by
  set e := b.order.toNat
  refine ⟨coeff e a / coeff e b, ?_⟩
  by_contra hne
  have ha₁ : a - (coeff e a / coeff e b) • b ≠ 0 := sub_ne_zero.2 hne
  have h' : b * d⁄dX (a - (coeff e a / coeff e b) • b) =
      (a - (coeff e a / coeff e b) • b) * d⁄dX b := by
    rw [map_sub, Derivation.map_smul, mul_sub, sub_mul, h, smul_mul_assoc, mul_smul_comm,
      mul_comm b]
  have hord := order_toNat_eq ha₁ hb h'
  have hcoeff := coeff_order ha₁
  rw [hord] at hcoeff
  refine hcoeff ?_
  rw [map_sub, coeff_smul, smul_eq_mul, div_mul_cancel₀ _ (coeff_order hb), sub_self]

end PowerSeries
