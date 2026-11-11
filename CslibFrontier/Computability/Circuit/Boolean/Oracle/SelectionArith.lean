/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- upstream: local-only (spike for #4383 M5.4d; scratch, not for merge)

/-!
# Spike: the `∃ k ∀ β` size arithmetic for chained selection rounds

Design §7 step 3: with `q ≤ C·L^a`, `L ≤ 2^(2βn)` and `R ≤ D·L²`, the chained-round size
`R·2^n·(c₀(q+1)^c₀ + 4n + 8)` is at most `2^(n + (2ac₀+5)βn)` for all large `n`.
-/

open Filter Asymptotics

namespace SelectionArithSpike

/-- An affine function of `n` is eventually at most `r ^ n` when `r > 1`. -/
theorem eventually_affine_le_pow {r : ℝ} (hr : 1 < r) (A B : ℝ) :
    ∀ᶠ n : ℕ in atTop, A + B * n ≤ r ^ n := by
  have hB : 0 < 2 * (|B| + 1) := by positivity
  have h1 := (isLittleO_coe_const_pow_of_one_lt (R := ℝ) hr).def (inv_pos.mpr hB)
  have h2 := (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_ge_atTop (2 * A)
  filter_upwards [h1, h2] with n hn hA
  have hr0 : 0 ≤ r ^ n := pow_nonneg (by linarith) n
  rw [Real.norm_natCast, Real.norm_of_nonneg hr0] at hn
  have hBn : B * n ≤ |B| * n := mul_le_mul_of_nonneg_right (le_abs_self B) (Nat.cast_nonneg n)
  have hn' : (|B| + 1) * n ≤ r ^ n / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul_of_nonneg_left hn hB.le
    rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul] at this
    linarith
  nlinarith [abs_nonneg B, Nat.cast_nonneg (α := ℝ) n]

/-- `2 ^ (y * k) = (2 ^ y) ^ k` for a natural exponent `k`. -/
private theorem two_rpow_mul_nat (y : ℝ) (k : ℕ) :
    (2 : ℝ) ^ (y * k) = ((2 : ℝ) ^ y) ^ k := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- **Design §7 step 3.** The chained-round size bound. -/
theorem selection_size_le (C a c₀ D : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, ∀ L R q : ℕ, (q : ℝ) ≤ C * (L : ℝ) ^ a →
      (L : ℝ) ≤ (2 : ℝ) ^ (2 * β * n) → (R : ℝ) ≤ D * (L : ℝ) ^ 2 →
      (R : ℝ) * 2 ^ n * (c₀ * ((q : ℝ) + 1) ^ c₀ + 4 * n + 8) ≤
        (2 : ℝ) ^ ((n : ℝ) + (2 * a * c₀ + 5) * β * n) := by
  have hr : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  set A : ℝ := c₀ * ((C : ℝ) + 1) ^ c₀
  filter_upwards [eventually_affine_le_pow hr (D * (A + 8)) (D * 4)] with n hn
  intro L R q hq hL hR
  -- `X = 2 ^ (β n)`
  set X : ℝ := (2 : ℝ) ^ (β * n) with hXdef
  have hX : X = ((2 : ℝ) ^ β) ^ n := by
    rw [hXdef, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hX0 : 0 ≤ X := by linarith
  have hRHS : (2 : ℝ) ^ ((n : ℝ) + (2 * a * c₀ + 5) * β * n) =
      2 ^ n * X ^ (2 * a * c₀ + 5) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, hXdef, ← two_rpow_mul_nat]
    congr 2
    push_cast
    ring
  rw [hRHS]
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · -- `L = 0` forces `R = 0`
    have : (R : ℝ) = 0 := le_antisymm (by simpa using hR) (Nat.cast_nonneg R)
    rw [this, zero_mul, zero_mul]
    positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hLX : (L : ℝ) ≤ X ^ 2 := by
    rw [hXdef, ← two_rpow_mul_nat]
    convert hL using 2
    push_cast
    ring
  -- `q + 1 ≤ (C + 1) X ^ (2a)`
  have hLa : (L : ℝ) ^ a ≤ X ^ (2 * a) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hLX a
  have hq1 : (q : ℝ) + 1 ≤ ((C : ℝ) + 1) * X ^ (2 * a) := by
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ a := one_le_pow₀ hL1
    have h2 : (C : ℝ) * (L : ℝ) ^ a + 1 ≤ ((C : ℝ) + 1) * (L : ℝ) ^ a := by nlinarith
    calc (q : ℝ) + 1 ≤ C * (L : ℝ) ^ a + 1 := by linarith
      _ ≤ ((C : ℝ) + 1) * (L : ℝ) ^ a := h2
      _ ≤ ((C : ℝ) + 1) * X ^ (2 * a) := mul_le_mul_of_nonneg_left hLa (by positivity)
  have hqc : ((q : ℝ) + 1) ^ c₀ ≤ ((C : ℝ) + 1) ^ c₀ * X ^ (2 * a * c₀) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hq1 c₀
  have hY1 : 1 ≤ X ^ (2 * a * c₀) := one_le_pow₀ hX1
  have hinner : (c₀ : ℝ) * ((q : ℝ) + 1) ^ c₀ + 4 * n + 8 ≤
      X ^ (2 * a * c₀) * (A + 4 * n + 8) := by
    have : (c₀ : ℝ) * ((q : ℝ) + 1) ^ c₀ ≤ X ^ (2 * a * c₀) * A := by
      calc (c₀ : ℝ) * ((q : ℝ) + 1) ^ c₀ ≤ c₀ * (((C : ℝ) + 1) ^ c₀ * X ^ (2 * a * c₀)) :=
            mul_le_mul_of_nonneg_left hqc (Nat.cast_nonneg _)
        _ = X ^ (2 * a * c₀) * A := by ring
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hRX : (R : ℝ) ≤ D * X ^ 4 := by
    calc (R : ℝ) ≤ D * (L : ℝ) ^ 2 := hR
      _ ≤ D * (X ^ 2) ^ 2 := by gcongr
      _ = D * X ^ 4 := by ring
  have hDn : (D : ℝ) * (A + 4 * n + 8) ≤ X := by rw [hX]; linarith
  have hA0 : 0 ≤ A := by positivity
  calc (R : ℝ) * 2 ^ n * (c₀ * ((q : ℝ) + 1) ^ c₀ + 4 * n + 8)
      ≤ (D * X ^ 4) * 2 ^ n * (X ^ (2 * a * c₀) * (A + 4 * n + 8)) := by
        gcongr
    _ = 2 ^ n * X ^ (2 * a * c₀ + 4) * (D * (A + 4 * n + 8)) := by ring
    _ ≤ 2 ^ n * X ^ (2 * a * c₀ + 4) * X := by gcongr
    _ = 2 ^ n * X ^ (2 * a * c₀ + 5) := by ring

/-- Second-order Bernoulli: `1 + L/15 + L(L-1)/450 ≤ (16/15) ^ L`. -/
private theorem bernoulli₂ (L : ℕ) :
    1 + (L : ℝ) / 15 + (L : ℝ) * ((L : ℝ) - 1) / 450 ≤ (16 / 15 : ℝ) ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hL : 0 ≤ (L : ℝ) * ((L : ℝ) - 1) := by
      rcases L with _ | L
      · simp
      · push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) L]
    rw [pow_succ]
    push_cast
    nlinarith [ih, hL]

/-- Design §7 step 3, side condition: `4 (L ℓ + 1) < (16/15) ^ ℓ` for `ℓ = L + 200`. -/
theorem side_condition (L : ℕ) : 4 * ((L : ℝ) * (L + 200) + 1) < (16 / 15 : ℝ) ^ (L + 200) := by
  have h200 : (10 : ℝ) ^ 5 ≤ (16 / 15 : ℝ) ^ 200 := by norm_num
  have hb := bernoulli₂ L
  have hL := Nat.cast_nonneg (α := ℝ) L
  rw [pow_add]
  nlinarith

end SelectionArithSpike
