/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.MasterTheorem
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The master theorem in asymptotic form

This module converts the explicit bounds of `Complexity.Foundations.Data.Nat.MasterTheorem` into
real powers and Mathlib's `Asymptotics.IsBigO`. Let `T` satisfy
`Nat.DivideConquerBound T a b n₀ T₀ (fun n => c n ^ d)` with `b ≥ 2` and `n₀ ≥ 1`.

* `a > b ^ d`: `T n ≤ (T₀ + c n₀ ^ d b ^ d / (a - b ^ d)) a n ^ log_b a` for `n ≠ 0`, so
  `T = O(n ^ log_b a)`.
* `a = b ^ d`: `T = O(n ^ d log n)`.
* `a < b ^ d`: `T = O(n ^ d)`.

Mathlib's `Mathlib.Computability.AkraBazzi` proves the more general Akra–Bazzi `Θ` bound. It
needs an equality recurrence over `ℝ` with positive base values and polynomial growth of the
driving term. The statements here start from the inequality `Nat.DivideConquerBound` and
give upper bounds only.

## Main results

* `Nat.pow_clog_le_mul_rpow_logb`: `a ^ ⌈log_b n⌉ ≤ a n ^ log_b a` for `n ≠ 0`.
* `Nat.clog_le_two_mul_logb`: `⌈log_b n⌉ ≤ 2 log_b n` for `n ≥ b`.
* `Nat.DivideConquerBound.le_mul_rpow`: case 1 with a real power and an explicit constant.
* `Nat.DivideConquerBound.isBigO_rpow`, `Nat.DivideConquerBound.isBigO_pow_mul_log`,
  `Nat.DivideConquerBound.isBigO_pow`: the three cases as `IsBigO` statements.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Theorem 4.1.
-/

public section

namespace Nat

open Asymptotics Filter

private theorem pow_rpow_logb {a b : ℕ} (hb : 1 < b) (ha : 1 ≤ a) (j : ℕ) :
    ((b : ℝ) ^ j) ^ Real.logb b a = (a : ℝ) ^ j := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (b : ℝ) ≠ 1 := by exact_mod_cast (by omega : b ≠ 1)
  rw [← Real.rpow_natCast (b : ℝ) j, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_logb hb0 hb1 (by exact_mod_cast (by omega : 0 < a)),
    Real.rpow_natCast]

/-- `a ^ ⌈log_b n⌉ ≤ a n ^ log_b a` for `b ≥ 2`, `a ≥ 1` and `n ≠ 0`. -/
theorem pow_clog_le_mul_rpow_logb {a b n : ℕ} (hb : 1 < b) (ha : 1 ≤ a) (hn : n ≠ 0) :
    ((a ^ clog b n : ℕ) : ℝ) ≤ a * (n : ℝ) ^ Real.logb b a := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp only [clog_one_right, pow_zero, Nat.cast_one, Real.one_rpow, mul_one]
    exact_mod_cast ha
  · have hlog : 0 ≤ Real.logb b (a : ℝ) :=
      Real.logb_nonneg (by exact_mod_cast hb) (by exact_mod_cast ha)
    set k := clog b n
    have hlt : b ^ (k - 1) < n := pow_pred_clog_lt_self hb (by omega)
    have hk : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos (clog_pos hb h)).symm
    calc ((a ^ k : ℕ) : ℝ) = (a : ℝ) * ((b : ℝ) ^ (k - 1)) ^ Real.logb b a := by
          rw [pow_rpow_logb hb ha, Nat.cast_pow, hk, pow_succ, Nat.add_sub_cancel, mul_comm]
      _ ≤ a * (n : ℝ) ^ Real.logb b a := by
          gcongr
          exact_mod_cast hlt.le

/-- `⌈log_b n⌉ ≤ 2 log_b n` for `b ≥ 2` and `n ≥ b`. -/
theorem clog_le_two_mul_logb {b n : ℕ} (hb : 1 < b) (hn : b ≤ n) :
    (clog b n : ℝ) ≤ 2 * Real.logb b n := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have h1 : 1 ≤ Real.logb b n := by
    rw [← Real.logb_self_eq_one hb']
    exact Real.logb_le_logb_of_le hb' (by positivity) (by exact_mod_cast hn)
  have h2 : (clog b n : ℝ) < Real.logb b n + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one (by linarith)
  linarith

namespace DivideConquerBound

variable {T : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Master theorem, case 1**, with a real power: if `b ^ d < a` and `n ≠ 0`, then
`T n ≤ (T₀ + c n₀ ^ d b ^ d / (a - b ^ d)) a n ^ log_b a`. -/
theorem le_mul_rpow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : b ^ d < a) {n : ℕ} (hn : n ≠ 0) :
    (T n : ℝ) ≤ (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * a * (n : ℝ) ^ Real.logb b a := by
  have ha : 1 ≤ a := by have := Nat.one_le_pow d b (by omega); omega
  have hmain := h.sub_mul_le_pow_clog ha hb hn₀ n
  have hpos : (0 : ℝ) < (a : ℝ) - b ^ d := by
    have : ((b ^ d : ℕ) : ℝ) < a := by exact_mod_cast hlt
    push_cast at this
    linarith
  have hcast : ((a - b ^ d : ℕ) : ℝ) = (a : ℝ) - b ^ d := by
    rw [Nat.cast_sub hlt.le]; push_cast; ring
  have hmain' : ((a : ℝ) - b ^ d) * T n ≤
      (((a : ℝ) - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * ((a ^ clog b n : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hmain
    push_cast [hcast] at this ⊢
    exact this
  have hT : (T n : ℝ) ≤ (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * ((a ^ clog b n : ℕ) : ℝ) := by
    have he : (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * ((a ^ clog b n : ℕ) : ℝ) =
        (((a : ℝ) - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * ((a ^ clog b n : ℕ) : ℝ) /
          (a - b ^ d) := by
      field_simp
    rw [he, le_div_iff₀ hpos]
    linarith
  calc (T n : ℝ) ≤ _ := hT
    _ ≤ (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * (a * (n : ℝ) ^ Real.logb b a) := by
        gcongr
        exact pow_clog_le_mul_rpow_logb hb ha hn
    _ = _ := by ring

/-- **Master theorem, case 1**: if `b ^ d < a`, then `T = O(n ^ log_b a)`. -/
theorem isBigO_rpow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : b ^ d < a) :
    (fun n => (T n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ Real.logb b a := by
  refine IsBigO.of_bound ((T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * a) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  exact h.le_mul_rpow hb hn₀ hlt (by omega)

/-- **Master theorem, case 2**: if `a = b ^ d`, then `T = O(n ^ d log n)`. -/
theorem isBigO_pow_mul_log (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (had : a = b ^ d) :
    (fun n => (T n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ d * Real.log n := by
  have ha : 1 ≤ a := had ▸ Nat.one_le_pow d b (by omega)
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb : 0 < Real.log b := Real.log_pos hb'
  refine IsBigO.of_bound ((b : ℝ) ^ d * (T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b)) ?_
  filter_upwards [eventually_ge_atTop b] with n hn
  have hL : 1 ≤ Real.logb b n := by
    rw [← Real.logb_self_eq_one hb']
    exact Real.logb_le_logb_of_le hb' (by positivity) (by exact_mod_cast hn)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  have hmain : (T n : ℝ) ≤ ((b : ℝ) * n) ^ d * (T₀ + c * n₀ ^ d * (clog b n : ℝ)) := by
    exact_mod_cast h.le_mul_pow_mul_clog ha hb hn₀ had (by omega : n ≠ 0)
  have hK := clog_le_two_mul_logb hb hn
  have hinner : (T₀ : ℝ) + c * n₀ ^ d * (clog b n : ℝ) ≤
      (T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b) * Real.log n := by
    have e : (T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b) * Real.log n =
        T₀ * Real.logb b n + c * n₀ ^ d * (2 * Real.logb b n) := by
      rw [Real.logb]; field_simp
    rw [e]
    have hT0 : (T₀ : ℝ) ≤ T₀ * Real.logb b n := le_mul_of_one_le_right (by positivity) hL
    have hc : (c : ℝ) * n₀ ^ d * (clog b n : ℝ) ≤ c * n₀ ^ d * (2 * Real.logb b n) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    linarith
  calc (T n : ℝ) ≤ _ := hmain
    _ ≤ ((b : ℝ) * n) ^ d * ((T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b) * Real.log n) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- **Master theorem, case 3**: if `a < b ^ d`, then `T = O(n ^ d)`. -/
theorem isBigO_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : a < b ^ d) :
    (fun n => (T n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ d := by
  set K : ℕ := (b ^ d - a) * T₀ + c * n₀ ^ d * b ^ d
  have hpos : (0 : ℝ) < ((b ^ d - a : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
  refine IsBigO.of_bound ((K : ℝ) * (b : ℝ) ^ d / ((b ^ d - a : ℕ) : ℝ)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  have hmain : ((b ^ d - a : ℕ) : ℝ) * T n ≤ K * (((b * n) ^ d : ℕ) : ℝ) := by
    exact_mod_cast h.sub_mul_le_mul_pow ha hb hn₀ (by omega : n ≠ 0)
  rw [Nat.cast_pow, Nat.cast_mul, mul_pow] at hmain
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

end DivideConquerBound

end Nat
