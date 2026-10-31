/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.CeilDiv
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The scale `n / √(log n)`

Natural-number estimates for the scale `n / Nat.sqrt (Nat.log 2 n)`, that is `⌊n / ⌊√⌊log₂ n⌋⌋⌋`,
in which the deterministic simulations of nondeterministic and probabilistic time by blocking and
tensor contraction are stated (#1833). From `n = 2` on the divisor is positive
(`Nat.one_le_sqrt_log_two`), and so is the scale (`Nat.one_le_div_sqrt_log_two`).

The scale dominates the logarithm (`Nat.log_two_le_div_sqrt_log_two`), hence every polynomial in
the exponent, and the number `⌈n / ⌈log₂ (n + 2)⌉⌉` of time blocks of length `⌈log₂ (n + 2)⌉`
(`Nat.ceilDiv_clog_two_le`). Scaling `n` by a constant scales it by at most that constant, up to
an additive constant (`Nat.mul_div_sqrt_log_two_le`). The scale is not monotone, since the divisor
jumps, but it is monotone up to constants (`Nat.div_sqrt_log_two_le_of_le`), so a bound in a
smaller size, such as the number of edges of a network, transfers to the clock. Together these
give the exponent arithmetic of the simulation: for `t = c * T`, with `q = ⌈t / ⌈log₂ (t + 2)⌉⌉`
blocks, the cost `3 ^ (K * q) * (t + 1) ^ d * 2 ^ (e * t / √⌊log₂ t⌋)` of enumerating the movement
schedules, building the networks and contracting them is `2 ^ O(T / √⌊log₂ T⌋)`
(`Nat.exists_three_pow_mul_le_two_pow_div_sqrt_log_two`).

The floors cost only constant factors: the natural scale is between the real scale
`n / √(log₂ n)` minus one and three times it, which is checked in the test suite.

## Main results

* `Nat.log_two_le_div_sqrt_log_two`: `⌊log₂ n⌋ ≤ n / √⌊log₂ n⌋`.
* `Nat.ceilDiv_clog_two_le`: `⌈n / ⌈log₂ (n + 2)⌉⌉ ≤ n / √⌊log₂ n⌋ + 1`.
* `Nat.mul_div_sqrt_log_two_le`: the scale of `c * n` is at most `c` times that of `n`, plus `c`.
* `Nat.div_sqrt_log_two_le_of_le`: the scale is monotone up to constants.
* `Nat.exists_three_pow_mul_le_two_pow_div_sqrt_log_two`: the cost of the counting simulation.
* `Nat.mul_two_pow_add_le_two_pow`, `Nat.mul_two_pow_div_sqrt_log_two_add_le`,
  `Nat.mul_add_one_pow_add_le_pow`: absorbing constants into exponential and polynomial bounds.
-/

public section

namespace Nat

/-- The divisor `√⌊log₂ n⌋` is positive from `n = 2` on. -/
theorem one_le_sqrt_log_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ sqrt (log 2 n) :=
  le_sqrt.2 (by rw [one_mul]; exact log_pos one_lt_two hn)

/-- The divisor `√⌊log₂ n⌋` is monotone. -/
theorem sqrt_log_two_mono : Monotone fun n => sqrt (log 2 n) :=
  fun _ _ h => sqrt_le_sqrt (log_mono_right h)

/-- `m ^ 3 ≤ 4 ^ m`. -/
private theorem cube_le_four_pow : ∀ m : ℕ, m ^ 3 ≤ 4 ^ m
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | m + 3 => by
    have ih := cube_le_four_pow (m + 2)
    have h : (m + 3) ^ 3 ≤ 4 * (m + 2) ^ 3 := by ring_nf; nlinarith
    calc (m + 3) ^ 3 ≤ 4 * (m + 2) ^ 3 := h
      _ ≤ 4 * 4 ^ (m + 2) := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (m + 3) := by ring

/-- `⌊log₂ n⌋ * √⌊log₂ n⌋ ≤ n`: with `L = ⌊log₂ n⌋`, `(L √L) ^ 2 ≤ L ^ 3 ≤ 4 ^ L ≤ n ^ 2`. -/
theorem log_two_mul_sqrt_log_two_le (n : ℕ) : log 2 n * sqrt (log 2 n) ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set L := log 2 n
  have h2L : 2 ^ L ≤ n := pow_log_le_self 2 hn.ne'
  have hsq : (L * sqrt L) ^ 2 ≤ (2 ^ L) ^ 2 := by
    calc (L * sqrt L) ^ 2 = L * L * (sqrt L * sqrt L) := by ring
      _ ≤ L * L * L := Nat.mul_le_mul_left _ (sqrt_le L)
      _ = L ^ 3 := by ring
      _ ≤ 4 ^ L := cube_le_four_pow L
      _ = (2 ^ L) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  exact ((Nat.pow_le_pow_iff_left (by norm_num)).1 hsq).trans h2L

/-- **The scale dominates the logarithm**: `⌊log₂ n⌋ ≤ n / √⌊log₂ n⌋`. -/
theorem log_two_le_div_sqrt_log_two (n : ℕ) : log 2 n ≤ n / sqrt (log 2 n) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · simp [log_of_lt hn]
  · exact (le_div_iff_mul_le (one_le_sqrt_log_two hn)).2 (log_two_mul_sqrt_log_two_le n)

/-- The scale is positive from `n = 2` on. -/
theorem one_le_div_sqrt_log_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ n / sqrt (log 2 n) :=
  (log_pos one_lt_two hn).trans_le (log_two_le_div_sqrt_log_two n)

/-- **Time blocks.** There are at most `n / √⌊log₂ n⌋ + 1` blocks of length `⌈log₂ (n + 2)⌉` in
`n` steps, since `√⌊log₂ n⌋ ≤ ⌈log₂ (n + 2)⌉`. -/
theorem ceilDiv_clog_two_le (n : ℕ) : n ⌈/⌉ clog 2 (n + 2) ≤ n / sqrt (log 2 n) + 1 := by
  have hb : 0 < clog 2 (n + 2) := clog_pos one_lt_two (by omega)
  rw [ceilDiv_le_iff hb]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact Nat.zero_le _
    · simp [show clog 2 3 = 2 by decide]
  · have hr := one_le_sqrt_log_two hn
    have hle : sqrt (log 2 n) ≤ clog 2 (n + 2) :=
      (sqrt_le_self _).trans ((log_mono_right (by omega : n ≤ n + 2)).trans (log_le_clog 2 _))
    calc n ≤ (n / sqrt (log 2 n) + 1) * sqrt (log 2 n) := by
          have := lt_div_mul_add (a := n) hr
          rw [add_mul, one_mul]
          omega
      _ ≤ _ := Nat.mul_le_mul_left _ hle

/-- Multiplying before dividing gains less than the multiplier: `c * n / r ≤ c * (n / r) + c`. -/
theorem mul_div_le_mul_div_add (c n r : ℕ) : c * n / r ≤ c * (n / r) + c := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  apply Nat.div_le_of_le_mul
  have := lt_div_mul_add (a := n) hr
  have h : n ≤ r * (n / r + 1) := by rw [mul_add, mul_one, mul_comm]; omega
  calc c * n ≤ c * (r * (n / r + 1)) := Nat.mul_le_mul_left _ h
    _ = r * (c * (n / r) + c) := by ring

/-- **Scaling.** The scale of `c * n` is at most `c` times the scale of `n`, plus `c`: the divisor
only grows. -/
theorem mul_div_sqrt_log_two_le (c n : ℕ) :
    c * n / sqrt (log 2 (c * n)) ≤ c * (n / sqrt (log 2 n)) + c := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · calc c * n / _ ≤ c * n := div_le_self _ _
      _ ≤ c * 1 := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := by omega
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have hr := one_le_sqrt_log_two hn
  calc c * n / sqrt (log 2 (c * n)) ≤ c * n / sqrt (log 2 n) :=
        div_le_div_left (sqrt_log_two_mono (Nat.le_mul_of_pos_left n hc)) hr
    _ ≤ c * (n / sqrt (log 2 n)) + c := mul_div_le_mul_div_add c n _

/-- **The scale is monotone up to constants**: `m ≤ n` gives
`m / √⌊log₂ m⌋ ≤ 2 * (n / √⌊log₂ n⌋) + 2`. When the divisors are within a factor `2` of each other
this is division by the smaller divisor; otherwise `m` is so much smaller than `n` that
`m * √⌊log₂ n⌋ ≤ n`. -/
theorem div_sqrt_log_two_le_of_le {m n : ℕ} (h : m ≤ n) :
    m / sqrt (log 2 m) ≤ 2 * (n / sqrt (log 2 n)) + 2 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · simp [log_of_lt hm]
  set a := sqrt (log 2 m)
  set b := sqrt (log 2 n)
  have ha : 1 ≤ a := one_le_sqrt_log_two hm
  have hab : a ≤ b := sqrt_log_two_mono h
  rcases le_or_gt b (2 * a) with hb | hb
  · calc m / a ≤ n / a := Nat.div_le_div_right h
      _ = 2 * n / (2 * a) := (Nat.mul_div_mul_left n a two_pos).symm
      _ ≤ 2 * n / b := Nat.div_le_div_left hb (ha.trans hab)
      _ ≤ 2 * (n / b) + 2 := mul_div_le_mul_div_add 2 n b
  · -- `m < 2 ^ ((a + 1) ^ 2)` and `2 ^ (b ^ 2) ≤ n`, with `(a + 1) ^ 2 + b ≤ b ^ 2`
    have hm2 : m < 2 ^ ((a + 1) * (a + 1)) :=
      (lt_pow_succ_log_self one_lt_two m).trans_le
        (Nat.pow_le_pow_right two_pos (lt_succ_sqrt (log 2 m)))
    have hn2 : 2 ^ (b * b) ≤ n :=
      (Nat.pow_le_pow_right two_pos (sqrt_le (log 2 n))).trans (pow_log_le_self 2 (by omega))
    have hexp : (a + 1) * (a + 1) + b ≤ b * b := by nlinarith
    have hmb : m * b ≤ n :=
      calc m * b ≤ 2 ^ ((a + 1) * (a + 1)) * 2 ^ b :=
            Nat.mul_le_mul hm2.le Nat.lt_two_pow_self.le
        _ = 2 ^ ((a + 1) * (a + 1) + b) := (pow_add _ _ _).symm
        _ ≤ 2 ^ (b * b) := Nat.pow_le_pow_right two_pos hexp
        _ ≤ n := hn2
    calc m / a ≤ m := Nat.div_le_self _ _
      _ ≤ n / b := (Nat.le_div_iff_mul_le (by omega)).2 hmb
      _ ≤ 2 * (n / b) + 2 := by omega

/-- **The cost of the counting simulation is `2 ^ O(T / √(log T))`** (#1833). For `t = c * T`,
time blocks of length `b = ⌈log₂ (t + 2)⌉` and `q = ⌈t / b⌉` blocks, the number `3 ^ (K * q)` of
movement schedules of `K` heads, a polynomial `(t + 1) ^ d` and a contraction cost
`2 ^ (e * t / √⌊log₂ t⌋)` multiply to at most `2 ^ (C * T / √⌊log₂ T⌋)` from `T = 2` on, for a
constant `C` depending only on `K`, `c`, `d` and `e`. -/
theorem exists_three_pow_mul_le_two_pow_div_sqrt_log_two (K c d e : ℕ) : ∃ C, ∀ T, 2 ≤ T →
    3 ^ (K * (c * T ⌈/⌉ clog 2 (c * T + 2))) * (c * T + 1) ^ d *
        2 ^ (e * (c * T) / sqrt (log 2 (c * T))) ≤
      2 ^ (C * T / sqrt (log 2 T)) := by
  refine ⟨(2 * K + d + e) * (2 * c + 1), fun T hT => ?_⟩
  set S := T / sqrt (log 2 T)
  set t := c * T
  have hS : 1 ≤ S := one_le_div_sqrt_log_two hT
  -- the scale of `t` is at most `2 c S`
  have ht : t / sqrt (log 2 t) ≤ c * S + c := mul_div_sqrt_log_two_le c T
  have hcS : c * S + c ≤ 2 * c * S := by nlinarith
  -- the number of movement schedules
  have hq : t ⌈/⌉ clog 2 (t + 2) ≤ (2 * c + 1) * S := by
    have := ceilDiv_clog_two_le t
    nlinarith
  have h3 : 3 ^ (K * (t ⌈/⌉ clog 2 (t + 2))) ≤ 2 ^ (2 * K * ((2 * c + 1) * S)) := by
    calc 3 ^ (K * (t ⌈/⌉ clog 2 (t + 2))) ≤ 4 ^ (K * (t ⌈/⌉ clog 2 (t + 2))) :=
          Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (2 * (K * (t ⌈/⌉ clog 2 (t + 2)))) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      _ ≤ 2 ^ (2 * K * ((2 * c + 1) * S)) := Nat.pow_le_pow_right (by norm_num) (by
          rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hq)
  -- the polynomial factor
  have hpoly : (t + 1) ^ d ≤ 2 ^ (d * ((2 * c + 1) * S)) := by
    have hlog : log 2 t + 1 ≤ (2 * c + 1) * S := by
      have := log_two_le_div_sqrt_log_two t
      nlinarith
    calc (t + 1) ^ d ≤ (2 ^ (log 2 t + 1)) ^ d :=
          Nat.pow_le_pow_left (lt_pow_succ_log_self one_lt_two t) d
      _ = 2 ^ (d * (log 2 t + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (d * ((2 * c + 1) * S)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hlog)
  -- the contraction factor
  have hcon : 2 ^ (e * t / sqrt (log 2 t)) ≤ 2 ^ (e * ((2 * c + 1) * S)) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := mul_div_le_mul_div_add e t (sqrt (log 2 t))
    nlinarith
  calc 3 ^ (K * (t ⌈/⌉ clog 2 (t + 2))) * (t + 1) ^ d * 2 ^ (e * t / sqrt (log 2 t))
      ≤ 2 ^ (2 * K * ((2 * c + 1) * S)) * 2 ^ (d * ((2 * c + 1) * S)) *
          2 ^ (e * ((2 * c + 1) * S)) := Nat.mul_le_mul (Nat.mul_le_mul h3 hpoly) hcon
    _ = 2 ^ ((2 * K + d + e) * (2 * c + 1) * S) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ ((2 * K + d + e) * (2 * c + 1) * T / sqrt (log 2 T)) :=
          Nat.pow_le_pow_right (by norm_num) (mul_div_le_mul_div_assoc _ _ _)

/-- A constant factor and an additive constant are absorbed by a positive exponent:
`a * 2 ^ (c * x) + b ≤ 2 ^ ((a + b + c) * x)` for `1 ≤ x`. -/
theorem mul_two_pow_add_le_two_pow {a b c x : ℕ} (hx : 1 ≤ x) :
    a * 2 ^ (c * x) + b ≤ 2 ^ ((a + b + c) * x) := by
  have h1 : 1 ≤ 2 ^ (c * x) := Nat.one_le_two_pow
  have hab : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have hab' : 2 ^ (a + b) ≤ 2 ^ ((a + b) * x) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc a * 2 ^ (c * x) + b ≤ (a + b) * 2 ^ (c * x) := by nlinarith
    _ ≤ 2 ^ ((a + b) * x) * 2 ^ (c * x) := Nat.mul_le_mul_right _ (hab.le.trans hab')
    _ = 2 ^ ((a + b + c) * x) := by rw [← pow_add]; ring_nf

/-- A constant factor and an additive constant are absorbed into the constant of
`2 ^ O(T / √⌊log₂ T⌋)` from `T = 2` on. -/
theorem mul_two_pow_div_sqrt_log_two_add_le {a b C T : ℕ} (hT : 2 ≤ T) :
    a * 2 ^ (C * T / sqrt (log 2 T)) + b ≤
      2 ^ ((a + b + 1) * (C + 1) * T / sqrt (log 2 T)) := by
  set x := (C + 1) * T / sqrt (log 2 T)
  have hx : 1 ≤ x :=
    (one_le_div_sqrt_log_two hT).trans
      ((Nat.le_mul_of_pos_left _ (Nat.succ_pos C)).trans (mul_div_le_mul_div_assoc _ _ _))
  have hCx : C * T / sqrt (log 2 T) ≤ 1 * x := by
    rw [one_mul]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ C))
  calc a * 2 ^ (C * T / sqrt (log 2 T)) + b ≤ a * 2 ^ (1 * x) + b := by
        gcongr
    _ ≤ 2 ^ ((a + b + 1) * x) := mul_two_pow_add_le_two_pow hx
    _ ≤ 2 ^ ((a + b + 1) * (C + 1) * T / sqrt (log 2 T)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        rw [mul_assoc]
        exact mul_div_le_mul_div_assoc _ _ _

/-- A constant factor and an additive constant are absorbed by the degree from `n = 2` on:
`a * (n + 1) ^ d + b ≤ n ^ (a + b + 2 * d)`. -/
theorem mul_add_one_pow_add_le_pow {a b d n : ℕ} (hn : 2 ≤ n) :
    a * (n + 1) ^ d + b ≤ n ^ (a + b + 2 * d) := by
  have hsq : (n + 1) ^ d ≤ n ^ (2 * d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) d
  have h1 : 1 ≤ n ^ (2 * d) := Nat.one_le_pow _ _ (by omega)
  have hab : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have hab' : 2 ^ (a + b) ≤ n ^ (a + b) := Nat.pow_le_pow_left hn _
  calc a * (n + 1) ^ d + b ≤ (a + b) * n ^ (2 * d) := by nlinarith
    _ ≤ n ^ (a + b) * n ^ (2 * d) := Nat.mul_le_mul_right _ (hab.le.trans hab')
    _ = n ^ (a + b + 2 * d) := by rw [← pow_add]

end Nat
