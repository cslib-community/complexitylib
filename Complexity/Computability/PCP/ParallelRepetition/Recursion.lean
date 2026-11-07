/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The recursion behind the parallel repetition theorem

Holenstein's proof of the parallel repetition theorem picks coordinates one at a time. With `p_m`
the probability of winning the `m` coordinates picked so far, Lemma 6.5 bounds each step by
`p_{m+1} ≤ p_m (v + C √((m L + ln (1 / p_m)) / (n - m)))`, where `v` is the value of the game and
`L` stands for `ln (|A| |B|)`. Lemma 7.1 turns this recursion into an exponential bound
[Holenstein, Lemma 7.1][Holenstein2009]: while `12 C² m L ≤ (1 - v)² (n - m)`, the probability
`p_m` is at most `((1 + v) / 2)^m` (`le_pow_of_step`), and therefore the probability of winning all
`n` coordinates is at most `((1 + v) / 2)^⌊(1 - v)² n / (13 C² L)⌋`
(`le_pow_floor_of_step`). Holenstein's Lemma 7.1 is stated with `c = C²` inside the root and
`c ≥ 12`; his proof of Theorem 2.5 applies it with `C = 15` by (7.6), and his (7.4) ignores the
rounding of the number of steps, which the floor here records.
This file is the analytic part of the theorem only: it assumes the recursion, which the
embedding lemmas establish.

## Main results

* `Cslib.PCP.ParallelRepetition.le_pow_of_step`: the induction in the proof of Lemma 7.1.
* `Cslib.PCP.ParallelRepetition.le_pow_floor_of_step`: the resulting bound on `p_n`.
* `Cslib.PCP.ParallelRepetition.le_two_mul_rpow_of_step`: the bound in Holenstein's exponential
  form, `p_n ≤ 2 (1 - (1 - v)³ / (26 C²))^{n / L}`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.PCP.ParallelRepetition

variable {v C L : ℝ} {n : ℕ} {p : ℕ → ℝ}

/-- A nonincreasing sequence starting at `1` stays in `[0, 1]`. -/
theorem le_one_of_antitone (hp0 : p 0 = 1) (hmono : ∀ m, p (m + 1) ≤ p m) : ∀ m, p m ≤ 1
  | 0 => hp0.le
  | m + 1 => (hmono m).trans (le_one_of_antitone hp0 hmono m)

/-- For `m > 0`, `1 ≤ L`, `0 ≤ v < 1`, `((1 + v) / 2) ^ (m + 1) ≤ p m`, and
`12 * C ^ 2 * (m + 1) * L ≤ (1 - v) ^ 2 * (n - (m + 1))`, the square-root error term in
Holenstein's step is at most `(1 - v) / 2`: `ln (1 / p_m) ≤ (m + 1) ln 2 ≤ m + 1`, so the numerator
is at most `3 m L`. -/
private theorem mul_sqrt_le_one_sub_div_two (hv : 0 ≤ v) (hv1 : v < 1) (hL : 1 ≤ L)
    {m : ℕ} (hm : 0 < m) (hmn : (m : ℝ) + 1 ≤ n)
    (H : 12 * C ^ 2 * ((m : ℝ) + 1) * L ≤ (1 - v) ^ 2 * ((n : ℝ) - ((m : ℝ) + 1)))
    (hsmall : ((1 + v) / 2) ^ (m + 1) ≤ p m) :
    C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)) ≤ (1 - v) / 2 := by
  have hb0 : 0 < (1 + v) / 2 := by linarith
  have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpm : 0 < p m := lt_of_lt_of_le (pow_pos hb0 _) hsmall
  -- `ln (1 / p_m) ≤ (m + 1) ln 2 ≤ m + 1`.
  have hlog : Real.log (1 / p m) ≤ m + 1 := by
    have h1 : Real.log (1 / p m) ≤ Real.log (1 / ((1 + v) / 2) ^ (m + 1)) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le (pow_pos hb0 _) hsmall)
    have h2 : Real.log (1 / ((1 + v) / 2) ^ (m + 1)) ≤ Real.log (2 ^ (m + 1)) := by
      refine Real.log_le_log (by positivity) ?_
      rw [one_div, ← inv_pow]
      gcongr
      rw [inv_le_comm₀ hb0 two_pos]
      linarith
    have h3 : Real.log ((2 : ℝ) ^ (m + 1)) ≤ m + 1 := by
      rw [Real.log_pow]
      push_cast
      nlinarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)]
    linarith
  have harg : (m * L + Real.log (1 / p m)) / (n - m) ≤ 3 * m * L / (n - m) :=
    div_le_div_of_nonneg_right (by nlinarith) (by linarith)
  calc C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m))
      ≤ |C| * Real.sqrt (3 * m * L / (n - m)) :=
        mul_le_mul (le_abs_self C) (Real.sqrt_le_sqrt harg) (Real.sqrt_nonneg _) (abs_nonneg C)
    _ = Real.sqrt (C ^ 2 * (3 * m * L / (n - m))) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (((1 - v) / 2) ^ 2) := by
        gcongr
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
    _ = (1 - v) / 2 := Real.sqrt_sq (by linarith)

/-- **The induction of Holenstein's Lemma 7.1** [Holenstein, proof of Lemma 7.1][Holenstein2009]: if
`p_0 = 1`, `p` is nonnegative and nonincreasing, and every step satisfies
`p_{m+1} ≤ p_m (v + C √((m L + ln (1 / p_m)) / (n - m)))`, then
`p_m ≤ ((1 + v) / 2)^m` as long as `12 C² m L ≤ (1 - v)² (n - m)`. -/
theorem le_pow_of_step (hv : 0 ≤ v) (hv1 : v ≤ 1) (hL : 1 ≤ L) (hp0 : p 0 = 1)
    (hnn : ∀ m, 0 ≤ p m) (hmono : ∀ m, p (m + 1) ≤ p m)
    (hstep : ∀ m < n, p (m + 1) ≤
      p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)))) :
    ∀ m : ℕ, 12 * C ^ 2 * m * L ≤ (1 - v) ^ 2 * (n - m) → p m ≤ ((1 + v) / 2) ^ m
  | 0, _ => by simp [hp0]
  | m + 1, H => by
    have hle1 := le_one_of_antitone hp0 hmono
    have hb0 : 0 < (1 + v) / 2 := by linarith
    -- If `v = 1` the bound is `1`.
    rcases hv1.lt_or_eq with hv1' | hv1'
    swap
    · rw [hv1']
      norm_num
      exact hle1 _
    have hvpos : 0 < 1 - v := by linarith
    push_cast at H
    have hmn : (m : ℝ) + 1 ≤ n := by
      by_contra! hlt
      have : (1 - v) ^ 2 * ((n : ℝ) - (m + 1)) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) (by linarith)
      linarith [(by positivity : (0 : ℝ) ≤ 12 * C ^ 2 * (m + 1) * L)]
    have hmn' : m < n := by exact_mod_cast (show (m : ℝ) < n by linarith)
    have Hm : 12 * C ^ 2 * m * L ≤ (1 - v) ^ 2 * (n - m) := by
      nlinarith [sq_nonneg C, sq_nonneg (1 - v)]
    have IH := le_pow_of_step hv hv1 hL hp0 hnn hmono hstep m Hm
    by_cases hsmall : p m < ((1 + v) / 2) ^ (m + 1)
    · exact (hmono m).trans hsmall.le
    push Not at hsmall
    have hstepm := hstep m hmn'
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- The first step: `p_1 ≤ v`.
      simp only [hp0, Nat.cast_zero, zero_mul, div_one, Real.log_one, add_zero, zero_div,
        Real.sqrt_zero, mul_zero, one_mul] at hstepm
      simp only [zero_add, pow_one]
      linarith
    · have hsq := mul_sqrt_le_one_sub_div_two hv hv1' hL hm hmn H hsmall
      calc p (m + 1) ≤ p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m))) :=
            hstepm
        _ ≤ p m * ((1 + v) / 2) := by
            have := hnn m
            gcongr
            linarith
        _ ≤ ((1 + v) / 2) ^ m * ((1 + v) / 2) := by gcongr
        _ = ((1 + v) / 2) ^ (m + 1) := (pow_succ _ _).symm

/-- **The bound of Holenstein's Lemma 7.1** [Holenstein, Lemma 7.1, (7.4)][Holenstein2009]: under
the recursion of `le_pow_of_step` with `C ≥ 1`, `p_n ≤ ((1 + v) / 2)^⌊(1 - v)² n / (13 C² L)⌋`. -/
theorem le_pow_floor_of_step (hv : 0 ≤ v) (hv1 : v ≤ 1) (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp0 : p 0 = 1) (hnn : ∀ m, 0 ≤ p m) (hmono : ∀ m, p (m + 1) ≤ p m)
    (hstep : ∀ m < n, p (m + 1) ≤
      p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)))) :
    p n ≤ ((1 + v) / 2) ^ ⌊(1 - v) ^ 2 * n / (13 * C ^ 2 * L)⌋₊ := by
  set M := ⌊(1 - v) ^ 2 * n / (13 * C ^ 2 * L)⌋₊
  have hK : 0 < 13 * C ^ 2 * L := by positivity
  have hx : 0 ≤ (1 - v) ^ 2 * n / (13 * C ^ 2 * L) := by positivity
  have hM : (M : ℝ) ≤ (1 - v) ^ 2 * n / (13 * C ^ 2 * L) := Nat.floor_le hx
  have hM' : 13 * C ^ 2 * L * M ≤ (1 - v) ^ 2 * n := by
    rw [le_div_iff₀ hK] at hM
    linarith
  have hsq1 : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hCL : 1 ≤ C ^ 2 * L := by nlinarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hcond : 12 * C ^ 2 * M * L ≤ (1 - v) ^ 2 * (n - M) := by nlinarith
  have hMn : M ≤ n := by
    have : (M : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  -- `p` is nonincreasing, so `p_n ≤ p_M`.
  have hanti : ∀ k, p (M + k) ≤ p M := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => exact (hmono _).trans ih
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hMn
  rw [hk]
  exact (hanti k).trans (le_pow_of_step hv hv1 hL hp0 hnn hmono hstep M hcond)

/-- **The bound of Holenstein's Theorem 2.5, in exponential form** [Holenstein, Lemma 7.1, (7.2)
and (7.7)][Holenstein2009]: under the recursion of `le_pow_of_step` with `C ≥ 1`,
`p_n ≤ 2 (1 - (1 - v)³ / (26 C²))^{n / L}`. The factor `2` accounts for rounding the number of
steps down; Holenstein's `6000` corresponds to `26 C²` with `C = 15` (`26 · 225 = 5850`). -/
theorem le_two_mul_rpow_of_step (hv : 0 ≤ v) (hv1 : v ≤ 1) (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp0 : p 0 = 1) (hnn : ∀ m, 0 ≤ p m) (hmono : ∀ m, p (m + 1) ≤ p m)
    (hstep : ∀ m < n, p (m + 1) ≤
      p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)))) :
    p n ≤ 2 * (1 - (1 - v) ^ 3 / (26 * C ^ 2)) ^ ((n : ℝ) / L) := by
  set b := (1 + v) / 2
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := by simp only [b]; linarith
  have hbhalf : 1 / 2 ≤ b := by simp only [b]; linarith
  set a := (1 - v) ^ 2 / (13 * C ^ 2)
  set x := (1 - v) ^ 2 * n / (13 * C ^ 2 * L)
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
  have hx : x = a * (n / L) := by
    simp only [x, a]
    field_simp
  have hfloor := le_pow_floor_of_step hv hv1 hC hL hp0 hnn hmono hstep
  -- Round the number of steps down at the cost of a factor `2`.
  have hround : b ^ ⌊x⌋₊ ≤ 2 * b ^ x := by
    have hle : x - 1 ≤ (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
    have h1 : b ^ ⌊x⌋₊ = b ^ ((⌊x⌋₊ : ℕ) : ℝ) := (Real.rpow_natCast b _).symm
    have h2 : b ^ ((⌊x⌋₊ : ℕ) : ℝ) ≤ b ^ (x - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hle
    have h3 : b ^ (x - 1) = b ^ x / b := Real.rpow_sub_one hb0.ne' x
    rw [h1]
    refine h2.trans (h3.le.trans ?_)
    rw [div_le_iff₀ hb0]
    have := Real.rpow_nonneg hb0.le x
    nlinarith
  -- Bernoulli's inequality for the exponent `a ∈ [0, 1]`.
  have hbern : b ^ a ≤ 1 - (1 - v) ^ 3 / (26 * C ^ 2) := by
    have h := rpow_one_add_le_one_add_mul_self (s := -((1 - v) / 2)) (by linarith) ha0 ha1
    have hb : 1 + -((1 - v) / 2) = b := by simp only [b]; ring
    rw [hb] at h
    refine h.trans (le_of_eq ?_)
    simp only [a]
    field_simp
    ring
  calc p n ≤ b ^ ⌊x⌋₊ := hfloor
    _ ≤ 2 * b ^ x := hround
    _ = 2 * (b ^ a) ^ ((n : ℝ) / L) := by rw [hx, Real.rpow_mul hb0.le]
    _ ≤ 2 * (1 - (1 - v) ^ 3 / (26 * C ^ 2)) ^ ((n : ℝ) / L) := by
        gcongr

end Cslib.PCP.ParallelRepetition
