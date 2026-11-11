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
`p_m` is at most `((1 + v) / 2)^m`, and therefore the probability of winning all
`n` coordinates is at most `((1 + v) / 2)^⌊(1 - v)² n / (13 C² L)⌋`
(`le_pow_floor_of_step`). Holenstein's Lemma 7.1 is stated with `c = C²` inside the root and
`c ≥ 12`; his proof of Theorem 2.5 applies it with `C = 15` by (7.6), and his (7.4) ignores the
rounding of the number of steps, which the floor here records.

The induction itself (`le_pow_of_step`) works for any ratio `b ≥ v`. With the ratio
`1 - (1 - v) / 5` in place of `(1 + v) / 2`, `le_rpow_of_step` obtains Holenstein's final bound
`p_n ≤ (1 - (1 - v)³ / 6000)^{n / L}` exactly, rounding included, for every `0 ≤ C ≤ 21`. This
sharpens the bookkeeping of Holenstein's (7.4) and (7.7); it is not the paper's argument.

This file is the analytic part of the theorem only: it assumes the recursion, which the
embedding lemmas establish.

## Main results

* `Cslib.PCP.ParallelRepetition.le_pow_of_step`: the induction in the proof of Lemma 7.1, for an
  arbitrary ratio.
* `Cslib.PCP.ParallelRepetition.le_pow_floor_of_step`: the resulting bound on `p_n` with
  Holenstein's ratio.
* `Cslib.PCP.ParallelRepetition.le_two_mul_rpow_of_step`: the bound in Holenstein's exponential
  form for every `C ≥ 1`, `p_n ≤ 2 (1 - (1 - v)³ / (26 C²))^{n / L}`.
* `Cslib.PCP.ParallelRepetition.le_rpow_of_step`: the bound of Theorem 2.5,
  `p_n ≤ (1 - (1 - v)³ / 6000)^{n / L}`, for `0 ≤ C ≤ 21`.

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

/-- The first step of the recursion: since `p_0 = 1`, the error term vanishes and `p_1 ≤ v`. -/
private theorem le_of_step_zero (hp0 : p 0 = 1) (hn : 0 < n)
    (hstep : ∀ m < n, p (m + 1) ≤
      p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)))) :
    p 1 ≤ v := by
  simpa [hp0] using hstep 0 hn

/-- **The induction of Holenstein's Lemma 7.1**, for any ratio `b ≥ v`
[Holenstein, proof of Lemma 7.1][Holenstein2009]: if `p_0 = 1`, `p` is nonnegative and
nonincreasing, and every step satisfies
`p_{m+1} ≤ p_m (v + C √((m L + ln (1 / p_m)) / (n - m)))`, then `p_M ≤ b^M` for `M ≤ n`, provided
that `C² (m L + (m + 1) ln (1 / b)) ≤ (b - v)² (n - m)` at every step `0 < m < M` with
`b^{m+1} ≤ p_m`. At such a step `ln (1 / p_m) ≤ (m + 1) ln (1 / b)`, so the error term is at most
`b - v`; at the other steps `p_{m+1} ≤ p_m < b^{m+1}` already, and the first step gives
`p_1 ≤ v`. Holenstein's induction uses `b = (1 + v) / 2` (`le_pow_floor_of_step`). -/
theorem le_pow_of_step {b : ℝ} (hb : 0 < b) (hvb : v ≤ b) (hp0 : p 0 = 1)
    (hnn : ∀ m, 0 ≤ p m) (hmono : ∀ m, p (m + 1) ≤ p m)
    (hstep : ∀ m < n, p (m + 1) ≤
      p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m))))
    {M : ℕ} (hMn : M ≤ n)
    (hcond : ∀ m : ℕ, 0 < m → m < M → b ^ (m + 1) ≤ p m →
      C ^ 2 * (m * L + (m + 1) * Real.log (1 / b)) ≤ (b - v) ^ 2 * (n - m)) :
    p M ≤ b ^ M := by
  induction M with
  | zero => simp [hp0]
  | succ m ih =>
    have hmn : m < n := by omega
    have IH := ih (by omega) fun k hk hkm => hcond k hk (by omega)
    by_cases hsmall : p m < b ^ (m + 1)
    · exact (hmono m).trans hsmall.le
    push Not at hsmall
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using (le_of_step_zero hp0 (by omega) hstep).trans hvb
    have hnm : (0 : ℝ) < n - m := by
      have : (m : ℝ) < n := by exact_mod_cast hmn
      linarith
    -- `ln (1 / p_m) ≤ (m + 1) ln (1 / b)`.
    have hlog : Real.log (1 / p m) ≤ (m + 1) * Real.log (1 / b) := by
      have h := Real.log_le_log (pow_pos hb _) hsmall
      rw [Real.log_pow] at h
      push_cast at h
      simp only [one_div, Real.log_inv]
      linarith
    have herr : C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)) ≤ b - v :=
      calc C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m))
          ≤ |C| * Real.sqrt ((m * L + (m + 1) * Real.log (1 / b)) / (n - m)) :=
            mul_le_mul (le_abs_self C)
              (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hnm.le))
              (Real.sqrt_nonneg _) (abs_nonneg C)
        _ = Real.sqrt (C ^ 2 * ((m * L + (m + 1) * Real.log (1 / b)) / (n - m))) := by
            rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((b - v) ^ 2) := by
            gcongr
            rw [mul_div_assoc', div_le_iff₀ hnm]
            exact hcond m hm (by omega) hsmall
        _ = b - v := Real.sqrt_sq (by linarith)
    calc p (m + 1) ≤ p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m))) :=
          hstep m hmn
      _ ≤ p m * b := mul_le_mul_of_nonneg_left (by linarith) (hnn m)
      _ ≤ b ^ m * b := mul_le_mul_of_nonneg_right IH hb.le
      _ = b ^ (m + 1) := (pow_succ _ _).symm

/-- **The bound of Holenstein's Lemma 7.1** [Holenstein, Lemma 7.1, (7.4)][Holenstein2009]: under
the recursion of `le_pow_of_step` with `C ≥ 1`, `p_n ≤ ((1 + v) / 2)^⌊(1 - v)² n / (13 C² L)⌋`.
The ratio is Holenstein's `(1 + v) / 2`, and the induction runs while
`12 C² m L ≤ (1 - v)² (n - m)`. -/
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
  refine (antitone_nat_of_succ_le hmono hMn).trans
    (le_pow_of_step (by linarith) (by linarith) hp0 hnn hmono hstep hMn fun k hk hkM _ => ?_)
  -- `ln (2 / (1 + v)) ≤ 1` and `k + 1 ≤ 2 k ≤ 2 k L`, so the left side is at most `3 C² M L`.
  have hlog : Real.log (1 / ((1 + v) / 2)) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 / ((1 + v) / 2) by positivity)
    have : 1 / ((1 + v) / 2) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM.le
  have h1 : (k : ℝ) * L + (k + 1) * Real.log (1 / ((1 + v) / 2)) ≤ 3 * (M * L) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ k + 1),
      mul_le_mul_of_nonneg_right hkM' (by linarith : (0 : ℝ) ≤ L),
      mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ k)]
  calc C ^ 2 * (k * L + (k + 1) * Real.log (1 / ((1 + v) / 2)))
      ≤ C ^ 2 * (3 * (M * L)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg C)
    _ ≤ ((1 + v) / 2 - v) ^ 2 * (n - k) := by
        nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_left hkM' (n : ℝ)) (sq_nonneg (1 - v))]

/-- **The bound of Holenstein's Theorem 2.5, in exponential form** [Holenstein, Lemma 7.1, (7.2)
and (7.7)][Holenstein2009]: under the recursion of `le_pow_of_step` with `C ≥ 1`,
`p_n ≤ 2 (1 - (1 - v)³ / (26 C²))^{n / L}`. The factor `2` accounts for rounding the number of
steps down; Holenstein's `6000` corresponds to `26 C²` with `C = 15` (`26 · 225 = 5850`). For
`0 ≤ C ≤ 21`, `le_rpow_of_step` gives the bound with the constant `6000` and no factor `2`. -/
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

/-- **The bound of Holenstein's Theorem 2.5 from the recursion**: under the recursion of
`le_pow_of_step` with `0 ≤ C ≤ 21`, `p_n ≤ (1 - (1 - v)³ / 6000)^{n / L}`. This is the bound that
Holenstein derives from Lemma 7.1 in (7.7) [Holenstein, Lemma 7.1 and (7.4)–(7.7)][Holenstein2009],
with the rounding accounted for.

The proof sharpens Holenstein's bookkeeping in (7.4) and (7.7) instead of following it; the paper
neither states nor proves this lemma. His (7.4) raises `(1 + v) / 2` to the power
`(1 - v)² n / (13 c ℓ)` and ignores that the number of steps is an integer; accounting for that
rounding with his ratio costs the factor `2` of `le_two_mul_rpow_of_step`. Here, with `u = 1 - v`:

* if `u² n / L ≤ 6000`, then already `p_n ≤ p_1 ≤ v` lies below the bound;
* otherwise `le_pow_of_step` runs `⌊u² n / (1000 L)⌋ ≥ (u² / 1200) (n / L)` steps with the
  ratio `b = 1 - u / 5`, and Bernoulli's inequality gives `b^{u² / 1200} ≤ 1 - u³ / 6000`. A step
  with `b^{m+1} ≤ p_m ≤ v ≤ b^5` has `m ≥ 4`, so the induction needs only
  `(25 / 16) (21 / 16) C² + 1 ≤ 1000`, which holds for `C ≤ 21`.

The range covers Holenstein's constant `C = 15` of (7.6), and also `C = 27 / √2 ≈ 19.09`. The
library's Corollary 5.3, `Cslib.Probability.CorrelatedSampling.isEmbeddable_diag_of_dist_le`, has
the constant `7 ε₁ + 2 ε₂` where Holenstein's has `3 ε₁ + 2 ε₂`. In his derivation of (6.2) and
(7.6), `ε₁` and `ε₂` each sum to at most `3 ε_Tot` by (6.15) and (6.16), so this turns
`15 = 3 (3 + 2)` into `27 = 3 (7 + 2)`. The factor `1 / √2` comes from the library's Lemma 4.1,
which bounds the sum of squared distances by `ln (1 / Pr[W]) / 2` in nats where Holenstein's (4.1)
has `log₂ (1 / Pr[W])`. -/
theorem le_rpow_of_step (hv : 0 ≤ v) (hv1 : v ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ 21) (hL : 1 ≤ L)
    (hp0 : p 0 = 1) (hnn : ∀ m, 0 ≤ p m) (hmono : ∀ m, p (m + 1) ≤ p m)
    (hstep : ∀ m < n, p (m + 1) ≤
      p m * (v + C * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)))) :
    p n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / L) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hp0]
  have hanti : Antitone p := antitone_nat_of_succ_le hmono
  have hp1 : p 1 ≤ v := le_of_step_zero hp0 hn hstep
  set u := 1 - v with hu
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hu2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0 hu1
  set t := (n : ℝ) / L with ht
  have hL0 : 0 < L := by linarith
  have ht0 : 0 ≤ t := by positivity
  have htL : t * L = n := by
    rw [ht]
    field_simp
  have hr0 : 0 < 1 - u ^ 3 / 6000 := by nlinarith [pow_le_one₀ hu0 hu1 (n := 3)]
  have hr1 : 1 - u ^ 3 / 6000 ≤ 1 := by nlinarith [pow_nonneg hu0 3]
  rcases le_or_gt (u ^ 2 * t) 6000 with hA | hB
  · -- Few steps: `p_n ≤ p_1 ≤ v = 1 - u` is already below the bound.
    calc p n ≤ p 1 := hanti hn
      _ ≤ 1 - u := by linarith
      _ ≤ (1 - u ^ 3 / 6000) ^ t := by
        rcases le_total t 1 with ht1 | ht1
        · calc 1 - u ≤ 1 - u ^ 3 / 6000 := by nlinarith [mul_le_mul_of_nonneg_left hu2 hu0]
            _ = (1 - u ^ 3 / 6000) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (1 - u ^ 3 / 6000) ^ t := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ht1
        · -- Bernoulli's inequality for the exponent `t ≥ 1`.
          refine le_trans ?_ (one_add_mul_self_le_rpow_one_add (s := -(u ^ 3 / 6000))
            (by linarith) ht1)
          nlinarith [mul_le_mul_of_nonneg_left hA hu0]
  -- Many steps: run the induction with the ratio `b = 1 - u / 5`.
  set b := 1 - u / 5 with hb
  have hu_pos : 0 < u := by
    rcases hu0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hB
      norm_num at hB
  have hb0 : 0 < b := by linarith
  have hb1 : b < 1 := by linarith
  -- `v = 1 - u ≤ (1 - u / 5)^5`, by Bernoulli's inequality.
  have hb5 : 1 - u ≤ b ^ 5 := by
    have h := one_add_mul_le_pow (a := -(u / 5)) (by linarith) 5
    rw [← sub_eq_add_neg, ← hb] at h
    push_cast at h
    linarith
  have hlogb : Real.log (1 / b) ≤ 1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 / b by positivity)
    have : 1 / b ≤ 5 / 4 := by
      rw [div_le_iff₀ hb0]
      linarith
    linarith
  set M := ⌊u ^ 2 * t / 1000⌋₊
  have hMle : (M : ℝ) ≤ u ^ 2 * t / 1000 := Nat.floor_le (by positivity)
  have hMgt : u ^ 2 * t / 1000 < M + 1 := Nat.lt_floor_add_one _
  have hML : 1000 * (M * L) ≤ u ^ 2 * n :=
    calc 1000 * (M * L) ≤ 1000 * (u ^ 2 * t / 1000 * L) := by gcongr
      _ = u ^ 2 * n := by rw [← htL]; ring
  have hMn : M ≤ n := by
    have htn : t ≤ n := div_le_self (Nat.cast_nonneg n) hL
    have : (M : ℝ) ≤ n := by nlinarith [mul_le_mul_of_nonneg_right hu2 ht0]
    exact_mod_cast this
  have hpM := le_pow_of_step hb0 (by linarith) hp0 hnn hmono hstep hMn fun m hm hmM hbm => by
    -- A step that needs the error bound has `m ≥ 4`, because `p_m ≤ p_1 ≤ v ≤ b^5`.
    have h5 : b ^ (m + 1) ≤ b ^ 5 := hbm.trans ((hanti hm).trans (hp1.trans (by linarith)))
    have hm4 : (4 : ℝ) ≤ m := by
      have := (pow_le_pow_iff_right_of_lt_one₀ hb0 hb1).1 h5
      exact_mod_cast (show 4 ≤ m by omega)
    have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM.le
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hmL : (m : ℝ) ≤ m * L := le_mul_of_one_le_right hm0 hL
    have hX : (m : ℝ) * L + (m + 1) * Real.log (1 / b) ≤ 21 / 16 * (m * L) := by
      linarith [mul_le_mul_of_nonneg_left hlogb (by positivity : (0 : ℝ) ≤ m + 1)]
    have hmn : 1000 * (m * L) ≤ u ^ 2 * n :=
      le_trans (by gcongr) hML
    have hum : u ^ 2 * m ≤ m * L := by
      linarith [mul_le_mul_of_nonneg_right hu2 hm0]
    have hC2 : C ^ 2 ≤ 441 := (pow_le_pow_left₀ hC0 hC 2).trans_eq (by norm_num)
    have hbv : (b - v) ^ 2 * (n - m) = 16 / 25 * (u ^ 2 * n) - 16 / 25 * (u ^ 2 * m) := by
      rw [show b - v = 4 * u / 5 by linarith]
      ring
    calc C ^ 2 * (m * L + (m + 1) * Real.log (1 / b))
        ≤ C ^ 2 * (21 / 16 * (m * L)) := mul_le_mul_of_nonneg_left hX (sq_nonneg C)
      _ ≤ 441 * (21 / 16 * (m * L)) := mul_le_mul_of_nonneg_right hC2 (by positivity)
      _ ≤ (b - v) ^ 2 * (n - m) := by
          rw [hbv]
          linarith
  -- The number of steps is at least `u² t / 1200`, since `u² t > 6000`.
  have hMx : u ^ 2 / 1200 * t ≤ M := by linarith
  have hbern : b ^ (u ^ 2 / 1200) ≤ 1 - u ^ 3 / 6000 := by
    have h := rpow_one_add_le_one_add_mul_self (s := -(u / 5)) (by linarith)
      (by positivity : 0 ≤ u ^ 2 / 1200) (by linarith)
    rw [← sub_eq_add_neg, ← hb] at h
    refine h.trans (le_of_eq ?_)
    ring
  calc p n ≤ p M := hanti hMn
    _ ≤ b ^ M := hpM
    _ = b ^ (M : ℝ) := (Real.rpow_natCast b M).symm
    _ ≤ b ^ (u ^ 2 / 1200 * t) := Real.rpow_le_rpow_of_exponent_ge hb0 hb1.le hMx
    _ = (b ^ (u ^ 2 / 1200)) ^ t := Real.rpow_mul hb0.le _ _
    _ ≤ (1 - u ^ 3 / 6000) ^ t := Real.rpow_le_rpow (Real.rpow_nonneg hb0.le _) hbern ht0

end Cslib.PCP.ParallelRepetition
