/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Bonami
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Foundations.Data.Finset.Holder
import Complexity.Probability.KWiseIndependent.TugOfWar
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Moments of low-degree functions

Consequences of the Bonami Lemma `‖f‖_q ≤ √(q - 1) ^ k ‖f‖_2`
(`BitString.lpNorm_le_sqrt_pow_mul_lpNorm_two`) for a real function `f` of degree at most `k` on the
cube [O'Donnell, Section 9.5][ODonnell2014]:

* **the `L^p`–`L^2` comparison** (`BitString.lpNorm_two_le_exp_mul_lpNorm`): for `0 < p ≤ 2`,
  `‖f‖_2 ≤ e ^ (k (2 / p - 1)) ‖f‖_p`, in particular `‖f‖_2 ≤ e ^ k ‖f‖_1`
  (`BitString.lpNorm_two_le_exp_mul_lpNorm_one`) [O'Donnell, Theorem 9.22][ODonnell2014];
* **the low-degree tail bound** (`BitString.dens_le_exp_neg_mul_rpow`): for `t ≥ √(2 e) ^ k`,
  `Pr[|f| ≥ t ‖f‖_2] ≤ exp (-(k / (2 e)) t ^ (2 / k))` [O'Donnell, Theorem 9.23][ODonnell2014];
* **one-sided anticoncentration** (`BitString.exp_neg_two_mul_div_four_le_dens_lt`): if `f` is
  nonconstant, `Pr[f > 𝔼 f] ≥ e ^ (-2 k) / 4` [O'Donnell, Theorem 9.24][ODonnell2014];
* **Khintchine's inequality**, the case `k = 1` of Theorems 9.21 and 9.22 [O'Donnell, Section
  9.5][ODonnell2014]: a linear form `ℓ = ∑ᵢ aᵢ xᵢ` in uniformly random signs has
  `‖ℓ‖_2 = √(∑ᵢ aᵢ ^ 2)` (`BitString.lpNorm_two_sum_mul_signVal`, the identity hash family case of
  `Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign`), so
  `‖ℓ‖_q ≤ √(q - 1) √(∑ᵢ aᵢ ^ 2)` for `q ≥ 2` (`BitString.lpNorm_sum_mul_signVal_le`) and
  `√(∑ᵢ aᵢ ^ 2) ≤ e ^ (2 / p - 1) ‖ℓ‖_p` for `0 < p ≤ 2`
  (`BitString.sqrt_sum_sq_le_exp_mul_lpNorm`).

O'Donnell states the comparison for `1 ≤ p ≤ 2`, proves the case `p = 1` and leaves general `p` to
[O'Donnell, Exercise 9.15][ODonnell2014]; the same proof gives every `0 < p ≤ 2`. For `ε > 0`, the
exponent `2` lies between `p` and `2 + ε`, so the log-convexity of moments
(`Fintype.expect_rpow_le_rpow_mul_rpow`) and the Bonami Lemma at `q = 2 + ε` bound `‖f‖_2` by
`(1 + ε) ^ (k ((2 / p - 1) / ε + (1 / p - 1 / 2)))` times `‖f‖_p`. As `log (1 + ε) ≤ ε`, the
logarithm of this factor is at most `k (2 / p - 1) + O(ε)`, and we let `ε → 0`. The tail bound is
Markov's inequality for `|f| ^ q` with `q = t ^ (2 / k) / e ≥ 2`, and the one-sided bound is
Cauchy–Schwarz for `f - 𝔼 f` against the indicator of `f > 𝔼 f`, combined with the case `p = 1`.

## Main results

* `Cslib.BitString.lpNorm_two_le_exp_mul_lpNorm`,
  `Cslib.BitString.lpNorm_two_le_exp_mul_lpNorm_one`: Theorem 9.22.
* `Cslib.BitString.dens_le_exp_neg_mul_rpow`: Theorem 9.23.
* `Cslib.BitString.exp_neg_two_mul_div_four_le_dens_lt`: Theorem 9.24.
* `Cslib.BitString.lpNorm_sum_mul_signVal_le`, `Cslib.BitString.sqrt_sum_sq_le_exp_mul_lpNorm`:
  Khintchine's inequality.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `L^p`–`L^2` comparison for low-degree functions**: if `f` has degree at most `k` and
`0 < p ≤ 2`, then `‖f‖_2 ≤ e ^ (k (2 / p - 1)) ‖f‖_p` [O'Donnell, Theorem 9.22][ODonnell2014]. The
book states the range `1 ≤ p ≤ 2` and leaves `p ≠ 1` to [O'Donnell, Exercise 9.15][ODonnell2014];
the proof covers `0 < p < 1` as well. -/
theorem lpNorm_two_le_exp_mul_lpNorm {p : ℝ} (hp₀ : 0 < p) (hp₂ : p ≤ 2) {k : ℕ}
    {f : (ι → Bool) → ℝ} (hf : f ∈ lowDegree ℝ ι k) :
    lpNorm 2 f ≤ Real.exp (k * (2 / p - 1)) * lpNorm p f := by
  rcases hp₂.eq_or_lt with rfl | hp₂
  · rw [div_self two_ne_zero, sub_self, mul_zero, Real.exp_zero, one_mul]
  set m := 𝔼 x, f x ^ 2 with hm
  have hm0 : 0 ≤ m := expect_nonneg fun x _ => sq_nonneg _
  rcases hm0.eq_or_lt with hm0 | hmpos
  · rw [lpNorm_two, ← hm, ← hm0, Real.sqrt_zero]
    exact mul_nonneg (Real.exp_pos _).le (lpNorm_nonneg _ _)
  -- every absolute moment of order `r ≠ 0` is positive
  have hpos : ∀ r : ℝ, r ≠ 0 → 0 < 𝔼 x, |f x| ^ r := by
    intro r hr
    refine lt_of_le_of_ne (expect_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
      fun h => ?_
    have h0 := (Fintype.expect_eq_zero_iff_of_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg (f x)) r)).1 h.symm
    have hf0 (x : ι → Bool) : f x = 0 := by
      have := congrFun h0 x
      simp only [Pi.zero_apply, Real.rpow_eq_zero (abs_nonneg _) hr, abs_eq_zero] at this
      exact this
    have : m = 0 := by simp only [hm, hf0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, expect_const_zero]
    linarith
  set A := 𝔼 x, |f x| ^ p with hA
  have hApos : 0 < A := hpos p hp₀.ne'
  -- for each `ε > 0`, interpolating between `p` and `2 + ε`
  have key : ∀ ε : ℝ, 0 < ε →
      p / 2 * Real.log m ≤ Real.log A + (2 - p) * k + (2 - p) * k / 2 * ε := by
    intro ε hε
    have hD : 0 < 2 + ε - p := by linarith
    have hθ0 : 0 < ε / (2 + ε - p) := div_pos hε hD
    have hθ1 : ε / (2 + ε - p) < 1 := (div_lt_one hD).2 (by linarith)
    have hexp : ε / (2 + ε - p) * p + (1 - ε / (2 + ε - p)) * (2 + ε) = 2 := by
      field_simp; ring
    have hhol := Fintype.expect_rpow_le_rpow_mul_rpow (f := fun x => |f x|)
      (fun x => abs_nonneg _) hθ0 hθ1 hp₀.le (by linarith : (0 : ℝ) ≤ 2 + ε)
    rw [hexp] at hhol
    simp only [Real.rpow_two, sq_abs] at hhol
    have hBpos := hpos (2 + ε) (by linarith)
    set B := 𝔼 x, |f x| ^ (2 + ε) with hB
    have hlog1 : Real.log m ≤
        ε / (2 + ε - p) * Real.log A + (1 - ε / (2 + ε - p)) * Real.log B := by
      have := Real.log_le_log hmpos hhol
      rwa [Real.log_mul (Real.rpow_pos_of_pos hApos _).ne' (Real.rpow_pos_of_pos hBpos _).ne',
        Real.log_rpow hApos, Real.log_rpow hBpos] at this
    have hbon := lpNorm_le_sqrt_pow_mul_lpNorm_two (q := 2 + ε) (by linarith) hf
    rw [lpNorm, lpNorm_two, ← hB, ← hm] at hbon
    have hlog2 : (2 + ε)⁻¹ * Real.log B ≤ k * (Real.log (1 + ε) / 2) + Real.log m / 2 := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hBpos _) hbon
      rwa [Real.log_rpow hBpos, Real.log_mul (pow_pos (Real.sqrt_pos.2 (by linarith)) _).ne'
        (Real.sqrt_pos.2 hmpos).ne', Real.log_pow, Real.log_sqrt (by linarith),
        Real.log_sqrt hmpos.le, show 2 + ε - 1 = 1 + ε by ring] at this
    have hlog3 : Real.log (1 + ε) ≤ ε := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ε)
      linarith
    have h1 : (2 + ε - p) * Real.log m ≤ ε * Real.log A + (2 - p) * Real.log B := by
      have := mul_le_mul_of_nonneg_left hlog1 hD.le
      have e : (2 + ε - p) * (ε / (2 + ε - p) * Real.log A +
          (1 - ε / (2 + ε - p)) * Real.log B) = ε * Real.log A + (2 - p) * Real.log B := by
        field_simp; ring
      linarith
    have h2 : Real.log B ≤ (2 + ε) * (k * (Real.log (1 + ε) / 2) + Real.log m / 2) := by
      have := mul_le_mul_of_nonneg_left hlog2 (by linarith : (0 : ℝ) ≤ 2 + ε)
      rwa [← mul_assoc, mul_inv_cancel₀ (by linarith : (2 + ε : ℝ) ≠ 0), one_mul] at this
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 - p)
    have h4 : (2 - p) * (2 + ε) * k / 2 * Real.log (1 + ε) ≤ (2 - p) * (2 + ε) * k / 2 * ε :=
      mul_le_mul_of_nonneg_left hlog3
        (div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Nat.cast_nonneg k))
          two_pos.le)
    have h5 : ε * (p / 2 * Real.log m) ≤
        ε * (Real.log A + (2 - p) * k + (2 - p) * k / 2 * ε) := by
      linarith
    exact le_of_mul_le_mul_left h5 hε
  have hkey : p / 2 * Real.log m ≤ Real.log A + (2 - p) * k := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hc : 0 ≤ (2 - p) * k / 2 :=
      div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg k)) two_pos.le
    have h := key (δ / ((2 - p) * k / 2 + 1)) (by positivity)
    have hcδ : (2 - p) * k / 2 * (δ / ((2 - p) * k / 2 + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hlogm : Real.log m * (1 / 2) ≤ k * (2 / p - 1) + Real.log A * p⁻¹ := by
    have e : (k : ℝ) * (2 / p - 1) + Real.log A * p⁻¹ = (Real.log A + (2 - p) * k) / p := by
      field_simp; ring
    rw [e, le_div_iff₀ hp₀]
    linarith
  rw [lpNorm_two, ← hm, lpNorm, ← hA, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hmpos,
    Real.rpow_def_of_pos hApos, ← Real.exp_add]
  exact Real.exp_le_exp.2 hlogm

/-- **The `L^1`–`L^2` comparison for low-degree functions**: if `f` has degree at most `k`, then
`‖f‖_2 ≤ e ^ k ‖f‖_1` [O'Donnell, Theorem 9.22][ODonnell2014]. -/
theorem lpNorm_two_le_exp_mul_lpNorm_one {k : ℕ} {f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι k) : lpNorm 2 f ≤ Real.exp k * lpNorm 1 f := by
  have h := lpNorm_two_le_exp_mul_lpNorm one_pos one_le_two hf
  rwa [div_one, show (2 : ℝ) - 1 = 1 by norm_num, mul_one] at h

/-- **The tail bound for low-degree functions**: if `f ≢ 0` has degree at most `k` and
`t ≥ √(2 e) ^ k`, then `Pr[|f| ≥ t ‖f‖_2] ≤ exp (-(k / (2 e)) t ^ (2 / k))`
[O'Donnell, Theorem 9.23][ODonnell2014]. The hypothesis `‖f‖_2 > 0` replaces the book's
normalisation `‖f‖_2 = 1`: for `f = 0` the event is everything. -/
theorem dens_le_exp_neg_mul_rpow {k : ℕ} {f : (ι → Bool) → ℝ} (hf : f ∈ lowDegree ℝ ι k)
    (hf0 : 0 < lpNorm 2 f) {t : ℝ} (ht : √(2 * Real.exp 1) ^ k ≤ t) :
    (dens {x | t * lpNorm 2 f ≤ |f x|} : ℝ) ≤
      Real.exp (-(k / (2 * Real.exp 1) * t ^ (2 / k : ℝ))) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_div, zero_mul, neg_zero, Real.exp_zero]
    exact_mod_cast dens_le_one
  set N := lpNorm 2 f with hN
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h2e : 0 < 2 * Real.exp 1 := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le (pow_pos (Real.sqrt_pos.2 h2e) k) ht
  set s := t ^ (2 / k : ℝ) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos ht0 _
  have hlogs : Real.log s = 2 / k * Real.log t := Real.log_rpow ht0 _
  -- `log t ≥ (k / 2) log (2 e)`, so `s ≥ 2 e`
  have hlogt : k / 2 * Real.log (2 * Real.exp 1) ≤ Real.log t := by
    have := Real.log_le_log (pow_pos (Real.sqrt_pos.2 h2e) k) ht
    rwa [Real.log_pow, Real.log_sqrt h2e.le, ← mul_div_assoc, mul_div_right_comm] at this
  set q := s / Real.exp 1 with hq
  have hqpos : 0 < q := div_pos hspos he
  have hlogq : Real.log q = 2 / k * Real.log t - 1 := by
    rw [hq, Real.log_div hspos.ne' he.ne', hlogs, Real.log_exp]
  have hq2 : 2 ≤ q := by
    have hlog2 : Real.log 2 ≤ Real.log q := by
      rw [hlogq]
      have h := mul_le_mul_of_nonneg_left hlogt (by positivity : (0 : ℝ) ≤ 2 / k)
      rw [← mul_assoc, show 2 / (k : ℝ) * (k / 2) = 1 by field_simp, one_mul,
        Real.log_mul two_ne_zero he.ne', Real.log_exp] at h
      linarith
    exact (Real.log_le_log_iff two_pos hqpos).1 hlog2
  -- Markov's inequality for `|f| ^ q`
  have hmk := Fintype.mul_dens_filter_le_expect (f := fun x => |f x| ^ q)
    (fun x => Real.rpow_nonneg (abs_nonneg _) _) ((t * N) ^ q)
  have hsub : ({x | t * N ≤ |f x|} : Finset (ι → Bool)) ⊆
      ({x | (t * N) ^ q ≤ |f x| ^ q} : Finset (ι → Bool)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact Real.rpow_le_rpow (by positivity) hx hqpos.le
  have hd : (dens ({x | t * N ≤ |f x|} : Finset (ι → Bool)) : ℝ) ≤
      (dens ({x | (t * N) ^ q ≤ |f x| ^ q} : Finset (ι → Bool)) : ℝ) := by
    exact_mod_cast dens_le_dens hsub
  set D := (dens ({x | t * N ≤ |f x|} : Finset (ι → Bool)) : ℝ) with hD
  have hbon := lpNorm_le_sqrt_pow_mul_lpNorm_two hq2 hf
  rw [← hN] at hbon
  have hmom : 𝔼 x, |f x| ^ q = lpNorm q f ^ q := (lpNorm_rpow hqpos.ne' f).symm
  have hmain : (t * N) ^ q * D ≤ (√(q - 1) ^ k * N) ^ q := by
    calc (t * N) ^ q * D ≤ (t * N) ^ q *
          (dens ({x | (t * N) ^ q ≤ |f x| ^ q} : Finset (ι → Bool)) : ℝ) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ 𝔼 x, |f x| ^ q := hmk
      _ = lpNorm q f ^ q := hmom
      _ ≤ (√(q - 1) ^ k * N) ^ q :=
        Real.rpow_le_rpow (lpNorm_nonneg _ _) hbon hqpos.le
  rcases (show (0 : ℝ) ≤ D by positivity).eq_or_lt with hD0 | hDpos
  · rw [← hD0]; positivity
  -- take logarithms
  have hq1 : 0 < q - 1 := by linarith
  have hlog := Real.log_le_log (by positivity) hmain
  rw [Real.log_mul (by positivity) hDpos.ne', Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_mul ht0.ne' hf0.ne',
    Real.log_mul (by positivity) hf0.ne', Real.log_pow, Real.log_sqrt hq1.le] at hlog
  have hlq : Real.log (q - 1) ≤ Real.log q := Real.log_le_log hq1 (by linarith)
  -- `log D ≤ q (k / 2 log (q - 1) - log t) ≤ q (k / 2 log q - log t) = -(k / 2) q`
  have hkey : Real.log D ≤ -(k / 2 * q) := by
    have h1 : k / 2 * Real.log q - Real.log t = -(k / 2) := by
      rw [hlogq]; field_simp; ring
    have h2 : q * (k * (Real.log (q - 1) / 2)) ≤ q * (k / 2 * Real.log q) := by
      apply mul_le_mul_of_nonneg_left _ hqpos.le
      have := mul_le_mul_of_nonneg_left hlq (by positivity : (0 : ℝ) ≤ k / 2)
      linarith
    nlinarith
  have hfinal : k / (2 * Real.exp 1) * s = k / 2 * q := by
    rw [hq]; field_simp
  rw [hfinal, ← Real.exp_log hDpos]
  exact Real.exp_le_exp.2 hkey

/-- **One-sided anticoncentration for low-degree functions**: a nonconstant function `f` of degree
at most `k` exceeds its mean with probability at least `e ^ (-2 k) / 4`
[O'Donnell, Theorem 9.24][ODonnell2014]. -/
theorem exp_neg_two_mul_div_four_le_dens_lt {k : ℕ} {f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι k) (hV : 0 < 𝔼 x, (f x - 𝔼 y, f y) ^ 2) :
    Real.exp (-(2 * k)) / 4 ≤ (dens {x | 𝔼 y, f y < f x} : ℝ) := by
  classical
  set μ := 𝔼 y, f y with hμ
  set g : (ι → Bool) → ℝ := fun x => f x - μ with hg
  have hgdeg : g ∈ lowDegree ℝ ι k := Submodule.sub_mem _ hf (const_mem_lowDegree k μ)
  set E : (ι → Bool) → ℝ := fun x => if 0 < g x then 1 else 0 with hE
  have hg0 : 𝔼 x, g x = 0 := by
    simp only [hg, expect_sub_distrib, Fintype.expect_const, hμ, sub_self]
  have habs : 𝔼 x, |g x| = 2 * 𝔼 x, E x * g x := by
    have hpt (x : ι → Bool) : |g x| = 2 * (E x * g x) - g x := by
      simp only [hE]
      split_ifs with h
      · rw [abs_of_pos h]; ring
      · push Not at h
        rw [abs_of_nonpos h]; ring
    rw [expect_congr rfl fun x _ => hpt x, expect_sub_distrib, ← mul_expect, hg0, sub_zero]
  have hcs := expect_mul_sq_le_sq_mul_sq univ E g
  have hE2 : 𝔼 x, E x ^ 2 = (dens {x | 0 < g x} : ℝ) := Fintype.expect_boole_sq _
  rw [hE2] at hcs
  set m := 𝔼 x, g x ^ 2 with hm
  have hmpos : 0 < m := hV
  have hset : ({x | 0 < g x} : Finset (ι → Bool)) = ({x | μ < f x} : Finset (ι → Bool)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, hg, sub_pos]
  rw [hset] at hcs
  set D := (dens {x | μ < f x} : ℝ) with hD
  have h22 := lpNorm_two_le_exp_mul_lpNorm_one hgdeg
  rw [lpNorm_two, ← hm, lpNorm_one, habs] at h22
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h22 2
  rw [Real.sq_sqrt hmpos.le] at hsq
  -- `m ≤ 4 e^{2k} (𝔼 E g)^2 ≤ 4 e^{2k} D m`
  have hX : Real.exp (2 * k) = Real.exp k ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h1 : m ≤ 4 * Real.exp (2 * k) * (D * m) := by
    calc m ≤ (Real.exp k * (2 * 𝔼 x, E x * g x)) ^ 2 := hsq
      _ = 4 * Real.exp (2 * k) * (𝔼 x, E x * g x) ^ 2 := by rw [hX]; ring
      _ ≤ 4 * Real.exp (2 * k) * (D * m) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
  have h2 : 1 ≤ 4 * Real.exp (2 * k) * D := by
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_right hlt hmpos
    linarith
  have hee : Real.exp (-(2 * k)) * Real.exp (2 * k) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(2 * k))).le
  have h4 : Real.exp (-(2 * k)) * (4 * Real.exp (2 * k) * D) = 4 * D := by
    calc _ = 4 * (Real.exp (-(2 * k)) * Real.exp (2 * k)) * D := by ring
      _ = 4 * D := by rw [hee, mul_one]
  linarith

/-! ### Khintchine's inequality -/

omit [DecidableEq ι] in
/-- A linear form `x ↦ ∑ᵢ aᵢ xᵢ` in the coordinate signs has degree at most one. -/
theorem sum_mul_signVal_mem_lowDegree_one (a : ι → ℝ) :
    (fun x : ι → Bool => ∑ i, a i * signVal (x i)) ∈ lowDegree ℝ ι 1 := by
  classical
  have h : (fun x : ι → Bool => ∑ i, a i * signVal (x i)) = ∑ i, a i • chi ℝ {i} := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chi_singleton]
  rw [h]
  exact sum_mem_lowDegree _ fun i _ =>
    Submodule.smul_mem _ _ (by simpa only [card_singleton] using chi_mem_lowDegree (F := ℝ) {i})

/-- A linear form `ℓ = ∑ᵢ aᵢ xᵢ` in uniformly random signs has `‖ℓ‖_2 = √(∑ᵢ aᵢ ^ 2)`: the
unbiasedness of the tug-of-war estimator
(`Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign`) for the identity hash family. -/
theorem lpNorm_two_sum_mul_signVal (a : ι → ℝ) :
    lpNorm 2 (fun x : ι → Bool => ∑ i, a i * signVal (x i)) = √(∑ i, a i ^ 2) := by
  rw [lpNorm_two]
  congr 1
  exact (Probability.isKWiseIndependentHash_id (X := ι) (Y := Bool) 2).expect_sq_sum_mul_sign
    (fun b => by rw [sq, signVal_mul_self]) (by rw [Fintype.expect_bool]; norm_num) univ a

/-- **Khintchine's inequality**, upper bound: for `q ≥ 2`, a linear form `ℓ = ∑ᵢ aᵢ xᵢ` in
uniformly random signs has `‖ℓ‖_q ≤ √(q - 1) √(∑ᵢ aᵢ ^ 2)`, the case `k = 1` of the Bonami Lemma
[O'Donnell, Theorem 9.21][ODonnell2014]. -/
theorem lpNorm_sum_mul_signVal_le {q : ℝ} (hq : 2 ≤ q) (a : ι → ℝ) :
    lpNorm q (fun x : ι → Bool => ∑ i, a i * signVal (x i)) ≤ √(q - 1) * √(∑ i, a i ^ 2) := by
  have h := lpNorm_le_sqrt_pow_mul_lpNorm_two hq (sum_mul_signVal_mem_lowDegree_one a)
  rwa [pow_one, lpNorm_two_sum_mul_signVal] at h

/-- **Khintchine's inequality**, lower bound: for `0 < p ≤ 2`, a linear form `ℓ = ∑ᵢ aᵢ xᵢ` in
uniformly random signs has `√(∑ᵢ aᵢ ^ 2) ≤ e ^ (2 / p - 1) ‖ℓ‖_p`, the case `k = 1` of the
`L^p`–`L^2` comparison [O'Donnell, Theorem 9.22][ODonnell2014]. -/
theorem sqrt_sum_sq_le_exp_mul_lpNorm {p : ℝ} (hp₀ : 0 < p) (hp₂ : p ≤ 2) (a : ι → ℝ) :
    √(∑ i, a i ^ 2) ≤
      Real.exp (2 / p - 1) * lpNorm p (fun x : ι → Bool => ∑ i, a i * signVal (x i)) := by
  have h := lpNorm_two_le_exp_mul_lpNorm hp₀ hp₂ (sum_mul_signVal_mem_lowDegree_one a)
  rwa [Nat.cast_one, one_mul, lpNorm_two_sum_mul_signVal] at h

end Cslib.BitString
