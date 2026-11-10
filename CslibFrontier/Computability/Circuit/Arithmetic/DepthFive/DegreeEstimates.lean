/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Params
import CslibFrontier.Foundations.Analysis.SpecialFunctions.RpowAbsSum
import Mathlib.Algebra.BigOperators.Field

/-!
# The weights of the factor degrees

The product-rank lemma bounds the rank measure of a product by `2 D ∏ j, H (e j)`, where
`H e = ∑ i ≤ e, q ^ |i - λ e|`. This file bounds the weights `H e`, following the degree
estimates of [OpenAI, §3][OpenAI2026DepthFive]. The sum is dominated by the terms nearest to
`λ e`, and `λ = 1 / 2 - s / (2 n)`.

* For every `e`, `H e ≤ exp (132 e / √n)`.
* If `4 s e < n`, then `λ e` is at distance at least `s e / (2 n)` from the integers, and
  `H e ≤ q ^ (s e / (4 n)) * exp (132 e / √n)`.
* `H 1 ≤ q ^ (1 / 8)`.

The first factors multiply to `exp (132 √n)` over factors of total degree `n`. A product of
factors of low degree, or one containing at least `n / (4 s)` linear factors, also gains a power
of `q` that is at most `n ^ (-√n / 100)`.

The source proves `H e ≤ q ^ d (1 + 4 q ^ (1 - 2 d))` for the distance `d` from `λ e` to the
integers, and sums the errors of the even degrees by a convexity argument. Here the even
degrees keep the weaker power `q ^ (d / 2)`, which absorbs the error whenever `q ^ (d / 2)` is
small, so that no convexity is needed.

## Main results

* `Params.Good.H_le_exp`, `Params.Good.H_le_of_low`, `Params.Good.H_one_le`: the three bounds.
* `Params.Good.prod_H_le_of_low`: a product of weights of low degrees.
* `Params.Good.H_one_pow_mul_prod_H_le`: a product of weights with many linear factors.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §3 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.DepthFive.Params

open Finset

variable {p : Params}

theorem Good.cast_n_pos (hp : p.Good) : (0 : ℝ) < p.n := by exact_mod_cast hp.n_pos

theorem Good.q_le_one (hp : p.Good) : p.q ≤ 1 := hp.q_le_half.trans (by norm_num)

/-- `q ^ (1 / 4) ≤ 1 / 4`. -/
theorem Good.q_rpow_quarter_le (hp : p.Good) : p.q ^ (1 / 4 : ℝ) ≤ 1 / 4 := by
  have hn : (2 : ℝ) ^ 20 ≤ p.n := by exact_mod_cast hp.n_ge
  calc p.q ^ (1 / 4 : ℝ) ≤ ((p.n : ℝ) ^ (-(2 : ℝ) / 5)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hp.q_pos.le hp.q_le_rpow (by norm_num)
    _ = (p.n : ℝ) ^ (-(1 : ℝ) / 10) := by
        rw [← Real.rpow_mul p.n.cast_nonneg]; norm_num
    _ ≤ ((2 : ℝ) ^ 20) ^ (-(1 : ℝ) / 10) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hn (by norm_num)
    _ = 1 / 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `λ e = e / 2 - s e / (2 n)`. -/
theorem Good.lam_mul (hp : p.Good) (e : ℝ) : p.lam * e = e / 2 - p.s * e / (2 * p.n) := by
  have hn := hp.cast_n_pos
  have h : (p.n : ℝ) = 2 * p.k + p.s := by
    exact_mod_cast (by have := p.hkm; have := p.hks; lia : p.n = 2 * p.k + p.s)
  rw [lam]
  field_simp
  rw [h]
  ring

/-- If `n ≤ 4 s e`, then `√n ≤ 4 e`. -/
theorem Good.sqrt_le_of_le (hp : p.Good) {e : ℕ} (he : p.n ≤ 4 * p.s * e) :
    √(p.n : ℝ) ≤ 4 * e := by
  have h : (p.n : ℝ) ≤ 4 * p.s * e := by exact_mod_cast he
  have hs := Real.sqrt_pos.2 hp.cast_n_pos
  refine le_of_mul_le_mul_left ?_ hs
  nlinarith [Real.mul_self_sqrt hp.cast_n_pos.le, hp.s_le, e.cast_nonneg (α := ℝ)]

/-- If `x ≥ √n / 40`, then `q ^ x ≤ n ^ (-√n / 100)`. -/
theorem Good.q_rpow_le (hp : p.Good) {x : ℝ} (hx : √(p.n : ℝ) / 40 ≤ x) :
    p.q ^ x ≤ (p.n : ℝ) ^ (-√(p.n : ℝ) / 100) := by
  have h1 : (1 : ℝ) ≤ p.n := by exact_mod_cast hp.n_pos
  calc p.q ^ x ≤ ((p.n : ℝ) ^ (-(2 : ℝ) / 5)) ^ x :=
        Real.rpow_le_rpow hp.q_pos.le hp.q_le_rpow
          (le_trans (by positivity) hx)
    _ = (p.n : ℝ) ^ (-(2 : ℝ) / 5 * x) := by rw [← Real.rpow_mul p.n.cast_nonneg]
    _ ≤ (p.n : ℝ) ^ (-√(p.n : ℝ) / 100) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

theorem Good.H_nonneg (hp : p.Good) (e : ℕ) : 0 ≤ p.H e :=
  sum_nonneg fun _ _ => Real.rpow_nonneg hp.q_pos.le _

/-- If `λ e` is at distance at least `3 / 8` from the integers, then `H e ≤ q ^ (1 / 8)`. -/
theorem Good.H_le_of_mid (hp : p.Good) {e i₀ : ℕ} (h₀ : i₀ + 3 / 8 ≤ p.lam * e)
    (h₁ : p.lam * e ≤ i₀ + 5 / 8) : p.H e ≤ p.q ^ (1 / 8 : ℝ) := by
  have hq := hp.q_pos
  have h := Real.sum_range_rpow_abs_sub_le hq hp.q_le_half (e + 1) (i₀ := i₀)
    (x := p.lam * e) (by linarith) (by linarith)
  have h38 : p.q ^ (3 / 8 : ℝ) = p.q ^ (1 / 8 : ℝ) * p.q ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hq]; norm_num
  have ha : p.q ^ (p.lam * e - i₀) ≤ p.q ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hq hp.q_le_one (by linarith)
  have hb : p.q ^ (i₀ + 1 - p.lam * e) ≤ p.q ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hq hp.q_le_one (by linarith)
  have h8 := Real.rpow_pos_of_pos hq (1 / 8)
  have h4 := hp.q_rpow_quarter_le
  have hmul : p.q ^ (1 / 8 : ℝ) * p.q ^ (1 / 4 : ℝ) ≤ p.q ^ (1 / 8 : ℝ) * (1 / 4) :=
    mul_le_mul_of_nonneg_left h4 h8.le
  refine h.trans ?_
  have h2 : 1 + 2 * p.q ≤ 2 := by linarith [hp.q_le_half]
  calc (1 + 2 * p.q) * (p.q ^ (p.lam * e - i₀) + p.q ^ (i₀ + 1 - p.lam * e))
      ≤ 2 * (p.q ^ (3 / 8 : ℝ) + p.q ^ (3 / 8 : ℝ)) := by gcongr
    _ ≤ p.q ^ (1 / 8 : ℝ) := by rw [h38]; linarith

/-- `H 1 ≤ q ^ (1 / 8)`. -/
theorem Good.H_one_le (hp : p.Good) : p.H 1 ≤ p.q ^ (1 / 8 : ℝ) := by
  have h := hp.lam_mul 1
  have hs : (0 : ℝ) ≤ p.s * 1 / (2 * p.n) := by positivity
  refine hp.H_le_of_mid (i₀ := 0) ?_ ?_ <;> push_cast <;> linarith [hp.lam_ge]

/-- For `0 ≤ ε ≤ 1 / 8`, the two terms nearest to an integer at distance `ε` are at most
`(1 + 64 q) q ^ (ε / 2)`. -/
private theorem rpow_add_rpow_le {q ε : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hq4 : q ^ (1 / 4 : ℝ) ≤ 1 / 4) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    q ^ (1 - ε) + q ^ ε ≤ (1 + 64 * q) * q ^ (ε / 2) := by
  have hz := Real.rpow_pos_of_pos hq (ε / 2)
  have hz1 : q ^ (ε / 2) ≤ 1 := Real.rpow_le_one hq.le hq1 (by positivity)
  have hw := Real.rpow_pos_of_pos hq (1 - 3 * (ε / 2))
  have hw4 : q ^ (1 - 3 * (ε / 2)) ≤ 1 / 4 :=
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)).trans hq4
  have e1 : q ^ (1 - ε) = q ^ (1 - 3 * (ε / 2)) * q ^ (ε / 2) := by
    rw [← Real.rpow_add hq]; congr 1; ring
  have e2 : q ^ ε = q ^ (ε / 2) * q ^ (ε / 2) := by
    rw [← Real.rpow_add hq]; congr 1; ring
  have e3 : q ^ (1 - 3 * (ε / 2)) * (q ^ (ε / 2)) ^ 3 = q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
    convert Real.rpow_one q using 2
    push_cast
    ring
  rw [e1, e2, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ hz.le
  rcases le_total (q ^ (ε / 2)) (1 / 4) with h | h
  · linarith
  · have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h 3) hw.le
    linarith

/-- A factor of low degree: if `4 s e < n`, then `H e ≤ q ^ (s e / (4 n)) * exp (132 e / √n)`. -/
theorem Good.H_le_of_low (hp : p.Good) {e : ℕ} (he : 4 * p.s * e < p.n) :
    p.H e ≤ p.q ^ (p.s * e / (4 * p.n) : ℝ) * Real.exp (132 * e / √(p.n : ℝ)) := by
  have hq := hp.q_pos
  have hn := hp.cast_n_pos
  have hε0 : (0 : ℝ) ≤ p.s * e / (2 * p.n) := by positivity
  have hε1 : (p.s * e / (2 * p.n) : ℝ) < 1 / 8 := by
    have h : (4 * p.s * e : ℝ) < p.n := by exact_mod_cast he
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hexp : (p.s * e / (4 * p.n) : ℝ) = p.s * e / (2 * p.n) / 2 := by ring
  have hlam := hp.lam_mul e
  obtain ⟨c, rfl | rfl⟩ := e.even_or_odd'
  · rcases c with _ | c
    · simp [H]
    push_cast at hlam hε0 hε1 hexp ⊢
    have h := Real.sum_range_rpow_abs_sub_le hq hp.q_le_half (2 * (c + 1) + 1) (i₀ := c)
      (x := p.lam * (2 * (c + 1))) (by linarith) (by linarith)
    have hE := rpow_add_rpow_le hq hp.q_le_one hp.q_rpow_quarter_le hε0 hε1.le
    rw [show p.lam * (2 * (c + 1)) - c = 1 - p.s * (2 * (c + 1)) / (2 * p.n) by linarith,
      show c + 1 - p.lam * (2 * (c + 1)) = p.s * (2 * (c + 1)) / (2 * p.n) by linarith] at h
    have hsq := Real.sqrt_pos.2 hn
    have h66 : 66 * p.q ≤ 132 * (2 * (c + 1)) / √(p.n : ℝ) := by
      have := hp.q_le
      rw [le_div_iff₀ hsq] at this ⊢
      nlinarith [c.cast_nonneg (α := ℝ)]
    have hpos := Real.rpow_pos_of_pos hq (p.s * (2 * (c + 1)) / (2 * p.n) / 2)
    calc p.H (2 * (c + 1)) ≤ _ := by simpa [H] using h
      _ ≤ (1 + 2 * p.q) * ((1 + 64 * p.q) * p.q ^ (p.s * (2 * (c + 1)) / (2 * p.n) / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = p.q ^ (p.s * (2 * (c + 1)) / (2 * p.n) / 2 : ℝ) *
            ((1 + 2 * p.q) * (1 + 64 * p.q)) := by ring
      _ ≤ p.q ^ (p.s * (2 * (c + 1)) / (2 * p.n) / 2 : ℝ) *
            (Real.exp (2 * p.q) * Real.exp (64 * p.q)) := by
          gcongr
          · linarith [Real.add_one_le_exp (2 * p.q)]
          · linarith [Real.add_one_le_exp (64 * p.q)]
      _ ≤ _ := by
          rw [← Real.exp_add, hexp]
          gcongr
          linarith
  · push_cast at hlam hε0 hε1 hexp ⊢
    have h := hp.H_le_of_mid (e := 2 * c + 1) (i₀ := c) (by push_cast; linarith)
      (by push_cast; linarith)
    calc p.H (2 * c + 1) ≤ p.q ^ (1 / 8 : ℝ) := h
      _ ≤ p.q ^ (p.s * (2 * c + 1) / (4 * p.n) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hq hp.q_le_one (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (Real.rpow_nonneg hq.le _)
          (Real.one_le_exp (by positivity))

/-- Every factor: `H e ≤ exp (132 e / √n)`. -/
theorem Good.H_le_exp (hp : p.Good) (e : ℕ) : p.H e ≤ Real.exp (132 * e / √(p.n : ℝ)) := by
  have hq := hp.q_pos
  by_cases he : 4 * p.s * e < p.n
  · exact (hp.H_le_of_low he).trans (mul_le_of_le_one_left (Real.exp_nonneg _)
      (Real.rpow_le_one hq.le hp.q_le_one (by positivity)))
  · have hx : (0 : ℝ) ≤ p.lam * e := mul_nonneg (le_trans (by norm_num) hp.lam_ge) e.cast_nonneg
    have h := Real.sum_range_rpow_abs_sub_le hq hp.q_le_half (e + 1) (Nat.floor_le hx)
      (Nat.lt_floor_add_one _).le
    have ha : p.q ^ (p.lam * e - ⌊p.lam * e⌋₊) ≤ 1 :=
      Real.rpow_le_one hq.le hp.q_le_one (sub_nonneg.2 (Nat.floor_le hx))
    have hb : p.q ^ (⌊p.lam * e⌋₊ + 1 - p.lam * e) ≤ 1 :=
      Real.rpow_le_one hq.le hp.q_le_one (sub_nonneg.2 (Nat.lt_floor_add_one _).le)
    have hsq := Real.sqrt_pos.2 hp.cast_n_pos
    have h33 : (33 : ℝ) ≤ 132 * e / √(p.n : ℝ) := by
      rw [le_div_iff₀ hsq]
      linarith [hp.sqrt_le_of_le (not_lt.1 he)]
    calc p.H e ≤ (1 + 2 * p.q) * (1 + 1) := h.trans (by gcongr)
      _ ≤ 132 * e / √(p.n : ℝ) + 1 := by linarith [hp.q_le_half]
      _ ≤ _ := Real.add_one_le_exp _

variable {ι : Type*} [Fintype ι] {e : ι → ℕ}

/-- The weights of factors of total degree at most `n` multiply to at most `exp (132 √n)`. -/
theorem Good.prod_H_le_exp (hp : p.Good) (he : ∑ j, e j ≤ p.n) :
    ∏ j, p.H (e j) ≤ Real.exp (132 * √(p.n : ℝ)) := by
  have h : (∑ j, (e j : ℝ)) ≤ p.n := by exact_mod_cast he
  calc ∏ j, p.H (e j) ≤ ∏ j, Real.exp (132 * e j / √(p.n : ℝ)) :=
        prod_le_prod₀ (fun j _ => hp.H_nonneg _) fun j _ => hp.H_le_exp _
    _ = Real.exp (132 * (∑ j, (e j : ℝ)) / √(p.n : ℝ)) := by
        rw [← Real.exp_sum, mul_sum, sum_div]
    _ ≤ Real.exp (132 * p.n / √(p.n : ℝ)) := by gcongr
    _ = Real.exp (132 * √(p.n : ℝ)) := by rw [mul_div_assoc, Real.div_sqrt]

/-- The weights of factors of low degree, of total degree `n`, multiply to at most
`exp (132 √n) n ^ (-√n / 100)`. -/
theorem Good.prod_H_le_of_low (hp : p.Good) (he : ∑ j, e j = p.n)
    (hlow : ∀ j, 4 * p.s * e j < p.n) :
    ∏ j, p.H (e j) ≤ Real.exp (132 * √(p.n : ℝ)) * (p.n : ℝ) ^ (-√(p.n : ℝ) / 100) := by
  have hn := hp.cast_n_pos
  have h : (∑ j, (e j : ℝ)) = p.n := by exact_mod_cast he
  calc ∏ j, p.H (e j)
      ≤ ∏ j, p.q ^ (p.s * e j / (4 * p.n) : ℝ) * Real.exp (132 * e j / √(p.n : ℝ)) :=
        prod_le_prod₀ (fun j _ => hp.H_nonneg _) fun j _ => hp.H_le_of_low (hlow j)
    _ = Real.exp (132 * √(p.n : ℝ)) * p.q ^ (p.s / 4 : ℝ) := by
        rw [prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos hp.q_pos, ← sum_div,
          ← sum_div, ← mul_sum, ← mul_sum, h, mul_comm]
        congr 1
        · rw [mul_div_assoc, Real.div_sqrt]
        · congr 1
          field_simp
    _ ≤ _ := by
        gcongr
        exact hp.q_rpow_le (by linarith [hp.le_s])

/-- The weights of `d ≥ n / (4 s)` linear factors and further factors, of total degree `n`,
multiply to at most `exp (132 √n) n ^ (-√n / 100)`. -/
theorem Good.H_one_pow_mul_prod_H_le (hp : p.Good) {d : ℕ} (hd : p.n ≤ 4 * p.s * d)
    (he : d + ∑ j, e j = p.n) :
    p.H 1 ^ d * ∏ j, p.H (e j) ≤
      Real.exp (132 * √(p.n : ℝ)) * (p.n : ℝ) ^ (-√(p.n : ℝ) / 100) := by
  rw [mul_comm]
  refine mul_le_mul (hp.prod_H_le_exp (by lia)) ?_ (pow_nonneg (hp.H_nonneg 1) d)
    (Real.exp_nonneg _)
  calc p.H 1 ^ d ≤ (p.q ^ (1 / 8 : ℝ)) ^ d := pow_le_pow_left₀ (hp.H_nonneg 1) hp.H_one_le d
    _ = p.q ^ (d / 8 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp.q_pos.le]; congr 1; ring
    _ ≤ _ := hp.q_rpow_le (by linarith [hp.sqrt_le_of_le hd])

end Cslib.Circuits.DepthFive.Params
