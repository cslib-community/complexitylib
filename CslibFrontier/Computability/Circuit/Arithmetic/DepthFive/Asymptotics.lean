/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Params
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The parameters of the source are eventually good

The rank bounds for homogeneous depth-five circuits are proved for every parameter choice
satisfying the inequalities `Cslib.Circuits.DepthFive.Params.Good`. This module defines the
parameter choice of [OpenAI, §2][OpenAI2026DepthFive] and proves that it satisfies them for every
`n ≥ 2 ^ 20`, so in particular for all sufficiently large `n`.

The rounding in `a` and `b` is controlled by one estimate: if `b = ⌈U t / (1 - t)⌉` then
`t ≤ b / (b + U) ≤ t (1 + 2 / b)`. It is applied with `t = 1 / √n` for `α` and with
`t = α ^ ρ` for `β`.

## Main definitions

* `Cslib.Circuits.DepthFive.paramsOf`: the parameters of the source for `n` matrix layers.

## Main results

* `Cslib.Circuits.DepthFive.good_paramsOf`: `paramsOf n` is good for `n ≥ 2 ^ 20`.
* `Cslib.Circuits.DepthFive.eventually_good`: `paramsOf n` is good for all large `n`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §2 (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive

/-- Rounding `U t / (1 - t)` up to an integer `b` moves the ratio `b / (b + U)` up from `t` by a
factor of at most `1 + 2 / b`. -/
private theorem ceil_ratio {t U : ℝ} {b : ℕ} (ht : 0 < t) (ht1 : t < 1) (hU : 0 < U)
    (hb : b = ⌈U * t / (1 - t)⌉₊) :
    U * t ≤ b ∧ t ≤ b / (b + U) ∧ ((2 : ℝ) ≤ b → b / (b + U) ≤ t * (1 + 2 / b)) := by
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have h1 : U * t ≤ b * (1 - t) := (div_le_iff₀ h1t).1 (hb ▸ Nat.le_ceil _)
  have h2 : (b - 1) * (1 - t) < U * t := by
    rw [← lt_div_iff₀ h1t, sub_lt_iff_lt_add, hb]
    exact Nat.ceil_lt_add_one (div_nonneg (by positivity) h1t.le)
  have hb0 : (0 : ℝ) ≤ b := b.cast_nonneg
  refine ⟨by nlinarith, ?_, fun hb2 ↦ ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    linarith
  · have h : t * (1 + 2 / b) = t * (b + 2) / b := by field_simp
    rw [h, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2.le (by linarith : (0 : ℝ) ≤ b + 2),
      mul_nonneg ht.le hb0, mul_nonneg (mul_nonneg ht.le hb0) hU.le]

/-- Parameters with `√n - 2 < s ≤ √n` and the degrees `a`, `b` of the source are good for
`n ≥ 2 ^ 20`. -/
private theorem Params.good_of_ceil (p : Params) (hn : 2 ^ 20 ≤ p.n)
    (hs : (p.s : ℝ) ≤ √(p.n : ℝ)) (hs' : √(p.n : ℝ) - 2 < p.s)
    (ha : p.a = ⌈(p.v : ℝ) / (√(p.n : ℝ) - 1)⌉₊)
    (hb : p.b = ⌈p.u * p.α ^ p.ρ / (1 - p.α ^ p.ρ)⌉₊) : p.Good := by
  -- the integers `n`, `s`, `k`, `m`, with `w = √n`
  have hn' : (2 : ℝ) ^ 20 ≤ p.n := mod_cast hn
  have hw2 : √(p.n : ℝ) * √(p.n : ℝ) = p.n := Real.mul_self_sqrt p.n.cast_nonneg
  have hw : 1024 ≤ √(p.n : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  set w := √(p.n : ℝ)
  have hw0 : 0 < w := by linarith
  have hww : 1024 * w ≤ w * w := mul_le_mul_of_nonneg_right hw hw0.le
  have hkm : (p.k : ℝ) + p.m = p.n := mod_cast p.hkm
  have hks : (p.k : ℝ) + p.s = p.m := mod_cast p.hks
  have hk : 3 / 8 * (p.n : ℝ) ≤ p.k := by linarith
  have hk1 : (1 : ℝ) ≤ p.k := by linarith
  have hn0 : (0 : ℝ) < p.n := by linarith
  have hm0 : (0 : ℝ) < p.m := by linarith
  have hv : (p.v : ℝ) = p.k * p.n ^ 2 := by simp [Params.v]
  have hu : (p.u : ℝ) = p.m * p.n ^ 2 := by simp [Params.u]
  have hρ1 : p.ρ ≤ 1 := div_le_one_of_le₀ (by linarith) hm0.le
  have hρ0 : 0 < p.ρ := div_pos (by linarith) hm0
  -- a slice degree that is at least `c n² / √n` with `c ≥ k` is large
  have big {c : ℝ} {j : ℕ} (hc : (p.k : ℝ) ≤ c) (hj : c * p.n ^ 2 * w⁻¹ ≤ j) :
      (p.k : ℝ) ≤ j ∧ 4 * (p.n : ℝ) ≤ j ∧ 2 / (j : ℝ) ≤ 1 / 16 := by
    have h : c * p.n ^ 2 * w⁻¹ = c * (p.n * w) := by rw [← hw2]; field_simp
    have h4 : 4 * (p.n : ℝ) ≤ j := by
      linarith [mul_le_mul_of_nonneg_right (hk1.trans hc) (mul_pos hn0 hw0).le,
        mul_le_mul_of_nonneg_left hw hn0.le]
    refine ⟨by linarith, h4, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- the rounding of `a`
  have hwinv : w⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hv0 : (0 : ℝ) < p.v := by rw [hv]; positivity
  obtain ⟨hA, hα, hα'⟩ := ceil_ratio (inv_pos.2 hw0) hwinv hv0
    (ha.trans (by congr 1; field_simp))
  rw [hv] at hA
  obtain ⟨hka, hna, ha16⟩ := big le_rfl hA
  have hα0 : 0 < p.α := (inv_pos.2 hw0).trans_le hα
  have hα1 : p.α < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hαu : p.α ≤ Real.exp (2 / p.a - Real.log w) :=
    calc p.α ≤ w⁻¹ * (1 + 2 / p.a) := hα' (by linarith)
      _ ≤ w⁻¹ * Real.exp (2 / p.a) := by gcongr; linarith [Real.add_one_le_exp (2 / (p.a : ℝ))]
      _ = Real.exp (2 / p.a - Real.log w) := by rw [Real.exp_sub, Real.exp_log hw0]; ring
  -- the rounding of `b`
  have hx0 : 0 < p.α ^ p.ρ := Real.rpow_pos_of_pos hα0 _
  have hαx : p.α ≤ p.α ^ p.ρ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hα0 hα1.le hρ1
  obtain ⟨hB, hβ, hβ'⟩ := ceil_ratio hx0 (Real.rpow_lt_one hα0.le hα1 hρ0)
    (by rw [hu]; positivity) hb
  obtain ⟨-, hnb, hb16⟩ := big (c := p.m) (by linarith) <|
    (mul_le_mul_of_nonneg_left (hα.trans hαx) (by positivity)).trans (hu ▸ hB :)
  -- `α ^ ρ` is at most a constant times `1 / √n`
  have hlog : Real.log w ≤ w / 4 :=
    (Real.log_le_iff_le_exp hw0).2 <| by
      linarith [Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ w / 4)]
  have hρlog : (1 - p.ρ) * Real.log w ≤ 1 / 2 := by
    have h : 1 - p.ρ = p.s / p.m := by
      rw [Params.ρ, eq_div_iff hm0.ne', sub_mul, div_mul_cancel₀ _ hm0.ne']; linarith
    rw [h, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith [mul_le_mul hs hlog (Real.log_nonneg (by linarith)) hw0.le]
  have hx : p.α ^ p.ρ * Real.exp (2 / p.b) ≤ 2 / w :=
    calc p.α ^ p.ρ * Real.exp (2 / p.b)
        ≤ Real.exp ((2 / p.a - Real.log w) * p.ρ) * Real.exp (2 / p.b) := by
          rw [Real.exp_mul]; gcongr
      _ = Real.exp ((2 / p.a - Real.log w) * p.ρ + 2 / p.b) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log 2 - Real.log w) := Real.exp_le_exp.2 <| by
          linarith [Real.log_two_gt_d9, mul_le_mul_of_nonneg_left hρ1
            (by positivity : (0 : ℝ) ≤ 2 / p.a)]
      _ = 2 / w := by rw [Real.exp_sub, Real.exp_log two_pos, Real.exp_log hw0]
  have hβx : p.β ≤ p.α ^ p.ρ * Real.exp (2 / p.b) :=
    (hβ' (by linarith)).trans <| by gcongr; linarith [Real.add_one_le_exp (2 / (p.b : ℝ))]
  have hq : p.q ≤ 2 / w :=
    (Real.rpow_le_rpow_of_exponent_ge hα0 hα1.le (by linarith)).trans <| hβ.trans <|
      hβx.trans hx
  exact
    { n_pos := by lia
      k_pos := mod_cast hk1
      le_s := by linarith
      s_le := hs
      lam_ge := (le_div_iff₀ (by linarith)).2 hk
      k_le_a := mod_cast hka
      four_n_le_a := mod_cast hna
      four_n_le_b := mod_cast hnb
      α_ge := hα
      α_rpow_le_β := hβ
      β_le_α_rpow := hβx
      β_le := hβx.trans hx
      q_le := hq
      q_le_rpow := hq.trans <| by
        rw [div_le_iff₀ hw0, show w = _ from Real.sqrt_eq_rpow _, ← Real.rpow_add hn0,
          show -(2 : ℝ) / 5 + 1 / 2 = 10⁻¹ by norm_num,
          Real.le_rpow_inv_iff_of_pos two_pos.le hn0.le (by norm_num)]
        norm_num
        linarith
      q_le_half := hq.trans <| by rw [div_le_iff₀ hw0]; linarith
      n_ge := hn }

/-- The parameters of the source: `s` is the largest integer at most `√n` with the parity of `n`,
`k = (n - s) / 2`, `m = (n + s) / 2`, `a = ⌈v / (√n - 1)⌉`, `b = ⌈u α^ρ / (1 - α^ρ)⌉`. -/
noncomputable def paramsOf (n : ℕ) : Params :=
  let s := if (n - n.sqrt) % 2 = 0 then n.sqrt else n.sqrt - 1
  let k := (n - s) / 2
  let m := (n + s) / 2
  let a := ⌈((k * n ^ 2 : ℕ) : ℝ) / (√(n : ℝ) - 1)⌉₊
  let x : ℝ := ((a : ℝ) / (a + (k * n ^ 2 : ℕ))) ^ ((k : ℝ) / m)
  { n, s, k, m, a
    b := ⌈(m * n ^ 2 : ℕ) * x / (1 - x)⌉₊
    hkm := by grind [n.sqrt_le_self, Nat.sqrt_eq_zero (n := n)]
    hks := by grind [n.sqrt_le_self, Nat.sqrt_eq_zero (n := n)] }

@[simp]
theorem paramsOf_n (n : ℕ) : (paramsOf n).n = n := rfl

/-- The parameters of the source are good for `n ≥ 2 ^ 20`. -/
theorem good_paramsOf {n : ℕ} (hn : 2 ^ 20 ≤ n) : (paramsOf n).Good := by
  have h1 := Real.nat_sqrt_le_real_sqrt (a := n)
  have h2 := Real.real_sqrt_lt_nat_sqrt_succ (a := n)
  refine (paramsOf n).good_of_ceil hn ?_ ?_ rfl rfl <;> simp only [paramsOf] <;> split_ifs
  · exact h1
  · exact (Nat.cast_le.2 (Nat.sub_le _ _)).trans h1
  · linarith
  · have : ((n.sqrt - 1 : ℕ) : ℝ) = n.sqrt - 1 :=
      Nat.cast_pred (Nat.sqrt_pos.2 (by lia))
    linarith

/-- The parameters of the source are good for all sufficiently large `n`. -/
theorem eventually_good : ∀ᶠ n in Filter.atTop, (paramsOf n).Good :=
  Filter.eventually_atTop.2 ⟨2 ^ 20, fun _ ↦ good_paramsOf⟩

end Cslib.Circuits.DepthFive
