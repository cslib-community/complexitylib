/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Counting tuples of bounded weight

Give each coordinate `i` of a tuple `β : ι → ℕ` a positive weight `w i`, with at most `m`
coordinates of each weight. This file bounds the number of tuples of total weight
`∑ i, w i * β i < p` by the partition generating function:

* for every `θ > 0` there are at most `exp (θ p + m π² / (6 θ))` of them
  (`Cslib.card_le_exp_of_sum_mul_lt`);
* taking `θ = √(m / p)`, there are at most `2 ^ (4 ⌊√(m p)⌋ + 4)`
  (`Cslib.card_le_two_pow_of_sum_mul_lt`).

This is the count (D.15) of the exponent tuples of the modes in the proof of the Boolean tensor
contraction theorem of [OpenAI2026ETH] (§D.4.5, pp. 62–63), where the modes play the coordinates
and their weights are their divisibility exponents.

**The proof.** Put `x = e^{-θ}`. Every tuple of weight below `p` has `x ^ (weight) ≥ x ^ p`, and the
sum of `x ^ (weight)` over all tuples is at most the generating product `∏ i, (1 - x ^ w i)⁻¹`.
Its logarithm is `∑ i, -log (1 - x ^ w i)`, which is at most `m` times the sum of
`-log (1 - e^{-θ j})` over the distinct weights `j`. Expanding the logarithm and summing the
geometric series bounds that sum (`Cslib.sum_neg_log_one_sub_exp_le`):

  `∑_{j ≥ 1} -log (1 - e^{-θ j}) = ∑_{h ≥ 1} 1 / (h (e^{θ h} - 1)) ≤ (1 / θ) ∑_{h ≥ 1} 1 / h²
    = π² / (6 θ)`,

using `e^y - 1 ≥ y` and `∑ 1 / h² = π² / 6` (`hasSum_zeta_two`).

## Main results

* `Cslib.sum_neg_log_one_sub_exp_le`: `∑_{j ∈ s} -log (1 - e^{-θ j}) ≤ π² / (6 θ)` for a finite
  set `s` of positive integers.
* `Cslib.card_le_exp_of_sum_mul_lt`: the generating-function bound on the number of tuples.
* `Cslib.card_le_two_pow_of_sum_mul_lt`: its natural-number form `2 ^ (4 ⌊√(m p)⌋ + 4)`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.5, the count (D.15)
  and the estimate following it (pp. 62–63).
-/

public section

namespace Cslib

open Finset Real

/-- **The logarithm of the partition generating function.** For `θ > 0` and every finite set
`s` of positive integers, `∑_{j ∈ s} -log (1 - e^{-θ j}) ≤ π² / (6 θ)`. -/
theorem sum_neg_log_one_sub_exp_le {θ : ℝ} (hθ : 0 < θ) (s : Finset ℕ) (hs : 0 ∉ s) :
    ∑ j ∈ s, -log (1 - exp (-(θ * j))) ≤ π ^ 2 / (6 * θ) := by
  have hterm : ∀ j ∈ s, HasSum (fun h : ℕ => exp (-(θ * j)) ^ (h + 1) / (h + 1))
      (-log (1 - exp (-(θ * j)))) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => hs (h ▸ hj))
    apply Real.hasSum_pow_div_log_of_abs_lt_one
    rw [abs_of_pos (exp_pos _), exp_lt_one_iff]
    have := mul_pos hθ hj0
    linarith
  have hzeta : HasSum (fun h : ℕ => 1 / θ * (1 / ((h : ℝ) + 1) ^ 2)) (1 / θ * (π ^ 2 / 6)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simp only [range_one, sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
    exact h.mul_left _
  have hle := hasSum_le (fun h => ?_) (hasSum_sum hterm) hzeta
  · calc _ ≤ 1 / θ * (π ^ 2 / 6) := hle
      _ = π ^ 2 / (6 * θ) := by field_simp
  -- For fixed `h`, the terms form a geometric series in `q = e^{-θ (h + 1)}`.
  set y : ℝ := θ * (h + 1) with hy
  have hy0 : 0 < y := by positivity
  set q : ℝ := exp (-y) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_lt_one_iff.2 (neg_lt_zero.2 hy0)
  have hpow : ∀ j : ℕ, exp (-(θ * j)) ^ (h + 1) = q ^ j := fun j => by
    rw [hq, ← exp_nat_mul, ← exp_nat_mul, hy]
    push_cast
    ring_nf
  have hgeo : ∑ j ∈ s, q ^ j ≤ (1 - q)⁻¹ - 1 := by
    have := sum_le_hasSum (insert 0 s) (fun j _ => pow_nonneg hq0 j)
      (hasSum_geometric_of_lt_one hq0 hq1)
    rw [sum_insert hs, pow_zero] at this
    linarith
  have hkey : q * (1 + y) ≤ 1 := by
    calc q * (1 + y) ≤ q * exp y := mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp y]) hq0
      _ = 1 := by rw [hq, ← exp_add, neg_add_cancel, exp_zero]
  have hq' : (1 - q)⁻¹ - 1 ≤ 1 / y := by
    have h1q : 0 < 1 - q := by linarith
    rw [show (1 - q)⁻¹ - 1 = q / (1 - q) by field_simp; ring, div_le_div_iff₀ h1q hy0]
    linarith
  have hh : (0 : ℝ) < h + 1 := by positivity
  calc ∑ j ∈ s, exp (-(θ * j)) ^ (h + 1) / (h + 1) = (∑ j ∈ s, q ^ j) / (h + 1) := by
        rw [sum_div]
        exact sum_congr rfl fun j _ => by rw [hpow]
    _ ≤ (1 / y) / (h + 1) := div_le_div_of_nonneg_right (hgeo.trans hq') hh.le
    _ = 1 / θ * (1 / ((h : ℝ) + 1) ^ 2) := by rw [hy]; field_simp

/-- **Counting tuples of bounded weight by the generating function.** Let every coordinate have a
positive weight, with at most `m` coordinates of each weight. Then for every `θ > 0` there are at
most `exp (θ p + m π² / (6 θ))` tuples of total weight below `p`. -/
theorem card_le_exp_of_sum_mul_lt {ι : Type*} [Fintype ι] {w : ι → ℕ} (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : ∀ j, #{i | w i = j} ≤ m) {p : ℕ} {S : Finset (ι → ℕ)}
    (hS : ∀ β ∈ S, ∑ i, w i * β i < p) {θ : ℝ} (hθ : 0 < θ) :
    (#S : ℝ) ≤ exp (θ * p + m * (π ^ 2 / (6 * θ))) := by
  classical
  set x : ℝ := exp (-θ) with hx
  have hx0 : 0 < x := exp_pos _
  have hx1 : x < 1 := exp_lt_one_iff.2 (neg_lt_zero.2 hθ)
  -- Every tuple contributes at least `x ^ p` to the generating sum.
  have h1 : (#S : ℝ) * x ^ p ≤ ∑ β ∈ S, x ^ (∑ i, w i * β i) := by
    calc (#S : ℝ) * x ^ p = ∑ _β ∈ S, x ^ p := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun β hβ => pow_le_pow_of_le_one hx0.le hx1.le (hS β hβ).le
  -- The tuples lie in a box, over which the generating sum factors.
  have hsub : S ⊆ Fintype.piFinset fun _ => range p := by
    intro β hβ
    rw [Fintype.mem_piFinset]
    intro i
    rw [mem_range]
    calc β i ≤ w i * β i := Nat.le_mul_of_pos_left _ (hw i)
      _ ≤ ∑ i, w i * β i := single_le_sum (fun i _ => Nat.zero_le (w i * β i)) (mem_univ i)
      _ < p := hS β hβ
  have h2 : ∑ β ∈ S, x ^ (∑ i, w i * β i) ≤ ∏ i, ∑ b ∈ range p, (x ^ w i) ^ b := by
    rw [prod_univ_sum]
    calc ∑ β ∈ S, x ^ (∑ i, w i * β i) = ∑ β ∈ S, ∏ i, (x ^ w i) ^ β i := by
          refine sum_congr rfl fun β _ => ?_
          rw [← prod_pow_eq_pow_sum]
          exact prod_congr rfl fun i _ => pow_mul x (w i) (β i)
      _ ≤ ∑ β ∈ Fintype.piFinset fun _ => range p, ∏ i, (x ^ w i) ^ β i :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => prod_nonneg fun _ _ => by positivity
  -- Each factor is a truncated geometric series.
  have h3 : ∏ i, ∑ b ∈ range p, (x ^ w i) ^ b ≤ exp (∑ i, -log (1 - x ^ w i)) := by
    rw [exp_sum]
    refine prod_le_prod₀ (fun i _ => sum_nonneg fun _ _ => by positivity) fun i _ => ?_
    have hy0 : 0 ≤ x ^ w i := by positivity
    have hy1 : x ^ w i < 1 := pow_lt_one₀ hx0.le hx1 (hw i).ne'
    rw [exp_neg, exp_log (by linarith)]
    exact sum_le_hasSum _ (fun _ _ => by positivity) (hasSum_geometric_of_lt_one hy0 hy1)
  -- Group the coordinates by weight.
  have h4 : ∑ i, -log (1 - x ^ w i) ≤ m * (π ^ 2 / (6 * θ)) := by
    have hxj : ∀ j : ℕ, x ^ j = exp (-(θ * j)) := fun j => by
      rw [hx, ← exp_nat_mul]
      ring_nf
    have hnn : ∀ j ∈ univ.image w, 0 ≤ -log (1 - x ^ j) := by
      intro j hj
      obtain ⟨i, -, rfl⟩ := mem_image.1 hj
      have : 0 < 1 - x ^ w i := by linarith [pow_lt_one₀ hx0.le hx1 (hw i).ne']
      have : 1 - x ^ w i ≤ 1 := by linarith [pow_pos hx0 (w i)]
      linarith [log_nonpos (by linarith) this]
    have h0 : 0 ∉ univ.image w := by
      simp only [mem_image, mem_univ, true_and, not_exists]
      exact fun i h => (hw i).ne' h
    rw [sum_comp (fun j => -log (1 - x ^ j)) w]
    calc ∑ j ∈ univ.image w, #{i ∈ univ | w i = j} • -log (1 - x ^ j)
        ≤ ∑ j ∈ univ.image w, m • -log (1 - x ^ j) :=
          sum_le_sum fun j hj => nsmul_le_nsmul_left (hnn j hj) (hm j)
      _ = m * ∑ j ∈ univ.image w, -log (1 - exp (-(θ * j))) := by
          rw [← smul_sum, nsmul_eq_mul]
          simp only [hxj]
      _ ≤ m * (π ^ 2 / (6 * θ)) :=
          mul_le_mul_of_nonneg_left (sum_neg_log_one_sub_exp_le hθ _ h0) (Nat.cast_nonneg m)
  have hxp : x ^ p * exp (θ * p) = 1 := by
    rw [hx, ← exp_nat_mul, ← exp_add]
    ring_nf
    exact exp_zero
  calc (#S : ℝ) = #S * x ^ p * exp (θ * p) := by rw [mul_assoc, hxp, mul_one]
    _ ≤ exp (m * (π ^ 2 / (6 * θ))) * exp (θ * p) :=
        mul_le_mul_of_nonneg_right ((h1.trans h2).trans (h3.trans (exp_le_exp.2 h4)))
          (exp_pos _).le
    _ = exp (θ * p + m * (π ^ 2 / (6 * θ))) := by rw [← exp_add, add_comm]

/-- `1 + π² / 6 ≤ 4 log 2`, so `exp ((1 + π² / 6) y) ≤ 16 ^ y`. -/
private theorem one_add_pi_sq_div_six_le : 1 + π ^ 2 / 6 ≤ 4 * log 2 := by
  nlinarith [pi_lt_d2, pi_pos, log_two_gt_d9]

/-- **Counting tuples of bounded weight, natural-number form.** Let every coordinate have a
positive weight, with at most `m` coordinates of each weight. Then there are at most
`2 ^ (4 ⌊√(m p)⌋ + 4)` tuples of total weight below `p`: the generating-function bound at
`θ = √(m / p)`. -/
theorem card_le_two_pow_of_sum_mul_lt {ι : Type*} [Fintype ι] {w : ι → ℕ} (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : ∀ j, #{i | w i = j} ≤ m) {p : ℕ} {S : Finset (ι → ℕ)}
    (hS : ∀ β ∈ S, ∑ i, w i * β i < p) : #S ≤ 2 ^ (4 * Nat.sqrt (m * p) + 4) := by
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : S = ∅ := eq_empty_of_forall_notMem fun β hβ => Nat.not_lt_zero _ (hS β hβ)
    simp [this]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have : IsEmpty ι := ⟨fun i => by
      have hpos : 0 < #{i' | w i' = w i} := card_pos.2 ⟨i, by simp⟩
      have := hm (w i)
      omega⟩
    exact (card_le_one_of_subsingleton S).trans Nat.one_le_two_pow
  set n := Nat.sqrt (m * p)
  set a : ℝ := √(m : ℝ) with ha
  set b : ℝ := √(p : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 (Nat.cast_pos.2 hm0)
  have hb0 : 0 < b := Real.sqrt_pos.2 (Nat.cast_pos.2 hp)
  have ha2 : (m : ℝ) = a ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg m)).symm
  have hb2 : (p : ℝ) = b ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg p)).symm
  have hexp : a / b * p + m * (π ^ 2 / (6 * (a / b))) = a * b * (1 + π ^ 2 / 6) := by
    rw [ha2, hb2]
    field_simp
  have hab : a * b ≤ n + 1 := by
    have hlt : ((m * p : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' (m * p)
    have hsq : (a * b) ^ 2 < ((n : ℝ) + 1) ^ 2 := by
      rw [mul_pow, ← ha2, ← hb2]
      push_cast at hlt
      exact hlt
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq).le
  have hreal : (#S : ℝ) ≤ 2 ^ (4 * n + 4) := by
    calc (#S : ℝ) ≤ exp (a / b * p + m * (π ^ 2 / (6 * (a / b)))) :=
          card_le_exp_of_sum_mul_lt hw hm hS (div_pos ha0 hb0)
      _ = exp (a * b * (1 + π ^ 2 / 6)) := by rw [hexp]
      _ ≤ exp (((4 * n + 4 : ℕ) : ℝ) * log 2) := by
          refine exp_le_exp.2 ?_
          have h1 : (0 : ℝ) ≤ 1 + π ^ 2 / 6 := by positivity
          calc a * b * (1 + π ^ 2 / 6) ≤ (n + 1) * (4 * log 2) :=
                mul_le_mul hab one_add_pi_sq_div_six_le h1 (by positivity)
            _ = ((4 * n + 4 : ℕ) : ℝ) * log 2 := by push_cast; ring
      _ = 2 ^ (4 * n + 4) := by rw [exp_nat_mul, exp_log two_pos]
  exact_mod_cast hreal

end Cslib
