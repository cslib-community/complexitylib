/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.OverflowBudget
public import Complexity.Foundations.Analysis.RowCompression.Floors
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Uniform noise budgets along a dyadic compression schedule

The slack of group `i < m` is `2 ^ (m - (i + 1))`, while a perturbation propagated through
the current and later groups has weight `C ^ (m - i)`. For nonnegative `C` and `q ≤ 1` with
`C * q < 1`, their weighted decay sum is at most `C * q / (1 - C * q)`, uniformly in `m`.
The proof compares the dyadic exponent with the number of remaining groups and reuses the
finite geometric-series bound. In particular, the absolute stability factor `C = 28` is
paid for by `q = 1/64`, with total factor at most `7/9`.

Composing this numerical bound with the actual first-overflow moment theorem removes the
finite weighted-sum obligation in [OpenAI2026LogSpace, Section 8.4, (8.18)]. Noise
with individual `p`-th moment budgets `(ε * q ^ d_i) ^ p` has actual overflow-tail budget
`(ε * C * q / (1 - C * q)) ^ p`. All quantities may share an environment.

Individual prefix-noise estimates and the choice of a propagation constant for the relative
stability argument remain separate obligations. This theorem applies to any supplied `C`;
it does not assert that the absolute constant 28 also proves that relative stability bound.

## Main results

* `Cslib.RowCompression.sum_propagation_mul_dyadic_decay_le`: an explicit uniform sum bound.
* `Cslib.RowCompression.sum_propagation_mul_sixteenth_le`: factor-28 payment at decay 1/16.
* `Cslib.RowCompression.sum_propagation_mul_quarter_le`: factor-28 payment at decay 1/4.
* `Cslib.RowCompression.vertexNormPow_firstOverflowNoiseTail_le_dyadic_budget`: the resulting
  normalized moment bound for the actual first-overflow tail.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, equation (8.18) on p. 49 (source label `buf-noise-sum`) and the following
  choice of noise decay
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset
open scoped BigOperators

/-- Geometric decay in the dyadic slack pays for propagation through all remaining groups,
including the current one, with a constant independent of the horizon. -/
theorem sum_propagation_mul_dyadic_decay_le {C q : ℝ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hCq : C * q < 1) (m : ℕ) :
    ∑ i ∈ range m, C ^ (m - i) * q ^ dyadicSlack m i ≤ C * q / (1 - C * q) := by
  calc
    _ ≤ ∑ i ∈ range m, (C * q) ^ (m - i) := by
      refine sum_le_sum fun i hi => ?_
      have hi' := mem_range.mp hi
      have hrem : m - i ≤ dyadicSlack m i := by
        have hcount : m - i = m - (i + 1) + 1 := by omega
        rw [hcount]
        exact Nat.succ_le_of_lt Nat.lt_two_pow_self
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq hq1 hrem)
        (pow_nonneg hC _)
    _ = ∑ i ∈ range m, (C * q) ^ ((m - 1 - i) + 1) := by
      refine sum_congr rfl fun i hi => ?_
      congr 1
      have hi' := mem_range.mp hi
      omega
    _ = ∑ i ∈ range m, (C * q) ^ (i + 1) :=
      sum_range_reflect (fun i => (C * q) ^ (i + 1)) m
    _ ≤ C * q / (1 - C * q) := by
      have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1) (mul_nonneg hC hq) hCq
      simpa only [sum_Ico_eq_sum_range, Nat.add_sub_cancel, pow_one, Nat.add_comm] using h

/-- The actual factor-28 propagation is paid by sixteenth-power dyadic decay.
The two-unit offset in `2 * (m - i) ≤ dyadicSlack m i + 2` is paid once,
before summing a geometric series. No event probability or independence is used. -/
theorem sum_propagation_mul_sixteenth_le (m : ℕ) :
    ∑ i ∈ range m, (28 : ℝ) ^ (m - i) *
      (1 / 16 : ℝ) ^ dyadicSlack m i ≤ 1792 / 57 := by
  have htwo (n : ℕ) : 2 * n ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      by_cases hn : n = 0
      · subst n; norm_num
      · have hp : 2 ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.one_lt_two_pow hn)
        rw [pow_succ]
        omega
  have hterm (i : ℕ) (hi : i ∈ range m) :
      (28 : ℝ) ^ (m - i) * (1 / 16 : ℝ) ^ dyadicSlack m i ≤
        256 * (7 / 64 : ℝ) ^ (m - i) := by
    have hrem : 2 * (m - i) ≤ dyadicSlack m i + 2 := by
      have hh := htwo (m - (i + 1))
      have hi' := mem_range.mp hi
      unfold dyadicSlack
      omega
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) hrem
    have he : (16 : ℝ) ^ (2 * (m - i)) = (256 : ℝ) ^ (m - i) := by
      rw [pow_mul]; norm_num
    rw [he, pow_add] at hp
    have hden : (0 : ℝ) < 16 ^ dyadicSlack m i := by positivity
    rw [one_div_pow, mul_one_div, div_le_iff₀ hden]
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ (7 / 64 : ℝ) ^ (m - i) by positivity)
    have hid : (7 / 64 : ℝ) ^ (m - i) * 256 ^ (m - i) = 28 ^ (m - i) := by
      rw [← mul_pow]; norm_num
    rw [hid] at h
    nlinarith only [h]
  have hs : ∑ i ∈ range m, (7 / 64 : ℝ) ^ (m - i) ≤ 7 / 57 := by
    calc
      _ = ∑ i ∈ range m, (7 / 64 : ℝ) ^ ((m - 1 - i) + 1) := by
        apply sum_congr rfl
        intro i hi
        congr 1
        have hi' := mem_range.mp hi
        omega
      _ = ∑ i ∈ range m, (7 / 64 : ℝ) ^ (i + 1) :=
        sum_range_reflect (fun i => (7 / 64 : ℝ) ^ (i + 1)) m
      _ ≤ _ := by
        have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1)
          (by norm_num : (0 : ℝ) ≤ 7 / 64) (by norm_num : (7 / 64 : ℝ) < 1)
        norm_num only [sum_Ico_eq_sum_range, Nat.add_sub_cancel, pow_one] at h
        simpa only [Nat.add_comm] using h
  apply (sum_le_sum hterm).trans
  rw [← mul_sum]
  nlinarith only [hs]

/-- The actual factor-28 propagation is paid by quarter-power dyadic decay.
The eight-unit offset in `4 * (m - i) ≤ dyadicSlack m i + 8` is paid once,
before summing a geometric series. No event probability or independence is used. -/
theorem sum_propagation_mul_quarter_le (m : ℕ) :
    ∑ i ∈ range m, (28 : ℝ) ^ (m - i) *
      (1 / 4 : ℝ) ^ dyadicSlack m i ≤ 458752 / 57 := by
  have hfour (n : ℕ) : 4 * n ≤ 2 ^ n + 4 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      by_cases hn : n ≤ 1
      · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> norm_num
      · have hp : 4 ≤ 2 ^ n := by
          have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n)
          exact h
        rw [pow_succ]
        omega
  have hterm (i : ℕ) (hi : i ∈ range m) :
      (28 : ℝ) ^ (m - i) * (1 / 4 : ℝ) ^ dyadicSlack m i ≤
        65536 * (7 / 64 : ℝ) ^ (m - i) := by
    have hrem : 4 * (m - i) ≤ dyadicSlack m i + 8 := by
      have hh := hfour (m - (i + 1))
      have hi' := mem_range.mp hi
      unfold dyadicSlack
      omega
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hrem
    have he : (4 : ℝ) ^ (4 * (m - i)) = (256 : ℝ) ^ (m - i) := by
      rw [pow_mul]; norm_num
    rw [he, pow_add] at hp
    have hden : (0 : ℝ) < 4 ^ dyadicSlack m i := by positivity
    rw [one_div_pow, mul_one_div, div_le_iff₀ hden]
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ (7 / 64 : ℝ) ^ (m - i) by positivity)
    have hid : (7 / 64 : ℝ) ^ (m - i) * 256 ^ (m - i) = 28 ^ (m - i) := by
      rw [← mul_pow]; norm_num
    rw [hid] at h
    nlinarith only [h]
  have hs : ∑ i ∈ range m, (7 / 64 : ℝ) ^ (m - i) ≤ 7 / 57 := by
    calc
      _ = ∑ i ∈ range m, (7 / 64 : ℝ) ^ ((m - 1 - i) + 1) := by
        apply sum_congr rfl
        intro i hi
        congr 1
        have hi' := mem_range.mp hi
        omega
      _ = ∑ i ∈ range m, (7 / 64 : ℝ) ^ (i + 1) :=
        sum_range_reflect (fun i => (7 / 64 : ℝ) ^ (i + 1)) m
      _ ≤ _ := by
        have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1)
          (by norm_num : (0 : ℝ) ≤ 7 / 64) (by norm_num : (7 / 64 : ℝ) < 1)
        norm_num only [sum_Ico_eq_sum_range, Nat.add_sub_cancel, pow_one] at h
        simpa only [Nat.add_comm] using h
  apply (sum_le_sum hterm).trans
  rw [← mul_sum]
  nlinarith only [hs]

/-- A prefix of the dyadic decay sum retains the decay of its last included group.
This pays sums of correlated group noises without losing a factor for the prefix length. -/
theorem sum_prefix_dyadic_decay_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {m j : ℕ} (hj : j ≤ m) :
    ∑ i ∈ range j, q ^ dyadicSlack m i ≤ q ^ dyadicSlack m (j - 1) / (1 - q) := by
  have hterm (i : ℕ) (hi : i < j) :
      dyadicSlack m (j - 1) + (j - 1 - i) ≤ dyadicSlack m i := by
    have hj0 : 0 < j := by omega
    have he : m - (i + 1) = (m - j) + (j - 1 - i) := by omega
    have hd : 1 ≤ 2 ^ (m - j) := Nat.one_le_pow _ _ (by decide)
    have hr : j - 1 - i + 1 ≤ 2 ^ (j - 1 - i) :=
      Nat.succ_le_of_lt Nat.lt_two_pow_self
    simp only [dyadicSlack, show j - 1 + 1 = j by omega, he, pow_add]
    nlinarith
  calc
    _ ≤ ∑ i ∈ range j, q ^ dyadicSlack m (j - 1) * q ^ (j - 1 - i) := by
      apply sum_le_sum
      intro i hi
      rw [← pow_add]
      exact pow_le_pow_of_le_one hq hq1.le (hterm i (mem_range.mp hi))
    _ = q ^ dyadicSlack m (j - 1) * ∑ i ∈ range j, q ^ i := by
      rw [← mul_sum, sum_range_reflect]
    _ ≤ q ^ dyadicSlack m (j - 1) * (1 / (1 - q)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
      simpa only [Nat.add_zero, pow_zero, Nat.Ico_zero_eq_range] using
        geom_sum_Ico_le_of_lt_one (m := 0) (n := j) hq hq1
    _ = _ := by ring

/-- **A horizon-independent budget for actual first-overflow noise.** Individual moments
decaying geometrically in the dyadic slack give an explicit normalized tail bound. The
source mask, noise, increments, initial states, and overflow may be arbitrarily correlated. -/
theorem vertexNormPow_firstOverflowNoiseTail_le_dyadic_budget {Ω V ι : Type*}
    [Fintype Ω] [Fintype V] (S : Ω → V → Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : Ω → V → ℕ → ι → Fin 2 → ℝ) (a : Ω → V → State ι) (m : ℕ)
    {p : ℕ} (hp : p ≠ 0) {N u : ℝ} (hNu : 0 ≤ N * u)
    (X : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    {C q ε : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hCq : C * q < 1) (hε : 0 ≤ ε) (γ : ℕ → Ω → V → ℝ)
    (hγ : ∀ i < m, ∀ σ x, X σ x → 0 ≤ γ i σ x)
    (hbudget : ∀ i < m, vertexNormPow p N u X (γ i) ≤
      (ε * q ^ dyadicSlack m i) ^ p) :
    vertexNormPow p N u X (fun σ x => firstOverflowNoiseTail (S σ x) n K ρ
      (Δ σ x) (a σ x) m (fun i => C ^ (m - i)) (fun i => γ i σ x)) ≤
        (ε * (C * q / (1 - C * q))) ^ p := by
  refine (vertexNormPow_firstOverflowNoiseTail_le_pow_sum S n K ρ Δ a m hp hNu X
    (fun i => C ^ (m - i)) (fun i => ε * q ^ dyadicSlack m i) γ
    (fun _ _ => pow_nonneg hC _) (fun _ _ => mul_nonneg hε (pow_nonneg hq _))
    hγ hbudget).trans ?_
  apply pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity)
  calc
    _ = ε * ∑ i ∈ range m, C ^ (m - i) * q ^ dyadicSlack m i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_propagation_mul_dyadic_decay_le hC hq hq1 hCq m) hε

end Cslib.RowCompression
