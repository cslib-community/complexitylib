/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Calculus/Taylor.lean`)

public import Complexity.Init
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Global Taylor bounds on the real line

For a function `f : ℝ → ℝ` of class `C^(n+1)` whose `(n+1)`st derivative is bounded by `C`
everywhere, the Lagrange form of the remainder bounds the error of the degree-`n` Taylor polynomial
at any base point `x` and increment `h` by `C |h| ^ (n + 1) / (n + 1)!`
(`abs_sub_sum_iteratedDeriv_le`). Mathlib's `taylor_mean_remainder_bound` works on an interval
`[a, b]` with `iteratedDerivWithin` and the weaker denominator `n!`; here the derivatives are the
global `iteratedDeriv` and the increment may be negative. Consequently `f` grows at most like a
polynomial of degree `n + 1` (`exists_abs_le_mul_one_add_pow`).

## Main results

* `abs_sub_sum_iteratedDeriv_le`: the Lagrange remainder bound
  `|f (x + h) - ∑ j ≤ n, f⁽ʲ⁾ x h ^ j / j!| ≤ C |h| ^ (n + 1) / (n + 1)!`.
* `exists_abs_le_mul_one_add_pow`: `|f y| ≤ K (1 + |y| ^ (n + 1))` for some `K`.
-/

public section

open Finset
open scoped Nat

/-- **Taylor's theorem with the Lagrange remainder, global form.** If `f : ℝ → ℝ` is `C^(n+1)`
and `|f⁽ⁿ⁺¹⁾| ≤ C` everywhere, then the degree-`n` Taylor polynomial of `f` at `x` approximates
`f (x + h)` within `C |h| ^ (n + 1) / (n + 1)!`. -/
theorem abs_sub_sum_iteratedDeriv_le {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv (n + 1) f y| ≤ C) (x h : ℝ) :
    |f (x + h) - ∑ j ∈ range (n + 1), iteratedDeriv j f x * h ^ j / j !| ≤
      C * |h| ^ (n + 1) / (n + 1)! := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [Finset.sum_range_succ']
  have hne : x ≠ x + h := by simpa using hh
  obtain ⟨x', -, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf.contDiffOn
  have hu : UniqueDiffOn ℝ (Set.uIcc x (x + h)) := uniqueDiffOn_uIcc hne
  rw [taylor_within_apply] at heq
  have hsum : ∑ k ∈ range (n + 1), ((k ! : ℝ)⁻¹ * (x + h - x) ^ k) •
      iteratedDerivWithin k f (Set.uIcc x (x + h)) x =
      ∑ j ∈ range (n + 1), iteratedDeriv j f x * h ^ j / j ! := by
    refine sum_congr rfl fun k hk => ?_
    have hk' : (k : WithTop ℕ∞) ≤ n + 1 := by
      have := mem_range.1 hk
      exact_mod_cast (by omega : k ≤ n + 1)
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le hk') Set.left_mem_uIcc,
      add_sub_cancel_left, smul_eq_mul]
    ring
  rw [hsum, add_sub_cancel_left] at heq
  rw [heq, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hC x'

/-- A `C^(n+1)` function `f : ℝ → ℝ` with bounded `(n+1)`st derivative grows at most like a
polynomial of degree `n + 1`: `|f y| ≤ K (1 + |y| ^ (n + 1))` for some constant `K`. -/
theorem exists_abs_le_mul_one_add_pow {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv (n + 1) f y| ≤ C) :
    ∃ K, ∀ y, |f y| ≤ K * (1 + |y| ^ (n + 1)) := by
  set A := ∑ j ∈ range (n + 1), |iteratedDeriv j f 0| / (j ! : ℝ)
  refine ⟨A + |C|, fun y => ?_⟩
  have h := abs_sub_sum_iteratedDeriv_le hf hC 0 y
  rw [zero_add] at h
  set T := ∑ j ∈ range (n + 1), iteratedDeriv j f 0 * y ^ j / (j ! : ℝ)
  have hpow {j : ℕ} (hj : j ≤ n + 1) : |y| ^ j ≤ 1 + |y| ^ (n + 1) := by
    rcases le_total |y| 1 with h1 | h1
    · linarith [pow_le_one₀ (abs_nonneg y) h1 (n := j), pow_nonneg (abs_nonneg y) (n + 1)]
    · linarith [pow_le_pow_right₀ h1 hj]
  have hsum : |T| ≤ A * (1 + |y| ^ (n + 1)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun j hj => ?_
    have hj' : j ≤ n + 1 := by have := mem_range.1 hj; omega
    calc |iteratedDeriv j f 0 * y ^ j / j !| = |iteratedDeriv j f 0| / j ! * |y| ^ j := by
          rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpow hj') (by positivity)
  have hC' : C * |y| ^ (n + 1) / (n + 1)! ≤ |C| * (1 + |y| ^ (n + 1)) := by
    have hf1 : (1 : ℝ) ≤ (n + 1)! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    have hy : 0 ≤ |y| ^ (n + 1) := by positivity
    rw [div_le_iff₀ (by positivity)]
    have h2 : C * |y| ^ (n + 1) ≤ |C| * |y| ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hy
    nlinarith [abs_nonneg C, mul_nonneg (abs_nonneg C) hy]
  have htri := abs_add_le (f y - T) T
  rw [sub_add_cancel] at htri
  nlinarith
