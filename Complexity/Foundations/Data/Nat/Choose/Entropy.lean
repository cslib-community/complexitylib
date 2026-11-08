/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
-- `import all` only to unfold `Real.qaryEntropy`, whose body Mathlib does not expose; an upstream
-- `Real.qaryEntropy_def` lemma would make it unnecessary.
import all Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Complexity.Foundations.Combinatorics.BinomialTail
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Entropy bounds for partial binomial sums

For `q ≥ 2`, `0 ≤ α ≤ 1 - 1 / q` and `r ≤ α n`,
`∑_{j ≤ r} C(n, j) (q - 1) ^ j ≤ exp (n H_q(α))`, where `H_q = Real.qaryEntropy q` is the `q`-ary
entropy in nats. The left side is the number of words over `q` letters within Hamming distance `r`
of a fixed word of length `n`, so this is the entropy bound on the volume of a Hamming ball
[Guruswami, Rudra and Sudan, Proposition 3.3.3][GuruswamiRudraSudan2019]. The proof compares each
term with the binomial expansion of `(α + (1 - α)) ^ n = 1`: since `α ≤ (q - 1) (1 - α)`, every
term of weight `j ≤ α n` satisfies `(q - 1) ^ j exp (-n H_q(α)) ≤ α ^ j (1 - α) ^ (n - j)`. In base
`q` this reads `Vol_q(n, α n) ≤ q ^ (H_q(α) n)` with `H_q` measured in base `q`, the form in the
source. The binary case `q = 2` is `Cslib.sum_choose_le_exp_mul_binEntropy`.

## Main results

* `Cslib.sum_choose_mul_pow_le_exp_mul_qaryEntropy`: the `q`-ary entropy bound.
* `Cslib.sum_choose_le_exp_mul_binEntropy`: the binary entropy bound
  `∑_{j ≤ r} C(n, j) ≤ exp (n h(α))` for `α ≤ 1 / 2`.

## References

* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019], draft of
  26 August 2025
-/

public section

namespace Cslib

open Finset Real

/-- A word of weight `j ≤ α n` weighted by `(q - 1) ^ j` has mass at most
`α ^ j (1 - α) ^ (n - j)` relative to `exp (n H_q(α))`. -/
private theorem pow_mul_exp_neg_mul_qaryEntropy_le {q n j : ℕ} {α : ℝ} (hq : 2 ≤ q)
    (hα₀ : 0 < α) (hα : α ≤ 1 - 1 / q) (hjn : j ≤ n) (hj : (j : ℝ) ≤ α * n) :
    ((q : ℝ) - 1) ^ j * exp (-(n * qaryEntropy q α)) ≤ α ^ j * (1 - α) ^ (n - j) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hα1 : α < 1 := by
    have : (0 : ℝ) < 1 / q := by positivity
    linarith
  have h1α : 0 < 1 - α := by linarith
  have hnj : ((n - j : ℕ) : ℝ) = n - j := by push_cast [hjn]; ring
  have hcast : (((q : ℤ) - 1 : ℤ) : ℝ) = q - 1 := by push_cast; ring
  -- `α ≤ (q - 1) (1 - α)` is the hypothesis `α ≤ 1 - 1 / q`
  have hs : α ≤ (q - 1) * (1 - α) := by
    have hq0 : (0 : ℝ) < q := by linarith
    have : α * q ≤ q - 1 := by
      have := mul_le_mul_of_nonneg_right hα hq0.le
      rwa [sub_mul, one_div, inv_mul_cancel₀ hq0.ne', one_mul] at this
    nlinarith
  have hle : log α ≤ log (q - 1) + log (1 - α) := by
    rw [← log_mul hq1.ne' h1α.ne']
    exact log_le_log hα₀ hs
  rw [← log_le_log_iff (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_exp, log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow, hnj, qaryEntropy,
    hcast, binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
  nlinarith [mul_nonneg (sub_nonneg.mpr hj) (sub_nonneg.mpr hle)]

/-- **The entropy bound on the volume of a Hamming ball** [Guruswami, Rudra and Sudan,
Proposition 3.3.3][GuruswamiRudraSudan2019]: for `q ≥ 2`, `0 ≤ α ≤ 1 - 1 / q` and `r ≤ α n`,
`∑_{j ≤ r} C(n, j) (q - 1) ^ j ≤ exp (n H_q(α))`, where `H_q = Real.qaryEntropy q` is the `q`-ary
entropy in nats. -/
theorem sum_choose_mul_pow_le_exp_mul_qaryEntropy {q n r : ℕ} {α : ℝ} (hq : 2 ≤ q)
    (hα₀ : 0 ≤ α) (hα : α ≤ 1 - 1 / q) (hr : (r : ℝ) ≤ α * n) :
    ((∑ j ∈ range (r + 1), n.choose j * (q - 1) ^ j : ℕ) : ℝ) ≤ exp (n * qaryEntropy q α) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hcast : ((q - 1 : ℕ) : ℝ) = q - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, hcast]
  rcases hα₀.eq_or_lt with rfl | hα₀
  · have hr0 : r = 0 := by
      have : (r : ℝ) ≤ 0 := by simpa using hr
      exact_mod_cast le_antisymm this r.cast_nonneg
    subst hr0
    simp
  have hα1 : α < 1 := by
    have : (0 : ℝ) < 1 / q := by positivity
    linarith
  have hrn : r ≤ n := by
    have : (r : ℝ) ≤ n := hr.trans (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    exact_mod_cast this
  have hE : 0 < exp (n * qaryEntropy q α) := exp_pos _
  rw [← div_le_one hE, Finset.sum_div]
  refine le_of_le_of_eq ?_ (sum_choose_mul_pow_eq_one n α)
  calc (∑ j ∈ range (r + 1), (n.choose j : ℝ) * ((q : ℝ) - 1) ^ j / exp (n * qaryEntropy q α))
      ≤ ∑ j ∈ range (r + 1), (n.choose j : ℝ) * α ^ j * (1 - α) ^ (n - j) := by
        refine sum_le_sum fun j hj => ?_
        have hjr : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have key := pow_mul_exp_neg_mul_qaryEntropy_le hq hα₀ hα (hjr.trans hrn)
          (le_trans (by exact_mod_cast hjr) hr)
        rw [div_eq_mul_inv, ← exp_neg, mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ ∑ j ∈ range (n + 1), (n.choose j : ℝ) * α ^ j * (1 - α) ^ (n - j) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun j _ _ => by
          have : 0 ≤ 1 - α := by linarith
          positivity

/-- **The entropy bound on the volume of a binary Hamming ball**: for `0 ≤ α ≤ 1 / 2` and
`r ≤ α n`, `∑_{j ≤ r} C(n, j) ≤ exp (n h(α))`, where `h = Real.binEntropy` is the binary entropy in
nats. This is the case `q = 2` of `sum_choose_mul_pow_le_exp_mul_qaryEntropy`. -/
theorem sum_choose_le_exp_mul_binEntropy {n r : ℕ} {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 1 / 2)
    (hr : (r : ℝ) ≤ α * n) :
    (∑ j ∈ range (r + 1), (n.choose j : ℝ)) ≤ exp (n * binEntropy α) := by
  have h := sum_choose_mul_pow_le_exp_mul_qaryEntropy (q := 2) le_rfl hα₀ (by norm_num [hα]) hr
  simpa only [qaryEntropy_two, Nat.cast_sum, Nat.cast_mul, Nat.reduceSub, one_pow, Nat.cast_one,
    mul_one] using h

end Cslib
