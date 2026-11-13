/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.BalancedCount
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorReduction
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The number of trials of the base-`r` reduction

The choice of the number `μ` of trials in [ChanItakuraMaYu2026], Theorem 3.4 (p. 14,
"we now choose `μ = Õ(n̂² / r^d)`"), made explicit from the exact count of balanced pairs.

For `0 < r`, `r ∣ d` and a target `k`, `vTrials k e r d` is
`⌊k 4 ^ (e + 2) ((d / r)!) ^ r / (3 d! (r!) ^ (d / r))⌋ + 1`, computed from `d`, `r`, `e` and `k`
only. By `card_balancedPairs_mul`, `3 #P μ > k 4 ^ (e + 2)` (`lt_three_mul_card_mul_vTrials`), so
with `μ = vTrials k e r d` trials and a uniform prime of `[2 ^ e, 2 ^ (e + 1))` with
`r ^ d ≤ 2 ^ e`, the base-`r` reduction misses a sum `c ∈ C ∩ (A + B)` with probability at most
`#bad / #window + exp (-k)` (`vaverage_miss_le_exp`).

Since `4 ^ (e + 2) = 16 · 4 ^ e` and the paper's `2 ^ e ≈ r ^ d`, this is
`μ ≈ 16 k r ^ (2 d) / (3 #P)`; with `#P = d! / ((d/r)!)^r · (r!)^(d/r)` the paper's
`μ = Õ(n̂² / r^d)` follows from its choice of `d`. Not formalized: that choice of
`d = 2 log_ρ n̂ + O(log log N)`, the lower bound `d! / ((d/r)!)^r = r^d / d^{Θ(r)}`, the expected
running time with these parameters, and Corollaries 3.5 and 3.6.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vTrials`: the number of trials.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.lt_three_mul_card_mul_vTrials`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vaverage_miss_le_exp`: the miss probability with this
  number of trials.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Nat Real

/-- The number of trials for the target `exp (-k)`:
`⌊k 4 ^ (e + 2) ((d / r)!) ^ r / (3 d! (r!) ^ (d / r))⌋ + 1`. -/
@[expose] def vTrials (k e r d : ℕ) : ℕ :=
  k * 4 ^ (e + 2) * ((d / r)!) ^ r / (3 * (d ! * (r !) ^ (d / r))) + 1

/-- With `vTrials k e r d` trials, `k 4 ^ (e + 2) < 3 #P μ`, for `0 < r` and `r ∣ d`. -/
theorem lt_three_mul_card_mul_vTrials {k e r d : ℕ} (hr : 0 < r) (hrd : r ∣ d) :
    k * 4 ^ (e + 2) < 3 * #(balancedPairs r d) * vTrials k e r d := by
  have hcount := card_balancedPairs_mul hr hrd
  have hS : 0 < ((d / r)!) ^ r := pow_pos (Nat.factorial_pos _) _
  have hN : 0 < 3 * (d ! * (r !) ^ (d / r)) :=
    Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.factorial_pos _) (pow_pos (Nat.factorial_pos _) _))
  have hdiv := Nat.lt_mul_div_succ (k * 4 ^ (e + 2) * ((d / r)!) ^ r) hN
  -- `k 4^(e+2) S < 3 N μ = 3 #P S μ`, then cancel `S`
  have : k * 4 ^ (e + 2) * ((d / r)!) ^ r <
      3 * #(balancedPairs r d) * vTrials k e r d * ((d / r)!) ^ r := by
    calc k * 4 ^ (e + 2) * ((d / r)!) ^ r
        < 3 * (d ! * (r !) ^ (d / r)) * vTrials k e r d := hdiv
      _ = 3 * (#(balancedPairs r d) * ((d / r)!) ^ r) * vTrials k e r d := by rw [hcount]
      _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- **The miss probability with `vTrials k e r d` trials** ([ChanItakuraMaYu2026], Theorem 3.4):
for `0 < r`, `r ∣ d`, `r ^ d ≤ 2 ^ e`, a sum `c = a + b ∈ C` and a uniform prime of the window
`[2 ^ e, 2 ^ (e + 1))`, the base-`r` reduction with `vTrials k e r d` uniform seeds misses `c`
with probability at most `#bad / #window + exp (-k)`. -/
theorem vaverage_miss_le_exp {r d s e k : ℕ} (hr : 0 < r) (hrd : r ∣ d)
    (hs : s ≤ balancedSize r d) (hre : r ^ d ≤ 2 ^ e) {A B C : List ℕ} {a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C) (hW : (primeWindow e).Nonempty) :
    (∑ q ∈ primeWindow e,
        missProbOf (fun q σ => vtrialM r d s (p := q) σ) (vTrials k e r d) A B C c q) /
        #(primeWindow e) ≤
      (#(badPrimesOf e ((r !) ^ (d / r)) c A B) : ℝ) / #(primeWindow e) + exp (-k) := by
  refine (vaverage_miss_le hs hre ha hb habc hc hW).trans (add_le_add_right ?_ _)
  set x : ℝ := 3 * #(balancedPairs r d) / (4 : ℝ) ^ (e + 2)
  set μ := vTrials k e r d
  have hP : (#(balancedPairs r d) : ℝ) ≤ (2 : ℝ) ^ e * 2 ^ e := by
    have := (card_balancedPairs_le r d).trans (Nat.pow_le_pow_left hre 2)
    rw [sq] at this
    exact_mod_cast this
  have h4 : (4 : ℝ) ^ (e + 2) = 16 * ((2 : ℝ) ^ e * 2 ^ e) := by
    rw [pow_add, ← mul_pow]; norm_num; ring
  have hx1 : 0 ≤ 1 - x := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ e * 2 ^ e := by positivity
    simp only [x]
    rw [sub_nonneg, div_le_one (by positivity), h4]
    linarith
  have hkx : (k : ℝ) ≤ x * μ := by
    have h := lt_three_mul_card_mul_vTrials (k := k) (e := e) hr hrd
    have h' : (k : ℝ) * (4 : ℝ) ^ (e + 2) ≤ 3 * #(balancedPairs r d) * μ := by
      exact_mod_cast h.le
    simp only [x]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  calc (1 - x) ^ μ ≤ (exp (-x)) ^ μ := pow_le_pow_left₀ hx1 (one_sub_le_exp_neg x) μ
    _ = exp (-(x * μ)) := by rw [← exp_nat_mul]; ring_nf
    _ ≤ exp (-k) := exp_le_exp.mpr (by linarith)

end Cslib.Algorithms.Lean.SubsetConvThreeSum
