/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialReduction
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The base-`r` reduction from 3SUM to convolution in `[r]^d`

The reduction of [ChanItakuraMaYu2026], Theorem 3.4 (Section 3.2, "Algorithm" and "Error
probability analysis", pp. 13–14), for given random choices: `vthreeSumM r d s p seeds A B C` is
the reduction `reduceM` of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialReduction` with
the base-`r` trials `vtrialM` of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorTrial`.

* `ret_vthreeSumM`, `exists_add_eq_of_mem_ret_vthreeSumM`, `time_vthreeSumM`: the output
  (bad sums and queries accepted by a trial on the isolated elements), one-sided error for every
  modulus and all seeds, and the exact cost.
* `vmiss_le`: for `c = a + b ∈ C`, a prime `p ≥ r ^ d` good for `c`
  (`4 #L (r !) ^ (d / r) ≤ p - 1`) and `μ` uniform seeds, the miss probability is at most
  `(1 - 3 #P / (4 p ^ 2)) ^ μ`, with `P` the pairs whose digit vectors add up to a balanced vector.
* `card_vBadPrimes_le`, `vaverage_miss_le`: for a uniform prime of the window
  `[2 ^ e, 2 ^ (e + 1))` with `r ^ d ≤ 2 ^ e`, the miss probability is at most
  `#bad / #window + (1 - 3 #P / 4 ^ (e + 2)) ^ μ`, and bad primes are few (Markov's inequality).

## Model and differences from the paper

* The paper picks a random prime of `(r ^ d, 2 r ^ d]`; here the prime is uniform in a binary
  window `[2 ^ e, 2 ^ (e + 1))` with `r ^ d ≤ 2 ^ e`, so that the existing prime-density bound
  `two_pow_le_card_primeWindow` applies. For `e = ⌈log₂ r ^ d⌉` the prime is below `4 r ^ d`
  instead of `2 r ^ d`.
* As in Theorem 2.3's formalization, the prime and the seeds are inputs, sampling is uncharged, and
  probabilities are exact counts over uniform finite sample spaces.
* Not formalized: the parameter choices `d = 2 log_ρ n̂ + O(log log N)` and `μ = Õ(n̂² / r ^ d)`,
  the count `#P = d! / ((d/r)!)^r · (r!)^{d/r}`, the expected running time, the amplification over
  `O(log (N |C|))` repetitions, and Corollaries 3.5 and 3.6.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vthreeSumM`: the base-`r` reduction.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vBadPrimes`: the primes of a window that are not good.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.ret_vthreeSumM`,
  `exists_add_eq_of_mem_ret_vthreeSumM`, `time_vthreeSumM`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vmiss_le`, `card_vBadPrimes_le`, `vaverage_miss_le`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Nat

variable {p : ℕ}

/-- **The base-`r` reduction** for given random choices: the modulus `p` and the seeds of the
trials. -/
@[expose] def vthreeSumM (r d s p : ℕ) (seeds : List (Seed p)) (A B C : List ℕ) :
    TimeM ℕ (List ℕ) :=
  reduceM (fun σ => vtrialM r d s σ) seeds A B C

/-- The base-`r` trials return their accepted queries. -/
theorem trialSpec_vtrialM {r d s : ℕ} (hs : s ≤ balancedSize r d) :
    TrialSpec (p := p) (fun σ => vtrialM r d s σ) fun σ Ag Bg c => VAccepts r d σ Ag Bg c :=
  fun σ Ag Bg C => ret_vtrialM σ Ag Bg C hs

/-- **What the base-`r` reduction returns**: the queries of `C` that are bad sums or accepted by a
trial on the isolated elements. -/
theorem ret_vthreeSumM {r d s : ℕ} (hs : s ≤ balancedSize r d) (seeds : List (Seed p))
    (A B C : List ℕ) :
    (vthreeSumM r d s p seeds A B C).ret = C.filter fun c => decide (BadHit p A B c ∨
      ∃ σ ∈ seeds, VAccepts r d σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) :=
  ret_reduceM (trialSpec_vtrialM hs) seeds A B C

/-- **Soundness of the base-`r` reduction** (one-sided error): every reported query is a sum
`a + b` with `a ∈ A` and `b ∈ B`, for every modulus and all seeds. -/
theorem exists_add_eq_of_mem_ret_vthreeSumM {r d s : ℕ} (hs : s ≤ balancedSize r d)
    {seeds : List (Seed p)} {A B C : List ℕ} {c : ℕ}
    (hc : c ∈ (vthreeSumM r d s p seeds A B C).ret) : ∃ a ∈ A, ∃ b ∈ B, a + b = c :=
  exists_add_eq_of_mem_ret_reduceM (trialSpec_vtrialM hs)
    (fun _ _ _ _ h => exists_add_eq_of_vaccepts h) hc

/-- **The cost of the base-`r` reduction**, exactly: `3 (|A| + |B|)` ticks to split off `A_bad`
and `B_bad`, the ticks of the trials (`time_vtrialM`), one tick per listed bad sum and per value
reported by a trial, and one per query. -/
theorem time_vthreeSumM {r d s : ℕ} (hs : s ≤ balancedSize r d) (seeds : List (Seed p))
    (A B C : List ℕ) :
    let Ag := A.filter fun a => decide (Isolated p A a)
    let Bg := B.filter fun b => decide (Isolated p B b)
    (vthreeSumM r d s p seeds A B C).time = 3 * A.length + 3 * B.length +
      (seeds.map fun σ => (vtrialM r d s σ Ag Bg C).time).sum +
      ((A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
        A.length * (B.filter fun b => decide (¬ Isolated p B b)).length) +
      (seeds.map fun σ => (C.filter fun c => decide (VAccepts r d σ Ag Bg c)).length).sum +
      C.length :=
  time_reduceM (trialSpec_vtrialM hs) seeds A B C

/-! ### Error probability -/

theorem card_balancedPairs_le (r d : ℕ) : #(balancedPairs r d) ≤ (r ^ d) ^ 2 := by
  refine (card_filter_le _ _).trans ?_
  rw [card_product, card_range, sq]

/-- **The miss probability for a good prime** ([ChanItakuraMaYu2026], Theorem 3.4): let
`c = a + b ∈ C` with `a ∈ A`, `b ∈ B`, let `p ≥ r ^ d` be prime and good for `c`
(`4 #L (r !) ^ (d / r) ≤ p - 1`). Over `μ` independent uniform seeds, the base-`r` reduction misses
`c` with probability at most `(1 - 3 #P / (4 p ^ 2)) ^ μ`. -/
theorem vmiss_le [Fact p.Prime] {r d s μ : ℕ} (hs : s ≤ balancedSize r d) (hp : r ^ d ≤ p)
    {A B C : List ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C)
    (hgood : 4 * (#(falsePairs p c (A.filter fun a => decide (Isolated p A a))
      (B.filter fun b => decide (Isolated p B b))) * (r !) ^ (d / r)) ≤ p - 1) :
    (#((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (vthreeSumM r d s p (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds p) : ℝ) ^ μ ≤
      (1 - 3 * #(balancedPairs r d) / (4 * (p : ℝ) ^ 2)) ^ μ :=
  reduceM_miss_le (trialSpec_vtrialM hs)
    ((card_balancedPairs_le r d).trans (Nat.pow_le_pow_left hp 2)) ha hb habc hc
    fun hia hib => four_mul_card_vaccepts_ge hp (fun _ hx => List.mem_of_mem_filter hx)
      (fun _ hx => List.mem_of_mem_filter hx) (List.mem_filter.mpr ⟨ha, decide_eq_true hia⟩)
      (List.mem_filter.mpr ⟨hb, decide_eq_true hib⟩) hia hib habc hgood

/-- The primes of the window `[2 ^ e, 2 ^ (e + 1))` that are not good for `c`:
`q - 1 < 4 #L (r !) ^ (d / r)`. -/
@[expose] def vBadPrimes (e r d c : ℕ) (A B : List ℕ) : Finset ℕ :=
  (primeWindow e).filter fun q => q - 1 < 4 * (#(falsePairs q c A B) * (r !) ^ (d / r))

/-- **Few bad primes** (Markov's inequality, as in [ChanItakuraMaYu2026], Theorem 3.4):
`e #bad (2 ^ e - 1) ≤ 4 (r !) ^ (d / r) |A| |B| log₂ M`. -/
theorem card_vBadPrimes_le {e r d c M : ℕ} {A B : List ℕ}
    (hM : ∀ ab ∈ A.toFinset ×ˢ B.toFinset, (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs ≤ M) :
    e * (#(vBadPrimes e r d c A B) * (2 ^ e - 1)) ≤
      4 * (r !) ^ (d / r) * (#(A.toFinset ×ˢ B.toFinset) * Nat.log 2 M) := by
  set K := (r !) ^ (d / r)
  have h1 : #(vBadPrimes e r d c A B) * (2 ^ e - 1) ≤
      4 * K * ∑ q ∈ primeWindow e, #(falsePairs q c A B) := by
    calc #(vBadPrimes e r d c A B) * (2 ^ e - 1)
        = ∑ _q ∈ vBadPrimes e r d c A B, (2 ^ e - 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ q ∈ vBadPrimes e r d c A B, 4 * K * #(falsePairs q c A B) :=
          sum_le_sum fun q hq => by
            obtain ⟨hw, hlt⟩ := mem_filter.mp hq
            have := (mem_primeWindow.mp hw).2.1
            have hlt' : q - 1 < 4 * (#(falsePairs q c A B) * K) := hlt
            have : 4 * (#(falsePairs q c A B) * K) = 4 * K * #(falsePairs q c A B) := by ring
            omega
      _ ≤ ∑ q ∈ primeWindow e, 4 * K * #(falsePairs q c A B) :=
          sum_le_sum_of_subset (filter_subset _ _)
      _ = _ := by rw [mul_sum]
  calc e * (#(vBadPrimes e r d c A B) * (2 ^ e - 1))
      ≤ e * (4 * K * ∑ q ∈ primeWindow e, #(falsePairs q c A B)) := Nat.mul_le_mul_left _ h1
    _ = 4 * K * (e * ∑ q ∈ primeWindow e, #(falsePairs q c A B)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (mul_sum_card_falsePairs_le hM)

/-- **The error of the base-`r` reduction** ([ChanItakuraMaYu2026], Theorem 3.4): for
`c = a + b ∈ C` with `a ∈ A`, `b ∈ B`, a uniform prime `q` of the window `[2 ^ e, 2 ^ (e + 1))`
with `r ^ d ≤ 2 ^ e`, and `μ` independent uniform seeds, the reduction misses `c` with probability
at most `#bad / #window + (1 - 3 #P / 4 ^ (e + 2)) ^ μ`. Bad primes are rare by
`card_vBadPrimes_le`, and the window has at least `2 ^ e / (3 (e + 1))` primes
(`two_pow_le_card_primeWindow`). -/
theorem vaverage_miss_le {r d s e μ : ℕ} (hs : s ≤ balancedSize r d) (hre : r ^ d ≤ 2 ^ e)
    {A B C : List ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C)
    (hW : (primeWindow e).Nonempty) :
    (∑ q ∈ primeWindow e, missProbOf (fun q σ => vtrialM r d s (p := q) σ) μ A B C c q) /
        #(primeWindow e) ≤
      (#(vBadPrimes e r d c A B) : ℝ) / #(primeWindow e) +
        (1 - 3 * #(balancedPairs r d) / (4 : ℝ) ^ (e + 2)) ^ μ := by
  set ρ := 1 - 3 * (#(balancedPairs r d) : ℝ) / (4 : ℝ) ^ (e + 2)
  have hP : (#(balancedPairs r d) : ℝ) ≤ (2 : ℝ) ^ e * 2 ^ e := by
    have := (card_balancedPairs_le r d).trans (Nat.pow_le_pow_left hre 2)
    rw [sq] at this
    exact_mod_cast this
  have h4 : (4 : ℝ) ^ (e + 2) = 16 * ((2 : ℝ) ^ e * 2 ^ e) := by
    rw [pow_add, ← mul_pow]; norm_num; ring
  have hρ : 0 ≤ ρ := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ e * 2 ^ e := by positivity
    rw [sub_nonneg, div_le_one (by positivity), h4]
    linarith
  have hbad : (primeWindow e).filter (· ∈ vBadPrimes e r d c A B) = vBadPrimes e r d c A B := by
    ext q
    simp only [mem_filter, vBadPrimes]
    tauto
  rw [← hbad]
  refine average_le_of_good hW (pow_nonneg hρ μ) fun q hq hnb => ?_
  obtain ⟨hprime, hlo, hhi⟩ := mem_primeWindow.mp hq
  have : Fact q.Prime := ⟨hprime⟩
  have hgood : 4 * (#(falsePairs q c (A.filter fun a => decide (Isolated q A a))
      (B.filter fun b => decide (Isolated q B b))) * (r !) ^ (d / r)) ≤ q - 1 := by
    have h1 : ¬ q - 1 < 4 * (#(falsePairs q c A B) * (r !) ^ (d / r)) := fun h =>
      hnb (mem_filter.mpr ⟨hq, h⟩)
    have h2 := card_falsePairs_mono (q := q) (c := c)
      (fun x hx => List.mem_of_mem_filter hx) (fun x hx => List.mem_of_mem_filter hx)
      (A := A) (B := B) (Ag := A.filter fun a => decide (Isolated q A a))
      (Bg := B.filter fun b => decide (Isolated q B b))
    have h3 := Nat.mul_le_mul_right ((r !) ^ (d / r)) h2
    omega
  have hmiss := vmiss_le (μ := μ) hs (hre.trans hlo) ha hb habc hc hgood
  unfold missProbOf
  rw [dite_eq_left_of_eq_true (eq_true hprime)]
  have hqpos : (0 : ℝ) < 4 * (q : ℝ) ^ 2 := by
    have : (0 : ℝ) < q := by exact_mod_cast hprime.pos
    positivity
  refine hmiss.trans (pow_le_pow_left₀ ?_ ?_ μ)
  · have hPq : (#(balancedPairs r d) : ℝ) ≤ (q : ℝ) ^ 2 := by
      have := (card_balancedPairs_le r d).trans (Nat.pow_le_pow_left (hre.trans hlo) 2)
      exact_mod_cast this
    rw [sub_nonneg, div_le_one hqpos]
    linarith
  · have hq2 : (4 : ℝ) * (q : ℝ) ^ 2 ≤ (4 : ℝ) ^ (e + 2) := by
      have : q * q ≤ 2 ^ (e + 1) * 2 ^ (e + 1) := Nat.mul_le_mul hhi.le hhi.le
      have h' : ((q : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (e + 1) * 2 ^ (e + 1) := by
        rw [sq]; exact_mod_cast this
      have h4' : (4 : ℝ) ^ (e + 2) = 4 * ((2 : ℝ) ^ (e + 1) * 2 ^ (e + 1)) := by
        rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num, pow_succ]; ring
      rw [h4']; linarith
    have : 3 * (#(balancedPairs r d) : ℝ) / (4 : ℝ) ^ (e + 2) ≤
        3 * (#(balancedPairs r d) : ℝ) / (4 * (q : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hqpos hq2
    linarith

end Cslib.Algorithms.Lean.SubsetConvThreeSum
