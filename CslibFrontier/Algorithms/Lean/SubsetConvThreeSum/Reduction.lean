/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialReduction
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# The reduction from 3SUM to selected entries of subset convolution

[ChanItakuraMaYu2026], Theorem 2.3: decide `c ∈ A + B` for every query `c ∈ C` by hashing modulo
a random prime `p` and `μ` trials of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Trial`.
`threeSumM d t s p seeds A B C` is the algorithm for given random choices: the prime `p` and the
list `seeds` of the trials' seeds.

1. It counts the residues of `A` and `B` modulo `p` and splits off the elements that share their
   residue class (`A_bad`, `B_bad`; `isolatedM`).
2. It reports every `c ∈ A_bad + B` or `c ∈ A + B_bad` (the sums are listed exactly).
3. It runs one trial per seed on the isolated elements and reports the accepted queries.

`threeSumM` is the reduction `reduceM` of
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialReduction` for the trials `trialM`, and
every result below is an instance of a lemma proved there for an arbitrary trial program; the
base-`r` reduction of Theorem 3.4 (`vthreeSumM`) is the other instance.

## Results

* **Soundness** (`exists_add_eq_of_mem_ret_threeSumM`): every reported `c` is a sum `a + b` with
  `a ∈ A`, `b ∈ B`, for every prime and all seeds; the error is one-sided.
* **What it returns** (`ret_threeSumM`) and its **exact cost** (`time_threeSumM`).
* **Error probability** (`miss_le`): for `c ∈ A + B`, a prime `p` of the window `[2 ^ d, 2 ^ (d+1))`
  that is good for `c`, and `μ` independent uniform seeds, the probability that `c` is not reported
  is at most `(1 - 3 #P / (4 p ^ 2)) ^ μ`, where `#P = (d choose 2 t) (2 t choose t)`
  (`card_rankedPairs`). Bad primes are rare by `card_badPrimes_le` and
  `two_pow_le_card_primeWindow`. Averaged over a uniform prime of the window
  (`average_miss_le`), the error is at most `#bad / #window + (1 - 3 #P / 4 ^ (d + 2)) ^ μ`.

The parameter choices, the expected cost, the conversion to worst-case time and the truly
subquadratic exponent of Corollary 2.4 are in
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Corollary`.

## Cost model

The `TimeM` unit-cost model of `CslibFrontier.Algorithms.Lean.TrimmedYates`: residues, numbers
below `N ^ O(1)` and sets of at most `d` coordinates are words and dictionary operations cost one
tick. Charged: one tick per element when counting residues and when splitting, one per listed bad
sum and per inserted reported value, one per query in the final look-up, and the ticks of the
trials (`time_trialM`). The random choices are inputs; sampling them is uncharged. The cost depends
on the random choices through `|A_bad|`, `|B_bad|`, `|A*|`, `|B*|`, `|C*|` and the number of
reported values; `time_threeSumM` states it exactly. Their expectations are bounded in
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Expectation`.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.threeSumM`, `missProb`.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.exists_add_eq_of_mem_ret_threeSumM`: soundness.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.trialSpec_trialM`, `ret_threeSumM`,
  `mem_ret_threeSumM_or_isolated`, `time_threeSumM`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.miss_le`, `average_miss_le`: error probability.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Cslib.Algorithms.Lean.TimeM

variable {p : ℕ}

/-- **The reduction** for given random choices: the prime `p` and the seeds of the trials. This is
the reduction `reduceM` of `TrialReduction` for the base-`2` trials `trialM`. -/
@[expose] def threeSumM (d t s p : ℕ) (seeds : List (Seed p)) (A B C : List ℕ) :
    TimeM ℕ (List ℕ) :=
  reduceM (fun σ => trialM d t s σ) seeds A B C

/-- The base-`2` trials return their accepted queries. -/
theorem trialSpec_trialM {d t s : ℕ} (hs : s ≤ 2 * t) :
    TrialSpec (p := p) (fun σ => trialM d t s σ) fun σ Ag Bg c => Accepts d t σ Ag Bg c :=
  fun σ Ag Bg C => ret_trialM σ Ag Bg C hs

/-- **What the reduction returns**: the queries of `C` that are bad sums or accepted by a trial. -/
theorem ret_threeSumM {d t s p : ℕ} (seeds : List (Seed p)) (A B C : List ℕ) (hs : s ≤ 2 * t) :
    (threeSumM d t s p seeds A B C).ret = C.filter fun c => decide (BadHit p A B c ∨
      ∃ σ ∈ seeds, Accepts d t σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) :=
  ret_reduceM (trialSpec_trialM hs) seeds A B C

/-- **Soundness of the reduction** (one-sided error): every reported query is a sum `a + b` with
`a ∈ A` and `b ∈ B`, for every modulus and all seeds. -/
theorem exists_add_eq_of_mem_ret_threeSumM {d t s p : ℕ} {seeds : List (Seed p)}
    {A B C : List ℕ} (hs : s ≤ 2 * t) {c : ℕ} (hc : c ∈ (threeSumM d t s p seeds A B C).ret) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = c :=
  exists_add_eq_of_mem_ret_reduceM (trialSpec_trialM hs)
    (fun _ _ _ _ h => exists_add_eq_of_accepts h) hc

/-- **Completeness for given random choices**: a sum `c = a + b` with `a ∈ A`, `b ∈ B` that is in
`C` is reported if it is a bad sum or some trial accepts it, and otherwise `a` and `b` are
isolated. -/
theorem mem_ret_threeSumM_or_isolated {d t s p : ℕ} (seeds : List (Seed p)) {A B C : List ℕ}
    (hs : s ≤ 2 * t) {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C) :
    c ∈ (threeSumM d t s p seeds A B C).ret ∨ (Isolated p A a ∧ Isolated p B b ∧
      ∀ σ ∈ seeds, ¬ Accepts d t σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) :=
  mem_ret_reduceM_or_isolated (trialSpec_trialM hs) seeds ha hb habc hc

/-- **The cost of the reduction**, exactly: `3 (|A| + |B|)` ticks to split off `A_bad` and
`B_bad`, the ticks of the trials (`time_trialM`), one tick per listed bad sum
(`|A_bad| |B| + |A| |B_bad|`) and per reported value of a trial, and one per query. -/
theorem time_threeSumM {d t s p : ℕ} (seeds : List (Seed p)) (A B C : List ℕ) (hs : s ≤ 2 * t) :
    let Ag := A.filter fun a => decide (Isolated p A a)
    let Bg := B.filter fun b => decide (Isolated p B b)
    (threeSumM d t s p seeds A B C).time = 3 * A.length + 3 * B.length +
      (seeds.map fun σ => (trialM d t s σ Ag Bg C).time).sum +
      ((A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
        A.length * (B.filter fun b => decide (¬ Isolated p B b)).length) +
      (seeds.map fun σ => (C.filter fun c => decide (Accepts d t σ Ag Bg c)).length).sum +
      C.length :=
  time_reduceM (trialSpec_trialM hs) seeds A B C

/-! ### Error probability -/

theorem card_rankedPairs_le (d t : ℕ) : #(rankedPairs d t) ≤ 2 ^ d * 2 ^ d := by
  refine (card_filter_le _ _).trans ?_
  rw [card_product, card_range]

/-- **The miss probability for a good prime** ([ChanItakuraMaYu2026], Theorem 2.3): let
`c = a + b ∈ C` with `a ∈ A`, `b ∈ B`, let `p ≥ 2 ^ d` be prime and good for `c`
(`4 #L (2 t choose t) ≤ p - 1`). Over `μ` independent uniform seeds, the reduction misses `c`
with probability at most `(1 - 3 #P / (4 p ^ 2)) ^ μ`, where `#P = (d choose 2 t) (2 t choose t)`
(`card_rankedPairs`). -/
theorem miss_le [Fact p.Prime] {d t s μ : ℕ} (hs : s ≤ 2 * t) (hp : 2 ^ d ≤ p) {A B C : List ℕ}
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C)
    (hgood : 4 * (#(falsePairs p c (A.filter fun a => decide (Isolated p A a))
      (B.filter fun b => decide (Isolated p B b))) * (2 * t).choose t) ≤ p - 1) :
    (#((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (threeSumM d t s p (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds p) : ℝ) ^ μ ≤
      (1 - 3 * #(rankedPairs d t) / (4 * (p : ℝ) ^ 2)) ^ μ :=
  reduceM_miss_le (trialSpec_trialM hs)
    ((card_rankedPairs_le d t).trans (by rw [sq]; exact Nat.mul_le_mul hp hp)) ha hb habc hc
    fun hia hib => four_mul_card_accepts_ge hp (fun _ hx => List.mem_of_mem_filter hx)
      (fun _ hx => List.mem_of_mem_filter hx) (List.mem_filter.mpr ⟨ha, decide_eq_true hia⟩)
      (List.mem_filter.mpr ⟨hb, decide_eq_true hib⟩) hia hib habc hgood

/-- The probability that the reduction misses `c` over `μ` uniform seeds, for the modulus `q`
(`0` if `q` is not prime). -/
@[expose] noncomputable def missProb (d t s μ : ℕ) (A B C : List ℕ) (c q : ℕ) : ℝ :=
  missProbOf (fun _ σ => trialM d t s σ) μ A B C c q

/-- At a prime modulus, the miss probability is the fraction of missing seed tuples. -/
theorem missProb_eq_of_prime [Fact p.Prime] (d t s μ : ℕ) (A B C : List ℕ) (c : ℕ) :
    missProb d t s μ A B C c p =
      (#((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (threeSumM d t s p (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds p) : ℝ) ^ μ := by
  unfold missProb missProbOf
  rw [dite_eq_left_of_eq_true (eq_true Fact.out)]
  rfl

theorem missProb_le_one (d t s μ : ℕ) (A B C : List ℕ) (c q : ℕ) :
    missProb d t s μ A B C c q ≤ 1 :=
  missProbOf_le_one _ μ A B C c q

/-- **The error of the reduction** ([ChanItakuraMaYu2026], Theorem 2.3): for `c = a + b ∈ C` with
`a ∈ A`, `b ∈ B`, a uniform prime `q` of the window `[2 ^ d, 2 ^ (d + 1))` and `μ` independent
uniform seeds, the reduction misses `c` with probability at most
`#bad / #window + (1 - 3 #P / 4 ^ (d + 2)) ^ μ`. Bad primes are rare by `card_badPrimes_le`;
`#P = (d choose 2 t) (2 t choose t)` (`card_rankedPairs`); the window has at least
`2 ^ d / (3 (d + 1))` primes (`two_pow_le_card_primeWindow`). -/
theorem average_miss_le {d t s μ : ℕ} (hs : s ≤ 2 * t) {A B C : List ℕ} {a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C)
    (hW : (primeWindow d).Nonempty) :
    (∑ q ∈ primeWindow d, missProb d t s μ A B C c q) / #(primeWindow d) ≤
      (#(badPrimes d t c A B) : ℝ) / #(primeWindow d) +
        (1 - 3 * #(rankedPairs d t) / (4 : ℝ) ^ (d + 2)) ^ μ :=
  average_miss_le_of_window hW (filter_subset _ _) (card_rankedPairs_le d t)
    fun _ hq hnb => missProbOf_le_of_prime (mem_primeWindow.mp hq).1 fun _ =>
      miss_le hs (mem_primeWindow.mp hq).2.1 ha hb habc hc
        (good_of_not_mem_badPrimesOf hq hnb)

end Cslib.Algorithms.Lean.SubsetConvThreeSum
