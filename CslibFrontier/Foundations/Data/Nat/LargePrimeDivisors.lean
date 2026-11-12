/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic

/-!
# Few large primes divide a number

A positive number `n` has at most `log₂ n / k` distinct prime divisors of size at least `2 ^ k`,
since their product divides `n`. This bounds the probability that a random prime of a window of
`k`-bit primes divides a fixed nonzero difference, as in the analysis of random-prime hashing.

## Main results

* `Nat.card_filter_dvd_mul_le_log`: `#{q ∈ s | q ∣ n} * k ≤ log₂ n` for a set `s` of primes of
  size at least `2 ^ k` and `n ≠ 0`.
-/

public section

open Finset

namespace Nat

/-- At most `log₂ n / k` primes of size at least `2 ^ k` divide a nonzero `n`. -/
theorem card_filter_dvd_mul_le_log {s : Finset ℕ} {k : ℕ} (hs : ∀ q ∈ s, q.Prime ∧ 2 ^ k ≤ q)
    {n : ℕ} (hn : n ≠ 0) : #(s.filter (· ∣ n)) * k ≤ Nat.log 2 n := by
  set T := s.filter (· ∣ n)
  have hprod : ∏ q ∈ T, q ∣ n := Finset.prod_primes_dvd n
    (fun q hq => (hs q (mem_filter.mp hq).1).1.prime) fun q hq => (mem_filter.mp hq).2
  have hle : (2 ^ k) ^ #T ≤ n := (Finset.pow_card_le_prod T id (2 ^ k)
    fun q hq => (hs q (mem_filter.mp hq).1).2).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod)
  rw [← pow_mul, mul_comm] at hle
  exact Nat.le_log_of_pow_le (by norm_num) hle

end Nat
