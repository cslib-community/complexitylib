/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/` next to `Bertrand`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import CslibFrontier.Foundations.NumberTheory.CentralBinomPrimes
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# The density of the `n`-bit primes

For every `n > 1`, at least a `1 / (3 n)` fraction of the `n`-bit numbers, those in
`[2 ^ (n - 1), 2 ^ n)`, are prime. This is Theorem 9.32 of [KatzLindell2020], which the book
states without proof. It is what makes the random prime generator of Algorithm 9.34 succeed with
high probability.

For `n ≥ 13` the proof follows Erdős's proof of Bertrand's postulate. Write `m = 2 ^ (n - 1)`.
Erdős's upper bound on the central binomial coefficient `C(2 m, m)` in terms of the number `K` of
primes in `[m, 2 m)` (`Nat.centralBinom_le_pow_card_primes_Ico`, in
`CslibFrontier/Foundations/NumberTheory/CentralBinomPrimes.lean`) gives
`C(2 m, m) ≤ (2 m) ^ √(2 m) 4 ^ (2 m / 3) (2 m) ^ K`. Comparing with `4 ^ m < m C(2 m, m)` bounds
`K` from below. The cases `1 < n < 13` are checked against explicit lists of primes.

## Main results

* `Nat.two_pow_sub_one_le_three_mul_card_primes`: for `1 < n`, the number of primes in
  `[2 ^ (n - 1), 2 ^ n)` is at least `2 ^ (n - 1) / (3 n)`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Theorem 9.32.
-/

public section

open Nat

/-- A duplicate-free list of `n`-bit primes of length at least `2 ^ (n - 1) / (3 n)` certifies
the density bound for `n`. -/
private theorem two_pow_le_card_primes_of_list (n : ℕ) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ p ∈ L, p.Prime ∧ 2 ^ (n - 1) ≤ p ∧ p < 2 ^ n)
    (hlen : 2 ^ (n - 1) ≤ 3 * n * L.length) :
    2 ^ (n - 1) ≤ 3 * n * ((Finset.Ico (2 ^ (n - 1)) (2 ^ n)).filter Nat.Prime).card := by
  refine hlen.trans (Nat.mul_le_mul_left _ ?_)
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨h1, h2, h3⟩ := hL x (List.mem_toFinset.mp hx)
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h2, h3⟩, h1⟩

/-- The density bound for `1 < n < 13`, from explicit lists of primes. -/
private theorem two_pow_le_card_primes_small (n : ℕ) (hn : 1 < n) (h13 : n < 13) :
    2 ^ (n - 1) ≤ 3 * n * ((Finset.Ico (2 ^ (n - 1)) (2 ^ n)).filter Nat.Prime).card := by
  interval_cases n
  · exact two_pow_le_card_primes_of_list 2 [2] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 3 [5] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 4 [11] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 5 [17, 19] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 6 [37, 41] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 7 [67, 71, 73, 79] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 8 [131, 137, 139, 149, 151, 157] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 9
      [257, 263, 269, 271, 277, 281, 283, 293, 307, 311] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 10 [521, 523, 541, 547, 557, 563, 569, 571, 577, 587,
      593, 599, 601, 607, 613, 617, 619, 631] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 11 [1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
      1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187,
      1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)
  · exact two_pow_le_card_primes_of_list 12 [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099,
      2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237,
      2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341,
      2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441,
      2447, 2459, 2467, 2473] (by decide)
      (by simp only [List.forall_mem_cons]; norm_num) (by norm_num)

/-- `9 n² (2 + 2 ^ (n + 1)) ≤ 4 ^ (n - 1)` for `n ≥ 14`. -/
private theorem nine_mul_sq_mul_le_two_pow (n : ℕ) (hn : 14 ≤ n) :
    9 * n ^ 2 * (2 + 2 * 2 ^ n) ≤ 2 ^ (2 * n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show 2 * (n + 1) - 2 = (2 * n - 2) + 2 by omega,
        show 2 ^ (n + 1) = 2 ^ n * 2 from pow_succ 2 n]
    have h1 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc 9 * (n + 1) ^ 2 * (2 + 2 * (2 ^ n * 2))
        ≤ 9 * (2 * n ^ 2) * (2 * (2 + 2 * 2 ^ n)) := by gcongr; omega
      _ = 4 * (9 * n ^ 2 * (2 + 2 * 2 ^ n)) := by ring
      _ ≤ 4 * 2 ^ (2 * n - 2) := by gcongr
      _ = 2 ^ (2 * n - 2 + 2) := by rw [pow_add]; ring

/-- `3 ((n - 1) + n √(2 ^ n)) ≤ 2 ^ (n - 1)` for `n ≥ 13`. -/
private theorem three_mul_add_mul_sqrt_le_two_pow (n : ℕ) (hn : 13 ≤ n) :
    3 * (n - 1 + n * Nat.sqrt (2 ^ n)) ≤ 2 ^ (n - 1) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · have h := Nat.sqrt_lt'.mpr (show 2 ^ 13 < 91 ^ 2 by norm_num)
    generalize Nat.sqrt (2 ^ 13) = s at h ⊢
    norm_num; omega
  · have hs := Nat.sqrt_le' (2 ^ n)
    generalize Nat.sqrt (2 ^ n) = s at hs ⊢
    have hY : (2 ^ (n - 1)) ^ 2 = 2 ^ (2 * n - 2) := by
      rw [← pow_mul]; congr 1; omega
    have hL := nine_mul_sq_mul_le_two_pow n hn
    have h2s : 2 * s ≤ 1 + s ^ 2 := by
      zify; nlinarith [sq_nonneg ((s : ℤ) - 1)]
    have hX : (3 * n * (1 + s)) ^ 2 ≤ (2 ^ (n - 1)) ^ 2 := by
      rw [hY]
      calc (3 * n * (1 + s)) ^ 2 = 9 * n ^ 2 * (1 + 2 * s + s ^ 2) := by ring
        _ ≤ 9 * n ^ 2 * (2 + 2 * 2 ^ n) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ _ := hL
    have hX' : 3 * n * (1 + s) ≤ 2 ^ (n - 1) := le_of_not_gt fun hc =>
      absurd hX (not_le.mpr (Nat.pow_lt_pow_left hc two_ne_zero))
    calc 3 * (n - 1 + n * s) ≤ 3 * n * (1 + s) := by
          have : n - 1 ≤ n := Nat.sub_le n 1
          nlinarith
      _ ≤ _ := hX'

/-- The density bound for `n ≥ 13`, from Erdős's bound on `C(2 m, m)` and
`4 ^ m < m C(2 m, m)` for `m = 2 ^ (n - 1)`. -/
private theorem two_pow_le_card_primes_large (n : ℕ) (hn : 13 ≤ n) :
    2 ^ (n - 1) ≤ 3 * n * ((Finset.Ico (2 ^ (n - 1)) (2 ^ n)).filter Nat.Prime).card := by
  have hnum := three_mul_add_mul_sqrt_le_two_pow n hn
  have h2m : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hm4 : 4 ≤ 2 ^ (n - 1) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h2m] at hnum ⊢
  generalize hmdef : 2 ^ (n - 1) = m at hnum hm4 ⊢
  generalize hK : ((Finset.Ico m (2 * m)).filter Nat.Prime).card = K
  by_contra hlt; push Not at hlt
  have H2 := Nat.four_pow_lt_mul_centralBinom m hm4
  have H3 : m.centralBinom ≤ (2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ K := by
    rw [← hK]; exact Nat.centralBinom_le_pow_card_primes_Ico m (by omega)
  generalize hs : Nat.sqrt (2 * m) = s at hnum H3
  have e0 : 2 * m = 2 ^ n := by rw [← hmdef, h2m]
  have e1 : (2 * m) ^ s = 2 ^ (n * s) := by rw [e0, pow_mul]
  have e2 : (4 : ℕ) ^ (2 * m / 3) = 2 ^ (2 * (2 * m / 3)) := by rw [pow_mul]; norm_num
  have e3 : (2 * m) ^ K = 2 ^ (n * K) := by rw [e0, pow_mul]
  have e4 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  have hE : (n - 1) + n * s + 2 * (2 * m / 3) + n * K ≤ 2 * m := by
    have h3 : 3 * (n * K) < m := by rw [← mul_assoc]; exact hlt
    generalize n * K = B at h3 ⊢
    generalize n * s = A at hnum ⊢
    omega
  have : m * m.centralBinom ≤ 4 ^ m := by
    calc m * m.centralBinom ≤ m * ((2 * m) ^ s * 4 ^ (2 * m / 3) * (2 * m) ^ K) :=
          Nat.mul_le_mul_left _ H3
      _ = 2 ^ ((n - 1) + n * s + 2 * (2 * m / 3) + n * K) := by
          rw [e1, e2, e3, ← hmdef, pow_add, pow_add, pow_add]; ring
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hE
      _ = 4 ^ m := e4.symm
  exact absurd H2 (not_lt.mpr this)

/-- **The density of the `n`-bit primes** ([KatzLindell2020], Theorem 9.32): for `1 < n`, at
least a `1 / (3 n)` fraction of the numbers in `[2 ^ (n - 1), 2 ^ n)` are prime. -/
theorem Nat.two_pow_sub_one_le_three_mul_card_primes {n : ℕ} (hn : 1 < n) :
    2 ^ (n - 1) ≤ 3 * n * ((Finset.Ico (2 ^ (n - 1)) (2 ^ n)).filter Nat.Prime).card := by
  rcases lt_or_ge n 13 with h | h
  · exact two_pow_le_card_primes_small n hn h
  · exact two_pow_le_card_primes_large n h

end
