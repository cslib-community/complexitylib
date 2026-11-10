/-
Copyright (c) 2020 Patrick Stevens, 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey, Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/` next to `Bertrand`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial

/-!
# Erdős's upper bound on the central binomial coefficient

Erdős's proof of Bertrand's postulate bounds the central binomial coefficient `C(2 n, n)` by
factoring it. Its prime factors are at most `2 n`, and the primes in `(2 n / 3, n]` do not divide
it. The primes up to `√(2 n)` contribute at most `2 n` each, the other primes up to `2 n / 3` at
most their product, which is below `4 ^ (2 n / 3)`, and each prime above `n` at most `2 n`. This
file keeps the number of primes above `n` in the bound, which is what a lower bound on the number
of primes in a window of ratio two needs.

## Main results

* `Nat.centralBinom_le_pow_card_primes_Ioc`: for `2 < n`,
  `C(2 n, n) ≤ (2 n) ^ √(2 n) 4 ^ (2 n / 3) (2 n) ^ k`, where `k` is the number of primes in
  `(n, 2 n]`.
* `Nat.centralBinom_le_pow_card_primes_Ico`: the same bound with `k` the number of primes in
  `[n, 2 n)`.

## References

The prime-factorization bound adapts `Nat.centralBinom_le_of_no_bertrand_prime` from
`Mathlib/NumberTheory/Bertrand.lean` (Apache 2.0, by Patrick Stevens and Bolton Bailey), which is
the case `k = 0`, and the version in `CslibFrontier/Foundations/NumberTheory/PrimeWindow.lean`.
-/

public section

open Nat

/-- The primes up to `2 n / 3` contribute at most `(2 n) ^ √(2 n) 4 ^ (2 n / 3)` to the central
binomial coefficient `C(2 n, n)`: those up to `√(2 n)` at most `2 n` each, and the others at
most their product. -/
private theorem prod_range_pow_factorization_centralBinom_le (n : ℕ) (hn : 0 < n) :
    ∏ x ∈ Finset.range (2 * n / 3 + 1), x ^ n.centralBinom.factorization x ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  have hS : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    by_contra hp
    apply h
    dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom hp, _root_.pow_zero]
  change ∏ x ∈ Finset.range (2 * n / 3 + 1), f x ≤ _
  rw [← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (by omega)
    have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by
      rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ (by omega) ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le (fun x hx => (Finset.mem_filter.1 hx).1) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-- A prime power factor of `C(2 n, n)` at a number in `(2 n / 3, 2 n]` is at most `2 n`, and it is
trivial unless the number is a prime in `(n, 2 n]`. -/
private theorem pow_factorization_centralBinom_le_ite {n x : ℕ} (hn : 2 < n)
    (hx : x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1)) :
    x ^ n.centralBinom.factorization x ≤
      if x ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime then 2 * n else 1 := by
  rw [Finset.mem_Ico] at hx
  split_ifs with hS
  · exact pow_factorization_choose_le (by omega)
  by_cases hpx : x.Prime
  · have hxn : x ≤ n := le_of_not_gt fun hgt =>
      hS (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hgt, by omega⟩, hpx⟩)
    rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hxn (by omega), pow_zero]
  · rw [factorization_eq_zero_of_not_prime _ hpx, pow_zero]

/-- The numbers in `(2 n / 3, 2 n]` contribute at most `(2 n) ^ k` to the central binomial
coefficient `C(2 n, n)`, where `k` is the number of primes in `(n, 2 n]`. -/
private theorem prod_Ico_pow_factorization_centralBinom_le (n : ℕ) (hn : 2 < n) :
    ∏ x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), x ^ n.centralBinom.factorization x ≤
      (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  calc ∏ x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), x ^ n.centralBinom.factorization x
      ≤ ∏ x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1),
          (if x ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime then 2 * n else 1) :=
        Finset.prod_le_prod fun x hx => pow_factorization_centralBinom_le_ite hn hx
    _ = ∏ x ∈ (Finset.Ico (2 * n / 3 + 1) (2 * n + 1)).filter
          (· ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime), 2 * n :=
        (Finset.prod_filter _ _).symm
    _ = (2 * n) ^ ((Finset.Ico (2 * n / 3 + 1) (2 * n + 1)).filter
          (· ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime)).card := Finset.prod_const _
    _ ≤ _ := Nat.pow_le_pow_right (by omega)
          (Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2)

/-- **Erdős's upper bound on the central binomial coefficient**, keeping the primes of
`(n, 2 n]`: `C(2 n, n) ≤ (2 n) ^ √(2 n) 4 ^ (2 n / 3) (2 n) ^ k`, where `k` is the number of
primes in `(n, 2 n]`. Mathlib proves the case `k = 0` on the way to Bertrand's postulate
(`Nat.centralBinom_le_of_no_bertrand_prime`). -/
theorem Nat.centralBinom_le_pow_card_primes_Ioc (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  have hsplit : n.centralBinom =
      (∏ x ∈ Finset.range (2 * n / 3 + 1), x ^ n.centralBinom.factorization x) *
        ∏ x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), x ^ n.centralBinom.factorization x := by
    rw [Finset.prod_range_mul_prod_Ico _ (by omega)]
    exact (Nat.prod_pow_factorization_centralBinom n).symm
  rw [hsplit]
  exact mul_le_mul' (prod_range_pow_factorization_centralBinom_le n (by omega))
    (prod_Ico_pow_factorization_centralBinom_le n hn)

/-- Erdős's upper bound on the central binomial coefficient with the primes of `[n, 2 n)`:
`C(2 n, n) ≤ (2 n) ^ √(2 n) 4 ^ (2 n / 3) (2 n) ^ k`, where `k` is the number of primes in
`[n, 2 n)`. It follows from `Nat.centralBinom_le_pow_card_primes_Ioc`, since `2 n` is not
prime. -/
theorem Nat.centralBinom_le_pow_card_primes_Ico (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.Ico n (2 * n)).filter Nat.Prime).card := by
  refine (Nat.centralBinom_le_pow_card_primes_Ioc n hn).trans (Nat.mul_le_mul_left _ ?_)
  refine Nat.pow_le_pow_right (by omega) (Finset.card_le_card fun p hp => ?_)
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨hp.1.1.le, lt_of_le_of_ne hp.1.2 fun h => ?_⟩, hp.2⟩
  have := hp.2.eq_one_or_self_of_dvd 2 ⟨n, h⟩
  omega

end
