/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.NumberTheory.AKS.Correctness
import Mathlib.Data.Nat.Log

/-!
# The AKS tests with integer thresholds

The AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] compares the multiplicative order
of `n` modulo `r` with `log₂² n` (step 2) and tests the congruence for `a ≤ ⌊√φ(r) log₂ n⌋`
(step 5). A program decides these comparisons more easily with the integer threshold
`c = ⌈log₂ n⌉` in place of `log₂ n`: step 2 asks for `ord_r(n) > c²`, and step 5 tests
`a ≤ ⌊√φ(r) · c⌋ = ⌊√(φ(r) c²)⌋`. This is a standard integer variant. It is still correct, by
Theorem 4.1 of the paper (`Cslib.AKS.prime_iff_passes`): `c² ≥ log₂² n`, so the order condition
is stronger than the paper's, and every prime passes the congruence for every `a`, so testing more
values of `a` loses nothing.

`Cslib.AKS.PassesUpTo n r A` states the tests with the congruence checked for `1 ≤ a ≤ A`; the
paper's `Cslib.AKS.Passes n r` is its case `A = ⌊√φ(r) log₂ n⌋`. For `n ≥ 2`, `ord_r(n) > c²` and
`A ≥ ⌊√φ(r) log₂ n⌋`, it holds exactly when `n` is prime
(`Cslib.AKS.prime_iff_passesUpTo`). The order condition is decided by small powers: for `r ≥ 2`,
`ord_r(n) > L` exactly when `n` is coprime to `r` and no `n^k` with `1 ≤ k ≤ L` is `1` modulo `r`
(`Cslib.AKS.lt_orderOf_iff`).

## Main definitions

* `Cslib.AKS.numTestsNat`: the integer bound `⌊√(φ(r) ⌈log₂ n⌉²)⌋` of step 5.

## Main results

* `Cslib.AKS.logb_le_clog`: `log₂ n ≤ ⌈log₂ n⌉`.
* `Cslib.AKS.numTests_le_numTestsNat`: the integer bound tests at least the paper's values.
* `Cslib.AKS.lt_orderOf_iff`: the order condition by small powers.
* `Cslib.AKS.prime_iff_passesUpTo`: the tests with integer thresholds characterize the primes.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.AKS

/-- The integer bound `⌊√(φ(r) c²)⌋ = ⌊√φ(r) · c⌋` of step 5, with `c = ⌈log₂ n⌉`. -/
def numTestsNat (n r : ℕ) : ℕ := Nat.sqrt (Nat.totient r * Nat.clog 2 n ^ 2)

/-- `log₂ n ≤ ⌈log₂ n⌉`. -/
theorem logb_le_clog (n : ℕ) : Real.logb 2 n ≤ Nat.clog 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.logb_le_iff_le_rpow one_lt_two hn0, Real.rpow_natCast]
  exact_mod_cast Nat.le_pow_clog one_lt_two n

/-- The integer bound tests at least the paper's values: `⌊√φ(r) log₂ n⌋ ≤ ⌊√(φ(r) c²)⌋`. -/
theorem numTests_le_numTestsNat (n r : ℕ) : numTests n r ≤ numTestsNat n r := by
  rw [numTests, numTestsNat, ← Real.nat_floor_real_sqrt_eq_nat_sqrt]
  refine Nat.floor_le_floor ?_
  rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg _)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  exact mul_le_mul_of_nonneg_left (logb_le_clog n) (Real.sqrt_nonneg _)

/-- **The order condition by small powers**: for `r ≥ 2`, the multiplicative order of `n` modulo
`r` exceeds `L` exactly when `n` is coprime to `r` and no `n^k` with `1 ≤ k ≤ L` is `1` modulo
`r`. -/
theorem lt_orderOf_iff {n r L : ℕ} (hr : 2 ≤ r) :
    L < orderOf (n : ZMod r) ↔ n.Coprime r ∧ ∀ k, 1 ≤ k → k ≤ L → n ^ k % r ≠ 1 := by
  have hpow (k : ℕ) : n ^ k % r = 1 ↔ (n : ZMod r) ^ k = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod r), ZMod.natCast_eq_natCast_iff',
      Nat.one_mod_eq_one.mpr (by omega)]
  constructor
  · intro h
    refine ⟨coprime_of_orderOf_pos (by omega), fun k hk hkL hk1 => ?_⟩
    have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one ((hpow k).mp hk1))
    omega
  · rintro ⟨hco, hsmall⟩
    have : NeZero r := ⟨by omega⟩
    have hpos : 0 < orderOf (n : ZMod r) := by
      rw [← ZMod.coe_unitOfCoprime n hco, orderOf_units]
      exact orderOf_pos _
    by_contra hle
    exact hsmall _ hpos (by omega) ((hpow _).mpr (pow_orderOf_eq_one _))

/-- **The tests with integer thresholds characterize the primes**: for `n ≥ 2`, `r` such that the
order of `n` modulo `r` exceeds `⌈log₂ n⌉²`, and `A ≥ ⌊√φ(r) log₂ n⌋`, `n` passes the tests up to
`A` exactly when it is prime. This is [Agrawal, Kayal, Saxena, Theorem 4.1][AKS2004] with integer
thresholds. -/
theorem prime_iff_passesUpTo {n r A : ℕ} (hn : 2 ≤ n)
    (hr : Nat.clog 2 n ^ 2 < orderOf (n : ZMod r)) (hA : numTests n r ≤ A) :
    n.Prime ↔ PassesUpTo n r A := by
  refine ⟨fun hp => passesUpTo_of_prime hp r A, fun ⟨h1, h3, h5⟩ => ?_⟩
  have hlog : Real.logb 2 n ^ 2 < orderOf (n : ZMod r) := by
    have h0 : 0 ≤ Real.logb 2 n :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast (by omega : 1 ≤ n))
    have h1 : Real.logb 2 n ^ 2 ≤ (Nat.clog 2 n : ℝ) ^ 2 :=
      pow_le_pow_left₀ h0 (logb_le_clog n) 2
    have h2 : ((Nat.clog 2 n ^ 2 : ℕ) : ℝ) < orderOf (n : ZMod r) := by exact_mod_cast hr
    push_cast at h2
    linarith
  refine prime_of_passes hn hlog ⟨h1, h3, ?_⟩
  rcases h5 with h | h
  · exact Or.inl h
  · exact Or.inr fun a ha1 ha => h a ha1 (ha.trans hA)

/-- The tests with the integer bound `⌊√(φ(r) ⌈log₂ n⌉²)⌋` characterize the primes. -/
theorem prime_iff_passesUpTo_numTestsNat {n r : ℕ} (hn : 2 ≤ n)
    (hr : Nat.clog 2 n ^ 2 < orderOf (n : ZMod r)) :
    n.Prime ↔ PassesUpTo n r (numTestsNat n r) :=
  prime_iff_passesUpTo hn hr (numTests_le_numTestsNat n r)

end Cslib.AKS
