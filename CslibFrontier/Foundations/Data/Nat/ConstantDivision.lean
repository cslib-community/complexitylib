/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Division by a constant via multiply and shift

Division by a fixed `N` can be computed as a multiplication by a precomputed constant followed by
dropping low digits: `⌊x / N⌋ = ⌊(m * x) / p ^ (k + e)⌋` for every `x < p ^ k`, provided
`p ^ (k + e) ≤ m * N < p ^ (k + e) + p ^ e` (`Nat.mul_div_pow_eq_div`).

Source mapping. Granlund and Montgomery [GranlundMontgomery1994], §4 (unsigned division),
Theorem 4.2, prove the base-`2` case for word size `W` (their `N`) and divisor `d`: if
`2 ^ (W + ℓ) ≤ m * d ≤ 2 ^ (W + ℓ) + 2 ^ ℓ`, then `⌊n / d⌋ = ⌊(m * n) / 2 ^ (W + ℓ)⌋` for
`0 ≤ n < 2 ^ W`. `Nat.mul_div_pow_eq_div` generalizes the radix to any positive `p`, writes `k`
for `W` and `e` for `ℓ`, and uses a strict upper bound, which loses the equality case that
Theorem 4.2 allows. This is the form of Li and Liu [LiLiu2024], Lemma 5 ("Generalization of
\[GM94\]", §4.2, p. 22 of ePrint 2023/1584), with `kI = k` and `kE = e`.

For the multiplier, Li and Liu take `kE = ⌈log_p N⌉` and `m = ⌈p ^ (kI + kE) / N⌉` (same page);
`Nat.constDivMultiplier` is that choice, and `Nat.constDivMultiplier_bounds` proves the hypotheses
of `Nat.mul_div_pow_eq_div` for it. The bound `m ≤ p ^ (k + 1)` in the same lemma is added here: it
keeps `m * x` below `p ^ (2k+1)` in the ring version
`CslibFrontier/Crypto/Primitives/Garbling/Arithmetic/ConstantDivision.lean`.

## Main definitions

* `Nat.constDivMultiplier`: the multiplier `⌈p ^ (k + e) / N⌉` for `e = ⌈log_p N⌉`.

## Main results

* `Nat.mul_div_pow_eq_div`: the multiply-and-shift identity.
* `Nat.constDivMultiplier_bounds`: the multiplier's bounds.

## References

* [T. Granlund, P. L. Montgomery, *Division by Invariant Integers using
  Multiplication*][GranlundMontgomery1994]
* [H. Li, T. Liu, *How to Garble Mixed Circuits that Combine Boolean and Arithmetic
  Computations*][LiLiu2024]
-/

public section

namespace Nat

/-- **Multiply and shift**: if `p ^ (k + e) ≤ m * N < p ^ (k + e) + p ^ e`, then for every
`x < p ^ k` the quotient `⌊(m * x) / p ^ (k + e)⌋` is `⌊x / N⌋`. -/
theorem mul_div_pow_eq_div {p N k e m x : ℕ} (hp : 0 < p) (hN : 0 < N)
    (hlo : p ^ (k + e) ≤ m * N) (hhi : m * N < p ^ (k + e) + p ^ e) (hx : x < p ^ k) :
    m * x / p ^ (k + e) = x / N := by
  set P := p ^ (k + e)
  set q := x / N
  have hP : 0 < P := pow_pos hp _
  have hqN : q * N ≤ x := Nat.div_mul_le_self x N
  have hxq : x < (q + 1) * N := by
    rw [add_mul, one_mul]
    exact Nat.lt_div_mul_add hN
  have hlow : q * P ≤ m * x := by
    refine Nat.le_of_mul_le_mul_left ?_ hN
    calc N * (q * P) = q * N * P := by ring
      _ ≤ x * (m * N) := Nat.mul_le_mul hqN hlo
      _ = N * (m * x) := by ring
  have hhigh : m * x < (q + 1) * P := by
    have hpe : 0 < p ^ e := pow_pos hp e
    have hsplit : P = p ^ k * p ^ e := pow_add p k e
    have h1 : m * N * x < P * (x + 1) := by
      calc m * N * x ≤ (P + (p ^ e - 1)) * x := Nat.mul_le_mul_right x (by omega)
        _ = P * x + (p ^ e - 1) * x := add_mul _ _ _
        _ < P * x + p ^ e * p ^ k := by
          have : (p ^ e - 1) * x < p ^ e * p ^ k :=
            Nat.mul_lt_mul_of_lt_of_lt (by omega) hx
          omega
        _ = P * (x + 1) := by rw [hsplit]; ring
    refine (Nat.mul_lt_mul_left hN).mp ?_
    calc N * (m * x) = m * N * x := by ring
      _ < P * (x + 1) := h1
      _ ≤ P * ((q + 1) * N) := Nat.mul_le_mul_left P hxq
      _ = N * ((q + 1) * P) := by ring
  have h1 : q ≤ m * x / P := (Nat.le_div_iff_mul_le hP).mpr hlow
  have h2 : m * x / P < q + 1 := (Nat.div_lt_iff_lt_mul hP).mpr hhigh
  omega

/-- The multiplier `⌈p ^ (k + e) / N⌉` for `e = ⌈log_p N⌉`. -/
@[expose] def constDivMultiplier (p k N : ℕ) : ℕ := (p ^ (k + Nat.clog p N) + N - 1) / N

/-- The multiplier satisfies the bounds of `mul_div_pow_eq_div` with `e = ⌈log_p N⌉`, and is at
most `p ^ (k + 1)`. -/
theorem constDivMultiplier_bounds {p N : ℕ} (k : ℕ) (hp : 1 < p) (hN : 0 < N) :
    p ^ (k + Nat.clog p N) ≤ constDivMultiplier p k N * N ∧
      constDivMultiplier p k N * N < p ^ (k + Nat.clog p N) + p ^ Nat.clog p N ∧
      constDivMultiplier p k N ≤ p ^ (k + 1) := by
  set e := Nat.clog p N
  set P := p ^ (k + e)
  set m := constDivMultiplier p k N
  have hdiv : m * N + (P + N - 1) % N = P + N - 1 := by
    rw [mul_comm]
    exact Nat.div_add_mod (P + N - 1) N
  have hrem : (P + N - 1) % N < N := Nat.mod_lt _ hN
  have hNe : N ≤ p ^ e := Nat.le_pow_clog hp N
  refine ⟨by omega, by omega, ?_⟩
  rcases Nat.eq_zero_or_pos e with he | he
  · have hN1 : N = 1 := by
      have : N ≤ 1 := by simpa [he] using hNe
      omega
    have hm : m = p ^ k := by simp [m, constDivMultiplier, hN1]
    rw [hm, pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  · obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    have hpc : p ^ c < N := by
      by_contra h
      have : e ≤ c := (Nat.clog_le_iff_le_pow hp).mpr (not_lt.mp h)
      omega
    have hP : P = p ^ (k + 1) * p ^ c := by
      rw [← pow_add]
      exact congrArg (p ^ ·) (by omega)
    have hmN : m * N < (p ^ (k + 1) + 1) * N := by
      have h1 : P + p ^ (k + 1) ≤ p ^ (k + 1) * N := by
        calc P + p ^ (k + 1) = p ^ (k + 1) * (p ^ c + 1) := by rw [hP]; ring
          _ ≤ p ^ (k + 1) * N := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hpc)
      calc m * N ≤ P + N - 1 := by omega
        _ < p ^ (k + 1) * N + N := by omega
        _ = (p ^ (k + 1) + 1) * N := by ring
    have := Nat.lt_of_mul_lt_mul_right hmN
    omega

end Nat
