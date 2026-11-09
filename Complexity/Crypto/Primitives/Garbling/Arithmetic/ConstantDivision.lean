/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Exact division by a public constant in `ℤ/p^(2k+1)`

A garbled arithmetic circuit over `ℤ/p^K` can multiply by public constants for free and can
truncate low base-`p` digits with a bit-decomposition gadget, but it has no division. Li and Liu
[LiLiu2024] emulate `ℤ/N` for an arbitrary modulus `N` inside `ℤ/p^(2k+1)` by computing
`x mod N` for inputs `x < p ^ k` with one constant multiplication and one truncation, following
the multiply-and-shift method of Granlund and Montgomery [GranlundMontgomery1994]:
`⌊x / N⌋ = ⌊(m * x) / p ^ (k + e)⌋` for `e = ⌈log_p N⌉` and the multiplier
`m = ⌈p ^ (k + e) / N⌉`.

The arithmetic core is `mul_div_pow_eq_div`: if `p ^ (k + e) ≤ m * N < p ^ (k + e) + p ^ e` and
`x < p ^ k`, then `⌊(m * x) / p ^ (k + e)⌋ = ⌊x / N⌋`. The multiplier `constDivMultiplier`
satisfies these bounds and is at most `p ^ (k + 1)` (`constDivMultiplier_bounds`), so the product
`m * x` stays below `p ^ (2k+1)` and multiplying in `ℤ/p^(2k+1)` does not wrap around. Hence
`constDiv`, which multiplies in the ring and keeps the digits above position `k + e`, is exact
(`constDiv_eq_div`), and so is `constMod x = x - N * constDiv x` (`constMod_eq_mod`).

## Main definitions

* `Cslib.Crypto.Garbling.Arithmetic.constDivMultiplier`: the multiplier `⌈p ^ (k + e) / N⌉`.
* `Cslib.Crypto.Garbling.Arithmetic.constDiv`, `Cslib.Crypto.Garbling.Arithmetic.constMod`:
  division and remainder by `N` in `ℤ/p^(2k+1)`.

## Main results

* `Cslib.Crypto.Garbling.Arithmetic.mul_div_pow_eq_div`: the multiply-and-shift identity.
* `Cslib.Crypto.Garbling.Arithmetic.constDivMultiplier_bounds`: the multiplier's bounds.
* `Cslib.Crypto.Garbling.Arithmetic.constDiv_eq_div`,
  `Cslib.Crypto.Garbling.Arithmetic.constMod_eq_mod`: exactness on inputs below `p ^ k`.

## References

* [T. Granlund, P. L. Montgomery, *Division by Invariant Integers using
  Multiplication*][GranlundMontgomery1994]
* [H. Li, T. Liu, *How to Garble Mixed Circuits that Combine Boolean and Arithmetic
  Computations*][LiLiu2024]
-/

public section

namespace Cslib.Crypto.Garbling.Arithmetic

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

/-- **Division by `N`** from `ℤ/p^(2k+1)`: multiply by `constDivMultiplier p k N` in the ring, then
keep the base-`p` digits above position `k + ⌈log_p N⌉`, returned as a natural-number quotient. -/
@[expose] def constDiv (p k N : ℕ) (x : ZMod (p ^ (2 * k + 1))) : ℕ :=
  ((constDivMultiplier p k N : ZMod (p ^ (2 * k + 1))) * x).val / p ^ (k + Nat.clog p N)

/-- **Remainder modulo `N`** in `ℤ/p^(2k+1)`: `x - N * constDiv p k N x`. -/
@[expose] def constMod (p k N : ℕ) (x : ZMod (p ^ (2 * k + 1))) : ZMod (p ^ (2 * k + 1)) :=
  x - N * (constDiv p k N x : ZMod (p ^ (2 * k + 1)))

variable {p k N : ℕ}

/-- `constDiv` is exact on inputs below `p ^ k`: the product does not wrap around. -/
theorem constDiv_eq_div (hp : 1 < p) (hN : 0 < N) {x : ZMod (p ^ (2 * k + 1))}
    (hx : x.val < p ^ k) : constDiv p k N x = x.val / N := by
  obtain ⟨hlo, hhi, hm⟩ := constDivMultiplier_bounds k hp hN
  have : NeZero (p ^ (2 * k + 1)) := ⟨(pow_pos (by omega) _).ne'⟩
  have hlt : constDivMultiplier p k N * x.val < p ^ (2 * k + 1) :=
    calc constDivMultiplier p k N * x.val ≤ p ^ (k + 1) * x.val := Nat.mul_le_mul_right _ hm
      _ < p ^ (k + 1) * p ^ k := Nat.mul_lt_mul_of_pos_left hx (pow_pos (by omega) _)
      _ = p ^ (2 * k + 1) := by rw [← pow_add]; exact congrArg (p ^ ·) (by omega)
  have hval : ((constDivMultiplier p k N : ZMod (p ^ (2 * k + 1))) * x).val =
      constDivMultiplier p k N * x.val := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, Nat.mod_eq_of_lt hlt]
  rw [constDiv, hval]
  exact mul_div_pow_eq_div (by omega) hN hlo hhi hx

/-- `constMod` is exact on inputs below `p ^ k`. -/
theorem constMod_eq_mod (hp : 1 < p) (hN : 0 < N) {x : ZMod (p ^ (2 * k + 1))}
    (hx : x.val < p ^ k) : constMod p k N x = ((x.val % N : ℕ) : ZMod (p ^ (2 * k + 1))) := by
  have : NeZero (p ^ (2 * k + 1)) := ⟨(pow_pos (by omega) _).ne'⟩
  rw [constMod, constDiv_eq_div hp hN hx, sub_eq_iff_eq_add]
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.mod_add_div x.val N]
  push_cast
  ring

end Cslib.Crypto.Garbling.Arithmetic
