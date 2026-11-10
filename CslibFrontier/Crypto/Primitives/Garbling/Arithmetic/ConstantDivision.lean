/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Nat.ConstantDivision
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Exact division by a public constant in `ℤ/p^(2k+1)`

A garbled arithmetic circuit over `ℤ/p^K` can multiply by public constants for free and can
truncate low base-`p` digits with a bit-decomposition gadget, but it has no division. Li and Liu
[LiLiu2024] emulate `ℤ/N` for an arbitrary modulus `N` inside `ℤ/p^(2k+1)` by computing
`x mod N` for inputs `x < p ^ k` with one constant multiplication and one truncation, following
the multiply-and-shift method of Granlund and Montgomery [GranlundMontgomery1994].

The natural-number identity and the multiplier are in
`CslibFrontier/Foundations/Data/Nat/ConstantDivision.lean`: `Nat.mul_div_pow_eq_div` gives
`⌊(m * x) / p ^ (k + e)⌋ = ⌊x / N⌋` when `p ^ (k + e) ≤ m * N < p ^ (k + e) + p ^ e` and
`x < p ^ k`, and `Nat.constDivMultiplier_bounds` shows that `m = Nat.constDivMultiplier p k N`
satisfies these bounds for `e = ⌈log_p N⌉` and is at most `p ^ (k + 1)`. So the product `m * x`
stays below `p ^ (2k+1)` and multiplying in `ℤ/p^(2k+1)` does not wrap around. Hence `constDiv`,
which multiplies in the ring and keeps the digits above position `k + e`, is exact
(`constDiv_eq_div`), and so is `constMod x = x - N * constDiv x` (`constMod_eq_mod`).

Source mapping (locators follow the ePrint 2023/1584 version of [LiLiu2024] dated 2023-10-13).
Section 4.2 (pp. 21–22) emulates mod-`N` arithmetic in a ring `ℤ/p^K` with `p ^ K > N ^ 2`
through a gate `mod_N`, and on p. 22 defines `div*_N(x) = ⌊(m * x mod p^(2k+1)) / p^(k+kE)⌋` and
`mod*_N(x) = x - N * div*_N(x)` on `ℤ/p^(2k+1)`, exact for `x < p ^ k`, with
`kE = ⌈log_p N⌉` and `m = ⌈p ^ (k + kE) / N⌉`. `constDiv` and `constMod` are these two maps. In the
source `div*_N` is a gate `ℤ/p^(2k+1) → ℤ/p^(2k+1)`; here `constDiv` returns the quotient as a
natural number and `constMod` casts it back into the ring. Only the values of the gates are
formalized: their garbling (constant multiplication and digit truncation as gadgets), the
circuit-level emulation of `ℤ/N`, its cost and its privacy are not.

## Main definitions

* `Cslib.Crypto.Garbling.Arithmetic.constDiv`, `Cslib.Crypto.Garbling.Arithmetic.constMod`:
  division and remainder by `N` in `ℤ/p^(2k+1)`.

## Main results

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

/-- **Division by `N`** from `ℤ/p^(2k+1)`: multiply by `Nat.constDivMultiplier p k N` in the ring,
then keep the base-`p` digits above position `k + ⌈log_p N⌉`, returned as a natural-number
quotient. -/
@[expose] def constDiv (p k N : ℕ) (x : ZMod (p ^ (2 * k + 1))) : ℕ :=
  ((Nat.constDivMultiplier p k N : ZMod (p ^ (2 * k + 1))) * x).val / p ^ (k + Nat.clog p N)

/-- **Remainder modulo `N`** in `ℤ/p^(2k+1)`: `x - N * constDiv p k N x`. -/
@[expose] def constMod (p k N : ℕ) (x : ZMod (p ^ (2 * k + 1))) : ZMod (p ^ (2 * k + 1)) :=
  x - N * (constDiv p k N x : ZMod (p ^ (2 * k + 1)))

variable {p k N : ℕ}

/-- `constDiv` is exact on inputs below `p ^ k`: the product does not wrap around. -/
theorem constDiv_eq_div (hp : 1 < p) (hN : 0 < N) {x : ZMod (p ^ (2 * k + 1))}
    (hx : x.val < p ^ k) : constDiv p k N x = x.val / N := by
  obtain ⟨hlo, hhi, hm⟩ := Nat.constDivMultiplier_bounds k hp hN
  have : NeZero (p ^ (2 * k + 1)) := ⟨(pow_pos (by omega) _).ne'⟩
  have hlt : Nat.constDivMultiplier p k N * x.val < p ^ (2 * k + 1) :=
    calc Nat.constDivMultiplier p k N * x.val ≤ p ^ (k + 1) * x.val :=
          Nat.mul_le_mul_right _ hm
      _ < p ^ (k + 1) * p ^ k := Nat.mul_lt_mul_of_pos_left hx (pow_pos (by omega) _)
      _ = p ^ (2 * k + 1) := by rw [← pow_add]; exact congrArg (p ^ ·) (by omega)
  have hval : ((Nat.constDivMultiplier p k N : ZMod (p ^ (2 * k + 1))) * x).val =
      Nat.constDivMultiplier p k N * x.val := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, Nat.mod_eq_of_lt hlt]
  rw [constDiv, hval]
  exact Nat.mul_div_pow_eq_div (by omega) hN hlo hhi hx

/-- `constMod` is exact on inputs below `p ^ k`. -/
theorem constMod_eq_mod (hp : 1 < p) (hN : 0 < N) {x : ZMod (p ^ (2 * k + 1))}
    (hx : x.val < p ^ k) : constMod p k N x = ((x.val % N : ℕ) : ZMod (p ^ (2 * k + 1))) := by
  have : NeZero (p ^ (2 * k + 1)) := ⟨(pow_pos (by omega) _).ne'⟩
  rw [constMod, constDiv_eq_div hp hN hx, sub_eq_iff_eq_add]
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.mod_add_div x.val N]
  push_cast
  ring

end Cslib.Crypto.Garbling.Arithmetic
