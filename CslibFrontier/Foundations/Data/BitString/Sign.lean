/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/BitString.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bits as numbers: `0`/`1` values and `±1` signs

Analysis on the Boolean cube reads a bit in two ways. As a value in a commutative ring `R`, a bit
is `0` or `1` (`BitString.bitVal`); this is the reading of multilinear polynomials and of `𝔽₂`.
As a real sign, a bit is `1` or `-1` (`BitString.signVal`), with `false ↦ 1` and `true ↦ -1`;
this is the reading of Fourier analysis, under which exclusive or becomes multiplication
(`BitString.signVal_xor`) [O'Donnell, Chapter 1][ODonnell2014]. The two readings are related by
`signVal b = 1 - 2 bitVal b` (`BitString.signVal_eq_one_sub_two_mul_bitVal`).

This module holds only these atoms, so that modules which read bits as numbers need not import
the Fourier or low-degree theory built on them.

## Main definitions

* `Cslib.BitString.bitVal`: a bit read as `0` or `1` in a commutative ring.
* `Cslib.BitString.signVal`: a bit read as a real sign, `false ↦ 1` and `true ↦ -1`.

## Main results

* `Cslib.BitString.signVal_xor`, `Cslib.BitString.neg_one_pow_toNat_xor`: the sign of an
  exclusive or is the product of the signs.
* `Cslib.BitString.signVal_mul_self`, `Cslib.BitString.abs_signVal`,
  `Cslib.BitString.signVal_mul_signVal`, `Cslib.BitString.sq_signVal_sub_signVal`: arithmetic of
  signs.
* `Cslib.BitString.signVal_eq_neg_one_pow`,
  `Cslib.BitString.neg_one_pow_toNat_eq_one_sub_two_mul_bitVal`,
  `Cslib.BitString.signVal_eq_one_sub_two_mul_bitVal`: the readings as powers of `-1` and as
  each other.
* `Cslib.BitString.bitVal_pow`, `Cslib.BitString.bitVal_not`: a bit read in `R` is idempotent,
  and negation is `1 - b`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

/-! ### Bits read as `0` or `1` -/

section BitVal

variable (R : Type*) [CommRing R]

/-- A bit read as `0` or `1` in `R`. -/
def bitVal (b : Bool) : R :=
  if b then 1 else 0

variable {R}

/-- The bit `true` reads as `1`. -/
@[simp] theorem bitVal_true : bitVal R true = 1 := rfl

/-- The bit `false` reads as `0`. -/
@[simp] theorem bitVal_false : bitVal R false = 0 := rfl

/-- A bit read in `R` is idempotent. -/
theorem bitVal_pow (b : Bool) {k : ℕ} (hk : k ≠ 0) : bitVal R b ^ k = bitVal R b := by
  cases b <;> simp [bitVal, hk]

/-- Negating a bit sends its value `v` in `R` to `1 - v`. -/
theorem bitVal_not (b : Bool) : bitVal R (!b) = 1 - bitVal R b := by
  cases b <;> simp [bitVal]

end BitVal

/-! ### Bits read as signs -/

/-- A bit read as a real sign: `false ↦ 1` and `true ↦ -1`. -/
def signVal (b : Bool) : ℝ :=
  if b then -1 else 1

/-- The bit `false` reads as the sign `1`. -/
@[simp] theorem signVal_false : signVal false = 1 := rfl

/-- The bit `true` reads as the sign `-1`. -/
@[simp] theorem signVal_true : signVal true = -1 := rfl

/-- Negating a bit negates its sign. -/
@[simp] theorem signVal_not (b : Bool) : signVal (!b) = -signVal b := by
  cases b <;> simp

/-- A sign squares to one. -/
theorem signVal_mul_self (b : Bool) : signVal b * signVal b = 1 := by
  cases b <;> simp

/-- A sign has absolute value one. -/
@[simp] theorem abs_signVal (b : Bool) : |signVal b| = 1 := by
  cases b <;> simp

/-- The product of two signs records whether the bits agree. -/
theorem signVal_mul_signVal (a b : Bool) : signVal a * signVal b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp

/-- The sign of an exclusive or is the product of the signs. -/
@[simp] theorem signVal_xor (a b : Bool) : signVal (a ^^ b) = signVal a * signVal b := by
  cases a <;> cases b <;> simp

/-- The squared difference of two signs is two minus twice their product. -/
theorem sq_signVal_sub_signVal (a b : Bool) :
    (signVal a - signVal b) ^ 2 = 2 - 2 * (signVal a * signVal b) := by
  cases a <;> cases b <;> norm_num

/-- The real sign of a bit as a power of `-1`. -/
theorem signVal_eq_neg_one_pow (b : Bool) : signVal b = (-1) ^ b.toNat := by
  cases b <;> simp

/-! ### Signs as powers of `-1` in a commutative ring -/

section CommRing

variable {R : Type*} [CommRing R]

/-- The sign `(-1) ^ b` of an exclusive or is the product of the signs. -/
theorem neg_one_pow_toNat_xor (a b : Bool) :
    (-1 : R) ^ (a ^^ b).toNat = (-1) ^ a.toNat * (-1) ^ b.toNat := by
  cases a <;> cases b <;> simp

/-- The sign `(-1) ^ b` of a bit, as a polynomial in the bit: `1 - 2 b`. -/
theorem neg_one_pow_toNat_eq_one_sub_two_mul_bitVal (b : Bool) :
    (-1 : R) ^ b.toNat = 1 - 2 * bitVal R b := by
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, bitVal_false,
    bitVal_true] <;> ring

end CommRing

/-- The real sign of a bit is `1 - 2 b` for the bit `b` read as `0` or `1`. -/
theorem signVal_eq_one_sub_two_mul_bitVal (b : Bool) : signVal b = 1 - 2 * bitVal ℝ b := by
  rw [signVal_eq_neg_one_pow, neg_one_pow_toNat_eq_one_sub_two_mul_bitVal]

end Cslib.BitString
