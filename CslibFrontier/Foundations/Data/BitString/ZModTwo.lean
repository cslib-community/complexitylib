/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The two-element field `ZMod 2` as bits

Bits form the two-element field under exclusive or and conjunction (Mathlib's
`BooleanRing Bool`). The computable ring isomorphism `Cslib.BitString.bitEquiv : ZMod 2 ≃+* Bool`
identifies `ZMod 2` with `Bool`; it equals Mathlib's `ZMod.ringEquivOfPrime`
(`Cslib.BitString.bitEquiv_eq_ringEquivOfPrime`), and its inverse reads a bit as `0` or `1` in
`ZMod 2`, matching `Cslib.BitString.bitVal (ZMod 2)` (`Cslib.BitString.bitEquiv_symm_apply`).

## Main definitions

* `Cslib.BitString.bitEquiv`: the computable ring isomorphism `ZMod 2 ≃+* Bool`.

## Main results

* `Cslib.BitString.bitEquiv_eq_ringEquivOfPrime`: `bitEquiv` is `ZMod.ringEquivOfPrime Bool`.
* `Cslib.BitString.bitEquiv_symm_apply`, `Cslib.BitString.bitEquiv_symm_false`,
  `Cslib.BitString.bitEquiv_symm_true`: `bitEquiv.symm` reads `false` as `0` and `true` as `1`.
* `Cslib.BitString.bitEquiv_symm_foldl_xor`: `bitEquiv.symm` turns a fold over `xor` into a sum.

## References

* [R. Lidl, H. Niederreiter, *Finite Fields*, Chapter 1][LidlNiederreiter1997]
-/

@[expose] public section

namespace Cslib.BitString

/-- The two-element field `𝔽₂ = ZMod 2` as bits: the unique ring isomorphism `ZMod 2 ≃+* Bool`. -/
def bitEquiv : ZMod 2 ≃+* Bool where
  toFun c := decide (c = 1)
  invFun a := (a.toNat : ZMod 2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide
  map_add' := by decide

/-- `bitEquiv` is Mathlib's `ZMod.ringEquivOfPrime` for the two-element field `Bool`, as a
computable definition. -/
theorem bitEquiv_eq_ringEquivOfPrime :
    bitEquiv = ZMod.ringEquivOfPrime Bool Nat.prime_two (by simp) :=
  RingEquiv.toRingHom_injective (RingHom.ext_zmod _ _)

/-- `bitEquiv.symm` reads a bit as `0` or `1`, as `Cslib.BitString.bitVal` does. -/
theorem bitEquiv_symm_apply (b : Bool) : bitEquiv.symm b = bitVal (ZMod 2) b := by
  cases b <;> rfl

/-- `bitEquiv.symm` reads the bit `false` as `0`. -/
@[simp]
theorem bitEquiv_symm_false : bitEquiv.symm false = 0 := rfl

/-- `bitEquiv.symm` reads the bit `true` as `1`. -/
@[simp]
theorem bitEquiv_symm_true : bitEquiv.symm true = 1 := rfl

/-- The inverse ring isomorphism maps a fold over `xor` to the sum of the mapped bits. -/
theorem bitEquiv_symm_foldl_xor (l : List Bool) :
    bitEquiv.symm (l.foldl xor false) = (l.map bitEquiv.symm).sum := by
  rw [← map_list_sum]
  congr 1
  simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]

end Cslib.BitString
