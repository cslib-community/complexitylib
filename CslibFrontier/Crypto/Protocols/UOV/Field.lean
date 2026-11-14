/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import CslibFrontier.Computability.Complexity.AffineDisperser.BinaryPolynomial
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.FieldTheory.Finite.Trinomial

/-!
# UOV concrete binary fields and element encodings

UOV v3.0 uses
`F16 = F2[X] / (X ^ 4 + X + 1)` and
`F256 = F2[X] / (X ^ 8 + X ^ 4 + X ^ 3 + X + 1)`.  These are exactly the existing
`Cslib.BinaryField 4` and `Cslib.BinaryField 8`: their least-code irreducible moduli have binary
codes `19 = 0b10011` and `283 = 0b100011011`, respectively.

The source stores a field element as the coefficients of its polynomial-basis representative.
Thus bit zero is the constant coefficient and the most significant bit of a nibble or byte is the
coefficient of `X ^ 3` or `X ^ 7`.  The equivalences below are the existing power-basis
`Cslib.BinaryField.equivBits` followed by the little-endian numbering
`Cslib.BitString.equivFin`.  For `F16`, two elements are packed into one byte with the first
element in the least-significant nibble [UOV2026, Section 3.3, p. 19].

This module identifies only the concrete fields and individual-element/pair encodings.  It does
not define UOV keys, matrices, vector serialization, signing, retry behavior, assumptions, or
security games.

## Main definitions

* `Cslib.Crypto.UOV.F16`, `Cslib.Crypto.UOV.F256`: the two UOV implementation fields.
* `Cslib.Crypto.UOV.f16EquivNibble`: polynomial-basis encoding of `F16` by a nibble.
* `Cslib.Crypto.UOV.f256EquivByte`: polynomial-basis encoding of `F256` by a byte.
* `Cslib.Crypto.UOV.f16PairEquivByte`: low-nibble-first packing of two `F16` elements.

## Main results

* `Cslib.Crypto.UOV.f16_modulus`, `Cslib.Crypto.UOV.f256_modulus`: the existing binary fields use
  the exact UOV irreducible polynomials.
* `Cslib.Crypto.UOV.val_f16EquivNibble_mk_polyOfCode`,
  `Cslib.Crypto.UOV.val_f256EquivByte_mk_polyOfCode`: bounded polynomial codes round-trip through
  the source encodings.
* `Cslib.Crypto.UOV.val_f16PairEquivByte`: the first element occupies the low nibble.
* `Cslib.Crypto.UOV.val_f16EquivNibble_root_pow_four`,
  `Cslib.Crypto.UOV.val_f256EquivByte_root_pow_eight`: convention-sensitive evaluations of the
  two quotient relations.

## References

* [W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting
  Documentation*, v3.0, Section 3.3, p. 19][UOV2026]
-/

@[expose] public section

namespace Cslib.Crypto.UOV

open BitString Polynomial

/-- UOV's `F16`, using the library's explicit degree-four binary field. -/
abbrev F16 := BinaryField 4

/-- UOV's `F256`, using the library's explicit degree-eight binary field. -/
abbrev F256 := BinaryField 8

/-- The least-code degree-four irreducible binary polynomial has code `19 = 0b10011`. -/
theorem f16_modulus_code : leastIrreducible 4 = polyOfCode 19 := by
  rw [← AffineDisperser.polyOfCode_leastIrreducibleCode (B := 32) (by norm_num) (by norm_num),
    show AffineDisperser.leastIrreducibleCode 32 4 = 19 by decide]

/-- `BinaryField 4` uses UOV's modulus `X ^ 4 + X + 1`. -/
theorem f16_modulus : leastIrreducible 4 = X ^ 4 + X + 1 := by
  rw [f16_modulus_code]
  norm_num [polyOfCode_eq_C_add_X_mul, polyOfCode_zero] <;> ring

/-- The least-code degree-eight irreducible binary polynomial has code
`283 = 0b100011011`. -/
theorem f256_modulus_code : leastIrreducible 8 = polyOfCode 283 := by
  rw [← AffineDisperser.polyOfCode_leastIrreducibleCode (B := 512) (by norm_num) (by norm_num),
    show AffineDisperser.leastIrreducibleCode 512 8 = 283 by decide]

/-- `BinaryField 8` uses UOV's modulus `X ^ 8 + X ^ 4 + X ^ 3 + X + 1`. -/
theorem f256_modulus : leastIrreducible 8 = X ^ 8 + X ^ 4 + X ^ 3 + X + 1 := by
  rw [f256_modulus_code]
  norm_num [polyOfCode_eq_C_add_X_mul, polyOfCode_zero] <;> ring

/-- UOV's polynomial-basis encoding of an `F16` element as one nibble.  Coordinate zero is the
constant coefficient. -/
noncomputable def f16EquivNibble : F16 ≃ Fin 16 :=
  (BinaryField.equivBits (w := 4) (by norm_num)).toEquiv.trans (BitString.equivFin 4)

/-- UOV's polynomial-basis encoding of an `F256` element as one byte.  Coordinate zero is the
constant coefficient. -/
noncomputable def f256EquivByte : F256 ≃ Fin 256 :=
  (BinaryField.equivBits (w := 8) (by norm_num)).toEquiv.trans (BitString.equivFin 8)

private theorem val_binaryFieldEquivFin_mk_polyOfCode {w c : ℕ} (hw : w ≠ 0)
    (hc : c < 2 ^ w) :
    (((BinaryField.equivBits hw).toEquiv.trans (BitString.equivFin w))
      (AdjoinRoot.mk (leastIrreducible w) (polyOfCode c))).val = c := by
  have hbits :
      BinaryField.equivBits hw (AdjoinRoot.mk (leastIrreducible w) (polyOfCode c)) =
        (BitString.equivFin w).symm ⟨c, hc⟩ := by
    ext j
    rw [BinaryField.equivBits_mk hw (degree_polyOfCode_lt hc) j, coeff_polyOfCode,
      RingEquiv.apply_symm_apply, BitString.equivFin_symm_apply]
  change (BitString.equivFin w
    (BinaryField.equivBits hw (AdjoinRoot.mk (leastIrreducible w) (polyOfCode c)))).val = c
  rw [hbits, Equiv.apply_symm_apply]

/-- A bounded polynomial code is unchanged by UOV's `F16` nibble encoding. -/
theorem val_f16EquivNibble_mk_polyOfCode {c : ℕ} (hc : c < 16) :
    (f16EquivNibble (AdjoinRoot.mk (leastIrreducible 4) (polyOfCode c))).val = c := by
  have hc' : c < 2 ^ 4 := by simpa using hc
  simpa only [f16EquivNibble] using
    val_binaryFieldEquivFin_mk_polyOfCode (w := 4) (c := c) (by norm_num) hc'

/-- Decoding a nibble gives the class of the binary polynomial with that code. -/
theorem f16EquivNibble_symm_apply (c : Fin 16) :
    f16EquivNibble.symm c = AdjoinRoot.mk (leastIrreducible 4) (polyOfCode c.val) := by
  apply f16EquivNibble.injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (val_f16EquivNibble_mk_polyOfCode c.isLt).symm

/-- A bounded polynomial code is unchanged by UOV's `F256` byte encoding. -/
theorem val_f256EquivByte_mk_polyOfCode {c : ℕ} (hc : c < 256) :
    (f256EquivByte (AdjoinRoot.mk (leastIrreducible 8) (polyOfCode c))).val = c := by
  have hc' : c < 2 ^ 8 := by simpa using hc
  simpa only [f256EquivByte] using
    val_binaryFieldEquivFin_mk_polyOfCode (w := 8) (c := c) (by norm_num) hc'

/-- Decoding a byte gives the class of the binary polynomial with that code. -/
theorem f256EquivByte_symm_apply (c : Fin 256) :
    f256EquivByte.symm c = AdjoinRoot.mk (leastIrreducible 8) (polyOfCode c.val) := by
  apply f256EquivByte.injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (val_f256EquivByte_mk_polyOfCode c.isLt).symm

/-- Pack two `F16` elements into one byte.  The first element is the low nibble and the second is
the high nibble, as in UOV v3.0, Section 3.3. -/
noncomputable def f16PairEquivByte : F16 × F16 ≃ Fin 256 :=
  ((Equiv.prodCongr f16EquivNibble f16EquivNibble).trans (Equiv.prodComm _ _)).trans
    finProdFinEquiv

/-- Low-nibble-first packing has unsigned value `low + 16 * high`. -/
theorem val_f16PairEquivByte (low high : F16) :
    (f16PairEquivByte (low, high)).val =
      (f16EquivNibble low).val + 16 * (f16EquivNibble high).val :=
  rfl

/-- The polynomial-basis generator `X` has nibble value `2`, not the bit-reversed value `4`. -/
theorem val_f16EquivNibble_root :
    (f16EquivNibble (AdjoinRoot.root (leastIrreducible 4))).val = 2 := by
  have h := val_f16EquivNibble_mk_polyOfCode (c := 2) (by norm_num)
  have hpoly : polyOfCode 2 = X := by
    norm_num [polyOfCode_eq_C_add_X_mul, polyOfCode_zero]
  simpa only [hpoly, AdjoinRoot.mk_X] using h

/-- The multiplicative identity has nibble value `1`. -/
theorem val_f16EquivNibble_one : (f16EquivNibble (1 : F16)).val = 1 := by
  have h := val_f16EquivNibble_mk_polyOfCode (c := 1) (by norm_num)
  have hpoly : polyOfCode 1 = 1 := by
    norm_num [polyOfCode_eq_C_add_X_mul, polyOfCode_zero]
  simpa only [hpoly, AdjoinRoot.mk_C] using h

/-- In UOV's `F16`, the quotient relation is `X ^ 4 = X + 1`, encoded as `0x3`. -/
theorem val_f16EquivNibble_root_pow_four :
    (f16EquivNibble (AdjoinRoot.root (leastIrreducible 4) ^ 4)).val = 3 := by
  have hroot : AdjoinRoot.root (leastIrreducible 4) ^ 4 =
      AdjoinRoot.mk (leastIrreducible 4) (polyOfCode 3) := by
    change (AdjoinRoot.mk (leastIrreducible 4) X) ^ 4 = _
    rw [← map_pow, ← sub_eq_zero, CharTwo.sub_eq_add, ← map_add]
    have hpoly : X ^ 4 + polyOfCode 3 = leastIrreducible 4 := by
      rw [f16_modulus]
      norm_num [polyOfCode_eq_C_add_X_mul, polyOfCode_zero] <;> ring
    rw [hpoly, AdjoinRoot.mk_self]
  rw [hroot, val_f16EquivNibble_mk_polyOfCode (by norm_num)]

/-- The polynomial-basis generator `X` has byte value `2`, not the bit-reversed value `64`. -/
theorem val_f256EquivByte_root :
    (f256EquivByte (AdjoinRoot.root (leastIrreducible 8))).val = 2 := by
  have h := val_f256EquivByte_mk_polyOfCode (c := 2) (by norm_num)
  have hpoly : polyOfCode 2 = X := by
    norm_num [polyOfCode_eq_C_add_X_mul, polyOfCode_zero]
  simpa only [hpoly, AdjoinRoot.mk_X] using h

/-- In UOV's `F256`, the quotient relation is
`X ^ 8 = X ^ 4 + X ^ 3 + X + 1`, encoded as `0x1b`. -/
theorem val_f256EquivByte_root_pow_eight :
    (f256EquivByte (AdjoinRoot.root (leastIrreducible 8) ^ 8)).val = 0x1b := by
  have hroot : AdjoinRoot.root (leastIrreducible 8) ^ 8 =
      AdjoinRoot.mk (leastIrreducible 8) (polyOfCode 0x1b) := by
    change (AdjoinRoot.mk (leastIrreducible 8) X) ^ 8 = _
    rw [← map_pow, ← sub_eq_zero, CharTwo.sub_eq_add, ← map_add]
    have hpoly : X ^ 8 + polyOfCode 0x1b = leastIrreducible 8 := by
      rw [f256_modulus]
      norm_num [polyOfCode_eq_C_add_X_mul, polyOfCode_zero] <;> ring
    rw [hpoly, AdjoinRoot.mk_self]
  rw [hroot, val_f256EquivByte_mk_polyOfCode (by norm_num)]

end Cslib.Crypto.UOV
