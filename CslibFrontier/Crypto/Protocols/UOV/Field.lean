/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial

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

public section

namespace Cslib.Crypto.UOV

open BitString Polynomial

/-- UOV's `F16`, using the library's explicit degree-four binary field. -/
abbrev F16 := BinaryField 4

/-- UOV's `F256`, using the library's explicit degree-eight binary field. -/
abbrev F256 := BinaryField 8

private theorem polyOfCode_nineteen : polyOfCode 19 = X ^ 4 + X + 1 := by
  have h19 : polyOfCode 19 = 1 + X * polyOfCode 9 := by
    convert polyOfCode_two_mul_add_one 9 using 1 <;> norm_num
  have h9 : polyOfCode 9 = 1 + X * polyOfCode 4 := by
    convert polyOfCode_two_mul_add_one 4 using 1 <;> norm_num
  have h4 : polyOfCode 4 = X * polyOfCode 2 := by
    convert polyOfCode_two_mul 2 using 1 <;> norm_num
  rw [h19, h9, h4, polyOfCode_two]
  ring

private theorem polyOfCode_two_hundred_eighty_three :
    polyOfCode 283 = X ^ 8 + X ^ 4 + X ^ 3 + X + 1 := by
  have h283 : polyOfCode 283 = 1 + X * polyOfCode 141 := by
    convert polyOfCode_two_mul_add_one 141 using 1 <;> norm_num
  have h141 : polyOfCode 141 = 1 + X * polyOfCode 70 := by
    convert polyOfCode_two_mul_add_one 70 using 1 <;> norm_num
  have h70 : polyOfCode 70 = X * polyOfCode 35 := by
    convert polyOfCode_two_mul 35 using 1 <;> norm_num
  have h35 : polyOfCode 35 = 1 + X * polyOfCode 17 := by
    convert polyOfCode_two_mul_add_one 17 using 1 <;> norm_num
  have h17 : polyOfCode 17 = 1 + X * polyOfCode 8 := by
    convert polyOfCode_two_mul_add_one 8 using 1 <;> norm_num
  have h8 : polyOfCode 8 = X * polyOfCode 4 := by
    convert polyOfCode_two_mul 4 using 1 <;> norm_num
  have h4 : polyOfCode 4 = X * polyOfCode 2 := by
    convert polyOfCode_two_mul 2 using 1 <;> norm_num
  rw [h283, h141, h70, h35, h17, h8, h4, polyOfCode_two]
  ring

private theorem polyOfCode_twenty_seven : polyOfCode 0x1b = X ^ 4 + X ^ 3 + X + 1 := by
  have h27 : polyOfCode 0x1b = 1 + X * polyOfCode 13 := by
    convert polyOfCode_two_mul_add_one 13 using 1 <;> norm_num
  have h13 : polyOfCode 13 = 1 + X * polyOfCode 6 := by
    convert polyOfCode_two_mul_add_one 6 using 1 <;> norm_num
  have h6 : polyOfCode 6 = X * polyOfCode 3 := by
    convert polyOfCode_two_mul 3 using 1 <;> norm_num
  rw [h27, h13, h6, polyOfCode_three]
  ring

/-- The least-code degree-four irreducible binary polynomial has code `19 = 0b10011`. -/
theorem f16_modulus_code : leastIrreducible 4 = polyOfCode 19 := by
  rw [← polyOfCode_leastIrreducibleCode (B := 32) (by norm_num) (by norm_num),
    show leastIrreducibleCode 32 4 = 19 by decide]

/-- `BinaryField 4` uses UOV's modulus `X ^ 4 + X + 1`. -/
theorem f16_modulus : leastIrreducible 4 = X ^ 4 + X + 1 := by
  rw [f16_modulus_code, polyOfCode_nineteen]

private theorem leastIrreducibleCode_eight : leastIrreducibleCode 512 8 = 283 := by
  have hlow :
      (List.range 256).find? (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by
    rw [List.find?_eq_none]
    intro m hm hpred
    have hm_lt : m < 256 := List.mem_range.mp hm
    have hlog : Nat.log 2 m ≠ 8 := by
      rcases eq_or_ne m 0 with rfl | hm0
      · norm_num
      · exact ne_of_lt (Nat.log_lt_of_lt_pow hm0 (by simpa using hm_lt))
    exact hlog (beq_iff_eq.mp (Bool.and_eq_true.mp hpred).1)
  have hwindow :
      ((List.range 28).map (256 + ·)).find?
          (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = some 283 := by
    decide
  have hhigh :
      ((List.range 256).map (256 + ·)).find?
          (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = some 283 := by
    rw [show List.range 256 =
        List.range 28 ++ (List.range 228).map (28 + ·) by
          simpa using (List.range_add (n := 28) (m := 228)),
      List.map_append, List.find?_append, hwindow, Option.some_or]
  unfold leastIrreducibleCode
  rw [show List.range 512 =
      List.range 256 ++ (List.range 256).map (256 + ·) by
        simpa using (List.range_add (n := 256) (m := 256)),
    List.find?_append, hlow, Option.none_or, hhigh, Option.getD_some]

/-- The least-code degree-eight irreducible binary polynomial has code
`283 = 0b100011011`. -/
theorem f256_modulus_code : leastIrreducible 8 = polyOfCode 283 := by
  rw [← polyOfCode_leastIrreducibleCode (B := 512) (by norm_num) (by norm_num),
    leastIrreducibleCode_eight]

/-- `BinaryField 8` uses UOV's modulus `X ^ 8 + X ^ 4 + X ^ 3 + X + 1`. -/
theorem f256_modulus : leastIrreducible 8 = X ^ 8 + X ^ 4 + X ^ 3 + X + 1 := by
  rw [f256_modulus_code, polyOfCode_two_hundred_eighty_three]

/-- UOV's polynomial-basis encoding of an `F16` element as one nibble.  Coordinate zero is the
constant coefficient. -/
noncomputable def f16EquivNibble : F16 ≃ Fin 16 :=
  BinaryField.equivFin (w := 4) (by norm_num)

/-- UOV's polynomial-basis encoding of an `F256` element as one byte.  Coordinate zero is the
constant coefficient. -/
noncomputable def f256EquivByte : F256 ≃ Fin 256 :=
  BinaryField.equivFin (w := 8) (by norm_num)

/-- A bounded polynomial code is unchanged by UOV's `F16` nibble encoding. -/
theorem val_f16EquivNibble_mk_polyOfCode {c : ℕ} (hc : c < 16) :
    (f16EquivNibble (AdjoinRoot.mk (leastIrreducible 4) (polyOfCode c))).val = c := by
  have hc' : c < 2 ^ 4 := by simpa using hc
  simpa only [f16EquivNibble] using
    BinaryField.val_equivFin_mk_polyOfCode (w := 4) (c := c) (by norm_num) hc'

/-- Decoding a nibble gives the class of the binary polynomial with that code. -/
theorem f16EquivNibble_symm_apply (c : Fin 16) :
    f16EquivNibble.symm c = AdjoinRoot.mk (leastIrreducible 4) (polyOfCode c.val) := by
  simpa only [f16EquivNibble] using
    BinaryField.equivFin_symm_eq_mk_polyOfCode (w := 4) (by norm_num) c

/-- A bounded polynomial code is unchanged by UOV's `F256` byte encoding. -/
theorem val_f256EquivByte_mk_polyOfCode {c : ℕ} (hc : c < 256) :
    (f256EquivByte (AdjoinRoot.mk (leastIrreducible 8) (polyOfCode c))).val = c := by
  have hc' : c < 2 ^ 8 := by simpa using hc
  simpa only [f256EquivByte] using
    BinaryField.val_equivFin_mk_polyOfCode (w := 8) (c := c) (by norm_num) hc'

/-- Decoding a byte gives the class of the binary polynomial with that code. -/
theorem f256EquivByte_symm_apply (c : Fin 256) :
    f256EquivByte.symm c = AdjoinRoot.mk (leastIrreducible 8) (polyOfCode c.val) := by
  simpa only [f256EquivByte] using
    BinaryField.equivFin_symm_eq_mk_polyOfCode (w := 8) (by norm_num) c

/-- Pack two `F16` elements into one byte.  The first element is the low nibble and the second is
the high nibble, as in UOV v3.0, Section 3.3. -/
@[expose] noncomputable def f16PairEquivByte : F16 × F16 ≃ Fin 256 :=
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
  simpa only [polyOfCode_two, AdjoinRoot.mk_X] using h

/-- The multiplicative identity has nibble value `1`. -/
theorem val_f16EquivNibble_one : (f16EquivNibble (1 : F16)).val = 1 := by
  have hmk : AdjoinRoot.mk (leastIrreducible 4) (polyOfCode 1) = (1 : F16) := by
    rw [polyOfCode_one]
    exact map_one _
  rw [← hmk]
  exact val_f16EquivNibble_mk_polyOfCode (c := 1) (by norm_num)

/-- In UOV's `F16`, the quotient relation is `X ^ 4 = X + 1`, encoded as `0x3`. -/
theorem val_f16EquivNibble_root_pow_four :
    (f16EquivNibble (AdjoinRoot.root (leastIrreducible 4) ^ 4)).val = 3 := by
  have hroot : AdjoinRoot.root (leastIrreducible 4) ^ 4 =
      AdjoinRoot.mk (leastIrreducible 4) (polyOfCode 3) := by
    change (AdjoinRoot.mk (leastIrreducible 4) X) ^ 4 = _
    rw [← map_pow, ← sub_eq_zero, CharTwo.sub_eq_add, ← map_add]
    have hpoly : X ^ 4 + polyOfCode 3 = leastIrreducible 4 := by
      rw [f16_modulus, polyOfCode_three]
      ring
    rw [hpoly, AdjoinRoot.mk_self]
  rw [hroot, val_f16EquivNibble_mk_polyOfCode (by norm_num)]

/-- The polynomial-basis generator `X` has byte value `2`, not the bit-reversed value `64`. -/
theorem val_f256EquivByte_root :
    (f256EquivByte (AdjoinRoot.root (leastIrreducible 8))).val = 2 := by
  have h := val_f256EquivByte_mk_polyOfCode (c := 2) (by norm_num)
  simpa only [polyOfCode_two, AdjoinRoot.mk_X] using h

/-- In UOV's `F256`, the quotient relation is
`X ^ 8 = X ^ 4 + X ^ 3 + X + 1`, encoded as `0x1b`. -/
theorem val_f256EquivByte_root_pow_eight :
    (f256EquivByte (AdjoinRoot.root (leastIrreducible 8) ^ 8)).val = 0x1b := by
  have hroot : AdjoinRoot.root (leastIrreducible 8) ^ 8 =
      AdjoinRoot.mk (leastIrreducible 8) (polyOfCode 0x1b) := by
    change (AdjoinRoot.mk (leastIrreducible 8) X) ^ 8 = _
    rw [← map_pow, ← sub_eq_zero, CharTwo.sub_eq_add, ← map_add]
    have hpoly : X ^ 8 + polyOfCode 0x1b = leastIrreducible 8 := by
      rw [f256_modulus, polyOfCode_twenty_seven]
      ring
    rw [hpoly, AdjoinRoot.mk_self]
  rw [hroot, val_f256EquivByte_mk_polyOfCode (by norm_num)]

end Cslib.Crypto.UOV
