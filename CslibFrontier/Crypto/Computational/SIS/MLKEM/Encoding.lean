/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Foundations.Data.Nat.Bitwise.Packing
public import Mathlib.Data.ZMod.Basic

/-!
# ML-KEM coefficient byte encoding

FIPS 203 Algorithms 5 and 6 serialize 256 coefficients in consecutive least-significant-bit-first
fields. A width `d` occupies exactly `32 * d` bytes. Widths below 12 use coefficients modulo
`2 ^ d`; width 12 uses the ML-KEM modulus 3329, so decoding is total but not every byte string is
canonical. Section 7.2, Equation (7.1) checks canonicality by decoding and re-encoding.

The implementation reuses `Cslib.BitString.packWords` and `readPackedField` rather than adding a
second bit-packing convention. This is only the coefficient/byte boundary: it does not identify
coefficient and NTT representations, serialize a complete key or ciphertext, or claim FIPS
validation.

## Main definitions

* `Cslib.Crypto.MLKEM.CodecWidth`: a supported FIPS 203 width from 1 through 12.
* `Cslib.Crypto.MLKEM.codecModulus`: `2 ^ d` below width 12 and 3329 at width 12.
* `Cslib.Crypto.MLKEM.byteEncode`, `Cslib.Crypto.MLKEM.byteDecode`: Algorithms 5 and 6.
* `Cslib.Crypto.MLKEM.IsCanonical`: the decode/re-encode check of Section 7.2.

## Main results

* `Cslib.Crypto.MLKEM.byteDecode_byteEncode`: every coefficient vector round-trips.
* `Cslib.Crypto.MLKEM.byteEncode_isCanonical`: every encoder output passes the canonicality check.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 4.2.1,
  Algorithms 5–6 and Section 7.2, Equation (7.1)][NISTFIPS203].
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Cslib

/-- A FIPS 203 coefficient width `d` satisfying `1 ≤ d ≤ 12`. -/
structure CodecWidth where
  /-- The number of bits in one encoded coefficient. -/
  val : ℕ
  /-- A coefficient field is nonempty. -/
  pos : 0 < val
  /-- FIPS 203 supports widths only through 12. -/
  le_twelve : val ≤ 12
  deriving DecidableEq

/-- The width 10 used for the vector part of every standardized ML-KEM ciphertext. -/
def width10 : CodecWidth := ⟨10, by decide, by decide⟩

/-- The width 11 used for the vector part of ML-KEM-1024 ciphertexts. -/
def width11 : CodecWidth := ⟨11, by decide, by decide⟩

/-- The width 12 used for NTT-domain public and secret key coefficients. -/
def width12 : CodecWidth := ⟨12, by decide, by decide⟩

/-- The coefficient modulus selected by FIPS 203 Algorithms 5 and 6. -/
def codecModulus (d : CodecWidth) : ℕ :=
  if d.val = 12 then 3329 else 2 ^ d.val

/-- The selected coefficient modulus is positive. -/
theorem codecModulus_pos (d : CodecWidth) : 0 < codecModulus d := by
  by_cases h : d.val = 12
  · rw [codecModulus, if_pos h]
    decide
  · rw [codecModulus, if_neg h]
    exact Nat.two_pow_pos d.val

instance (d : CodecWidth) : NeZero (codecModulus d) :=
  ⟨(codecModulus_pos d).ne'⟩

/-- The codec modulus fits in the `d` bits allocated to a coefficient. -/
theorem codecModulus_le_two_pow (d : CodecWidth) : codecModulus d ≤ 2 ^ d.val := by
  by_cases h : d.val = 12
  · rw [codecModulus, if_pos h, h]
    decide
  · rw [codecModulus, if_neg h]

/-- The 256 coefficients consumed and produced by the FIPS 203 byte codec. -/
abbrev Coefficients (d : CodecWidth) := Fin 256 → ZMod (codecModulus d)

/-- The exact `32 * d`-byte output and input boundary of the FIPS 203 codec. -/
abbrev EncodedBytes (d : CodecWidth) := FixedBytes (32 * d.val)

/-- FIPS 203 Algorithm 5, `ByteEncode_d`.

Coefficient zero supplies the first `d` bits, and every field and byte is read least-significant
bit first. -/
def byteEncode (d : CodecWidth) (F : Coefficients d) : EncodedBytes d := fun r =>
  ⟨BitString.packWords
      (fun a =>
        (F ⟨a / d.val % 256, Nat.mod_lt _ (by decide)⟩).val.testBit (a % d.val))
      8 (32 * d.val) r,
    by exact BitString.packWords_lt
      (fun a => (F ⟨a / d.val % 256, Nat.mod_lt _ (by decide)⟩).val.testBit (a % d.val))
      8 (32 * d.val) r⟩

/-- FIPS 203 Algorithm 6, `ByteDecode_d`.

At width 12 the natural 12-bit field is cast into `ZMod 3329`, exactly implementing the
standard's reduction of raw values `3329 ... 4095`. -/
def byteDecode (d : CodecWidth) (B : EncodedBytes d) : Coefficients d := fun i =>
  (BitString.readPackedField 8 (fun r => (B r).val) (i.val * d.val) d.val :
    ZMod (codecModulus d))

/-- Decoding an encoded coefficient vector recovers every coefficient. -/
@[simp] theorem byteDecode_byteEncode (d : CodecWidth) (F : Coefficients d) :
    byteDecode d (byteEncode d F) = F := by
  funext i
  have hcapacity : i.val * d.val + d.val ≤ (32 * d.val) * 8 := by
    have hi := i.isLt
    omega
  have hvalue :
      (F ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩).val < 2 ^ d.val :=
    lt_of_lt_of_le (ZMod.val_lt _) (codecModulus_le_two_pow d)
  have hfield := BitString.readPackedField_fields
    (fun q => (F ⟨q % 256, Nat.mod_lt _ (by decide)⟩).val)
    (h := 8) (B := 32 * d.val) (q := i.val) (s := d.val) d.pos hcapacity hvalue
  have hindex : (⟨i.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  change (BitString.readPackedField 8 (fun r => (byteEncode d F r).val)
      (i.val * d.val) d.val : ZMod (codecModulus d)) = F i
  rw [hfield, hindex, ZMod.natCast_zmod_val]

/-- A byte string is canonical when decoding and re-encoding does not change it.

For width 12 this is FIPS 203 Section 7.2, Equation (7.1). At smaller widths every exact-length
byte string is canonical because the coefficient modulus is `2 ^ d`. -/
def IsCanonical (d : CodecWidth) (B : EncodedBytes d) : Prop :=
  byteEncode d (byteDecode d B) = B

instance (d : CodecWidth) (B : EncodedBytes d) : Decidable (IsCanonical d B) :=
  inferInstance

/-- Every output of `byteEncode` is canonical. -/
theorem byteEncode_isCanonical (d : CodecWidth) (F : Coefficients d) :
    IsCanonical d (byteEncode d F) := by
  rw [IsCanonical, byteDecode_byteEncode]

end Cslib.Crypto.MLKEM
