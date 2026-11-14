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
* `Cslib.Crypto.MLKEM.rawCoefficient`: the unreduced `d`-bit field read from encoded bytes.
* `Cslib.Crypto.MLKEM.byteEncode`, `Cslib.Crypto.MLKEM.byteDecode`: Algorithms 5 and 6.
* `Cslib.Crypto.MLKEM.IsCanonical`: the decode/re-encode check of Section 7.2.

## Main results

* `Cslib.Crypto.MLKEM.byteDecode_byteEncode`: every coefficient vector round-trips.
* `Cslib.Crypto.MLKEM.byteEncode_byteDecode`: every byte string round-trips below width 12.
* `Cslib.Crypto.MLKEM.isCanonical_width12_iff`: width-12 canonicality is exactly the absence of
  raw fields in `3329 ... 4095`.
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

/-- The unreduced natural `d`-bit field at coefficient position `i`. -/
def rawCoefficient (d : CodecWidth) (B : EncodedBytes d) (i : Fin 256) : ℕ :=
  BitString.readPackedField 8 (fun r => (B r).val) (i.val * d.val) d.val

/-- Every raw coefficient fits in its `d`-bit field. -/
theorem rawCoefficient_lt_two_pow (d : CodecWidth) (B : EncodedBytes d) (i : Fin 256) :
    rawCoefficient d B i < 2 ^ d.val :=
  BitString.readPackedField_lt 8 (fun r => (B r).val) (i.val * d.val) d.val

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
  (rawCoefficient d B i : ZMod (codecModulus d))

/-- Reading a field from encoded coefficients recovers its canonical natural representative. -/
theorem rawCoefficient_byteEncode (d : CodecWidth) (F : Coefficients d) (i : Fin 256) :
    rawCoefficient d (byteEncode d F) i = (F i).val := by
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
  change BitString.readPackedField 8 (fun r => (byteEncode d F r).val)
    (i.val * d.val) d.val = (F i).val
  rw [hfield, hindex]

/-- Decoding an encoded coefficient vector recovers every coefficient. -/
@[simp] theorem byteDecode_byteEncode (d : CodecWidth) (F : Coefficients d) :
    byteDecode d (byteEncode d F) = F := by
  funext i
  change (rawCoefficient d (byteEncode d F) i : ZMod (codecModulus d)) = F i
  rw [rawCoefficient_byteEncode, ZMod.natCast_zmod_val]

/-- Re-encoding decoded bytes is exact whenever every raw field is below the selected modulus. -/
theorem byteEncode_byteDecode_of_raw_lt (d : CodecWidth) (B : EncodedBytes d)
    (hraw : ∀ i, rawCoefficient d B i < codecModulus d) :
    byteEncode d (byteDecode d B) = B := by
  have hval (i : Fin 256) : (byteDecode d B i).val = rawCoefficient d B i := by
    rw [byteDecode, ZMod.val_natCast_of_lt (hraw i)]
  let w : Fin (32 * d.val) → ℕ := fun r => (B r).val
  have hw (r : Fin (32 * d.val)) : w r < 2 ^ 8 := by
    exact (B r).isLt
  have hrepack := BitString.packWords_readPackedField (h := 8) (B := 32 * d.val)
    (s := d.val) (by decide) d.pos w hw
  funext r
  apply Fin.ext
  change BitString.packWords
      (fun a => ((byteDecode d B) ⟨a / d.val % 256, Nat.mod_lt _ (by decide)⟩).val.testBit
        (a % d.val)) 8 (32 * d.val) r = (B r).val
  have hstreams :
      BitString.packWords
          (fun a => ((byteDecode d B)
            ⟨a / d.val % 256, Nat.mod_lt _ (by decide)⟩).val.testBit (a % d.val))
          8 (32 * d.val) =
        BitString.packWords
          (fun a => (BitString.readPackedField 8 w (a / d.val * d.val) d.val).testBit
            (a % d.val)) 8 (32 * d.val) := by
    apply BitString.packWords_congr
    intro a ha
    have hindex : a / d.val < 256 := by
      apply (Nat.div_lt_iff_lt_mul d.pos).mpr
      omega
    have hi : (⟨a / d.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) =
        ⟨a / d.val, hindex⟩ := Fin.ext (Nat.mod_eq_of_lt hindex)
    rw [hi, hval]
    rfl
  rw [hstreams]
  exact congrFun hrepack r

/-- Below width 12 the coefficient modulus is the full `d`-bit range. -/
theorem codecModulus_eq_two_pow {d : CodecWidth} (h : d.val ≤ 11) :
    codecModulus d = 2 ^ d.val := by
  rw [codecModulus, if_neg (by omega)]

/-- For every width `d ≤ 11`, encoding and decoding are inverse in the byte-to-coefficient
direction as well. -/
theorem byteEncode_byteDecode (d : CodecWidth) (h : d.val ≤ 11) (B : EncodedBytes d) :
    byteEncode d (byteDecode d B) = B := by
  apply byteEncode_byteDecode_of_raw_lt
  intro i
  rw [codecModulus_eq_two_pow h]
  exact rawCoefficient_lt_two_pow d B i

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

/-- Every exact-length byte string is canonical at widths `d ≤ 11`. -/
theorem isCanonical_of_le_eleven (d : CodecWidth) (h : d.val ≤ 11) (B : EncodedBytes d) :
    IsCanonical d B := by
  simpa only [IsCanonical] using byteEncode_byteDecode d h B

/-- At width 12, a byte string is canonical exactly when all of its raw 12-bit fields are below
the ML-KEM modulus 3329. -/
theorem isCanonical_width12_iff (B : EncodedBytes width12) :
    IsCanonical width12 B ↔ ∀ i, rawCoefficient width12 B i < 3329 := by
  constructor
  · intro hcanonical i
    change byteEncode width12 (byteDecode width12 B) = B at hcanonical
    have hfield := congrArg (fun X : EncodedBytes width12 => rawCoefficient width12 X i)
      hcanonical
    rw [rawCoefficient_byteEncode] at hfield
    rw [← hfield]
    exact ZMod.val_lt _
  · intro hraw
    change byteEncode width12 (byteDecode width12 B) = B
    apply byteEncode_byteDecode_of_raw_lt
    intro i
    simpa [codecModulus, width12] using hraw i

end Cslib.Crypto.MLKEM
