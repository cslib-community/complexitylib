/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Floor.Div
import CslibFrontier.Foundations.Data.BitString.List.BinaryOrder
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# FIPS 205 WOTS+ message and checksum digits

This module formalizes the byte-to-base conversion of FIPS 205, Section 4.4, Algorithm 4, and
the common message/checksum preprocessing in Section 5, Algorithms 7 and 8, lines 1--7. The
standard fixes `lg_w = 4`, hence `w = 16`, `len1 = 2n`, `len2 = 3`, and `len = 2n + 3`, for all
three permitted security-byte lengths `n = 16, 24, 32`.

The checksum is the sum of the base-16 digit complements. As required by Algorithms 7 and 8, it
is shifted left by four bits, serialized as two big-endian bytes, converted with `base2b`, and the
first three base-16 digits are appended to the message digits.

This is only the digit-preprocessing layer. It does not define the Algorithm 5 hash chain,
WOTS+ key generation, signature generation, public-key reconstruction, concrete FIPS 205 hash
instantiations, or a security theorem.

## Main definitions

* `Cslib.Crypto.SLHDSA.base2b`: Algorithm 4 on byte strings.
* `Cslib.Crypto.SLHDSA.WOTS.SecurityBytes`: the three standard values of `n`.
* `Cslib.Crypto.SLHDSA.WOTS.Digit`: one base-16 WOTS+ digit.
* `Cslib.Crypto.SLHDSA.WOTS.messageDigits`: the `len1` message digits.
* `Cslib.Crypto.SLHDSA.WOTS.checksum`: the complement checksum.
* `Cslib.Crypto.SLHDSA.WOTS.digits`: the `len` message-and-checksum digits used by both
  `wots_sign` and `wots_pkFromSig`.

## Main results

* `Cslib.Crypto.SLHDSA.WOTS.checksum_lt`: the checksum fits in its three base-16 digits.
* `Cslib.Crypto.SLHDSA.WOTS.message_sum_add_checksum`: the checksum exactly complements the
  message digits to `15 * len1`.
* `Cslib.Crypto.SLHDSA.WOTS.binaryValue_checksumByteString`: the prescribed two-byte string
  represents the checksum shifted left by four bits.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Sections 4.4 and 5,
  Algorithms 4, 7, and 8][NISTFIPS205]
-/

@[expose] public section

namespace Cslib.Crypto.SLHDSA

open Cslib.BitString Cslib.Crypto

/-- The source precondition for Algorithm 4: `X` contains at least
`ceil(outLen * b / 8)` bytes. -/
def Base2bInput (X : List Byte) (b outLen : ℕ) : Prop :=
  outLen * b ⌈/⌉ 8 ≤ X.length

instance (X : List Byte) (b outLen : ℕ) : Decidable (Base2bInput X b outLen) := by
  unfold Base2bInput
  infer_instance

/-- FIPS 205 Algorithm 4 (`base_2b`), expressed by taking consecutive `b`-bit chunks from the
big-endian bit string. Its final argument enforces the source's byte-length precondition. -/
def base2b (X : List Byte) (b outLen : ℕ) (_h : Base2bInput X b outLen) :
    Fin outLen → Fin (2 ^ b) := fun i =>
  ⟨binaryValue ((bytesToBitsBE X).drop (i.val * b) |>.take b), by
    have h := binaryValue_lt_two_pow ((bytesToBitsBE X).drop (i.val * b) |>.take b)
    exact h.trans_le (Nat.pow_le_pow_right (by decide) (List.length_take_le b _))⟩

/-- Under Algorithm 4's source precondition, every requested output reads a complete `b`-bit
chunk rather than a truncated suffix. -/
theorem length_base2b_chunk (X : List Byte) (b outLen : ℕ) (h : Base2bInput X b outLen)
    (i : Fin outLen) :
    (((bytesToBitsBE X).drop (i.val * b)).take b).length = b := by
  have hcapacity : outLen * b ≤ 8 * X.length :=
    (ceilDiv_le_iff_le_mul (by decide : 0 < 8)).1 h
  have hi := Nat.mul_le_mul_right b (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at hi
  rw [List.length_take, List.length_drop, length_bytesToBitsBE, Nat.min_eq_left]
  omega

/-- Algorithm 4 reads the unsigned value of the `i`-th consecutive `b`-bit chunk. -/
@[simp] theorem base2b_val (X : List Byte) (b outLen : ℕ) (h : Base2bInput X b outLen)
    (i : Fin outLen) :
    (base2b X b outLen h i).val =
      binaryValue (((bytesToBitsBE X).drop (i.val * b)).take b) :=
  rfl

/-- Every Algorithm 4 output belongs to the advertised base-`2^b` digit range. -/
theorem base2b_lt (X : List Byte) (b outLen : ℕ) (h : Base2bInput X b outLen)
    (i : Fin outLen) : (base2b X b outLen h i).val < 2 ^ b :=
  (base2b X b outLen h i).isLt

namespace WOTS

/-- The three byte lengths `n` used by the FIPS 205 parameter sets. -/
inductive SecurityBytes where
  | bytes16
  | bytes24
  | bytes32
  deriving DecidableEq, Repr

namespace SecurityBytes

/-- The security-element and message length `n`, in bytes. -/
def count : SecurityBytes → ℕ
  | .bytes16 => 16
  | .bytes24 => 24
  | .bytes32 => 32

/-- Every standardized value of `n` is at most 32 bytes. -/
theorem count_le_32 (p : SecurityBytes) : p.count ≤ 32 := by
  cases p <;> decide

end SecurityBytes

/-- The Winternitz digit width fixed by FIPS 205. -/
abbrev lgW : ℕ := 4

/-- The Winternitz radix fixed by FIPS 205. -/
abbrev w : ℕ := 2 ^ lgW

/-- One base-`w` digit used by WOTS+. -/
abbrev Digit := Fin w

/-- The number of base-16 message digits, Equation (5.2). -/
abbrev len1 (p : SecurityBytes) : ℕ := 2 * p.count

/-- The number of base-16 checksum digits, Equation (5.3). -/
abbrev len2 : ℕ := 3

/-- The total number of WOTS+ chains, Equation (5.4). -/
abbrev len (p : SecurityBytes) : ℕ := len1 p + len2

/-- An `n`-byte message consumed by WOTS+. -/
abbrev Message (p : SecurityBytes) := Fin p.count → Byte

/-- The big-endian byte string associated with a fixed-length WOTS+ message. -/
def messageByteString {p : SecurityBytes} (M : Message p) : List Byte :=
  List.ofFn M

/-- An `n`-byte WOTS+ message has the capacity required for its `2n` base-16 digits. -/
theorem message_base2bInput {p : SecurityBytes} (M : Message p) :
    Base2bInput (messageByteString M) lgW (len1 p) := by
  unfold Base2bInput messageByteString
  rw [List.length_ofFn]
  cases p <;> decide

/-- The `len1 = 2n` base-16 message digits from line 2 of Algorithms 7 and 8. -/
def messageDigits {p : SecurityBytes} (M : Message p) : Fin (len1 p) → Digit :=
  base2b (messageByteString M) lgW (len1 p) (message_base2bInput M)

/-- The complement checksum from lines 3--5 of Algorithms 7 and 8. -/
def checksum {p : SecurityBytes} (M : Message p) : ℕ :=
  Finset.univ.sum fun i : Fin (len1 p) => w - 1 - (messageDigits M i).val

/-- The WOTS+ message checksum fits in the 12 bits represented by `len2 = 3` base-16 digits. -/
theorem checksum_lt {p : SecurityBytes} (M : Message p) : checksum M < 2 ^ (len2 * lgW) := by
  have hle : checksum M ≤ Finset.univ.sum (fun _i : Fin (len1 p) => w - 1) := by
    unfold checksum
    exact Finset.sum_le_sum fun _i _hi => Nat.sub_le _ _
  have hcount : len1 p * (w - 1) < 2 ^ (len2 * lgW) := by
    cases p <;> decide
  calc
    checksum M ≤ Finset.univ.sum (fun _i : Fin (len1 p) => w - 1) := hle
    _ = len1 p * (w - 1) := by simp
    _ < 2 ^ (len2 * lgW) := hcount

/-- The checksum exactly complements the message digits to the maximum base-16 digit sum. -/
theorem message_sum_add_checksum {p : SecurityBytes} (M : Message p) :
    Finset.univ.sum (fun i => (messageDigits M i).val) + checksum M =
      len1 p * (w - 1) := by
  rw [checksum, ← Finset.sum_add_distrib]
  calc
    Finset.univ.sum
        (fun i : Fin (len1 p) =>
          (messageDigits M i).val + (w - 1 - (messageDigits M i).val)) =
        Finset.univ.sum (fun _i : Fin (len1 p) => w - 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hi : (messageDigits M i).val < 16 := (messageDigits M i).isLt
      change (messageDigits M i).val + (15 - (messageDigits M i).val) = 15
      omega
    _ = len1 p * (w - 1) := by simp

/-- Line 6 of Algorithms 7 and 8: left-align the 12 checksum bits in two bytes. -/
def shiftedChecksum {p : SecurityBytes} (M : Message p) : Fin (2 ^ 16) :=
  ⟨checksum M * 2 ^ 4, by
    have h := checksum_lt M
    norm_num [len2, lgW] at h ⊢
    omega⟩

/-- The two-byte big-endian representation of the shifted checksum in line 7. -/
def checksumByteString {p : SecurityBytes} (M : Message p) : List Byte :=
  [⟨(shiftedChecksum M).val / 2 ^ 8, by
      have h := (shiftedChecksum M).isLt
      norm_num at h ⊢
      omega⟩,
    ⟨(shiftedChecksum M).val % 2 ^ 8, Nat.mod_lt _ (by decide)⟩]

/-- The prescribed two-byte checksum has the capacity required for three base-16 digits. -/
theorem checksum_base2bInput {p : SecurityBytes} (M : Message p) :
    Base2bInput (checksumByteString M) lgW len2 := by
  simp [Base2bInput, checksumByteString, lgW, len2]

/-- The two checksum bytes represent exactly the checksum shifted left by four bits. -/
theorem binaryValue_checksumByteString {p : SecurityBytes} (M : Message p) :
    binaryValue (bytesToBitsBE (checksumByteString M)) = (shiftedChecksum M).val := by
  rw [show bytesToBitsBE (checksumByteString M) =
      binaryWord 8 ((shiftedChecksum M).val / 2 ^ 8) ++
        binaryWord 8 ((shiftedChecksum M).val % 2 ^ 8) by
    simp [bytesToBitsBE, byteBitsBE, checksumByteString]]
  rw [binaryValue_append, binaryValue_binaryWord, binaryValue_binaryWord,
    length_binaryWord (Nat.mod_lt _ (by decide))]
  simpa [Nat.mul_comm] using Nat.div_add_mod (shiftedChecksum M).val 256

/-- The three base-16 checksum digits appended by line 7 of Algorithms 7 and 8. -/
def checksumDigits {p : SecurityBytes} (M : Message p) : Fin len2 → Digit :=
  base2b (checksumByteString M) lgW len2 (checksum_base2bInput M)

/-- The `len = len1 + len2` digits used by both `wots_sign` and `wots_pkFromSig`. -/
def digits {p : SecurityBytes} (M : Message p) : Fin (len p) → Digit :=
  Fin.append (messageDigits M) (checksumDigits M)

/-- The message prefix of `digits` is exactly `messageDigits`. -/
@[simp] theorem digits_castAdd {p : SecurityBytes} (M : Message p) (i : Fin (len1 p)) :
    digits M (Fin.castAdd len2 i) = messageDigits M i :=
  Fin.append_left _ _ _

/-- The checksum suffix of `digits` is exactly `checksumDigits`. -/
@[simp] theorem digits_natAdd {p : SecurityBytes} (M : Message p) (i : Fin len2) :
    digits M (Fin.natAdd (len1 p) i) = checksumDigits M i :=
  Fin.append_right _ _ _

end WOTS

end Cslib.Crypto.SLHDSA
