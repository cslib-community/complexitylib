/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.Digits

/-! Checked edge clients for the FIPS 205 WOTS+ base-16 message and checksum digits. -/

public section

namespace SLHDSAWOTSDigitTests

open Cslib.BitString Cslib.Crypto.SLHDSA Cslib.Crypto.SLHDSA.WOTS

example : Base2bInput [0x0f] 4 2 := by decide
example : (base2b [0x0f] 4 2 (by decide) 0).val = 0 := by decide +kernel
example : (base2b [0x0f] 4 2 (by decide) 1).val = 15 := by decide +kernel

def zeroMessage : Message .bytes16 := fun _ => 0
def maxMessage : Message .bytes16 := fun _ => 255

-- Sixteen zero bytes produce 32 zero message digits and checksum 32 * 15 = 480 = 0x1e0.
example : ∀ i, (messageDigits zeroMessage i).val = 0 := by decide +kernel
example : checksum zeroMessage = 480 := by decide +kernel
example : (checksumDigits zeroMessage ⟨0, by simp [len2]⟩).val = 1 := by decide +kernel
example : (checksumDigits zeroMessage ⟨1, by simp [len2]⟩).val = 14 := by decide +kernel
example : (checksumDigits zeroMessage ⟨2, by simp [len2]⟩).val = 0 := by decide +kernel
example : binaryValue (byteStringBits (checksumByteString zeroMessage)) =
    (shiftedChecksum zeroMessage).val :=
  binaryValue_checksumByteString zeroMessage
example :
    Finset.univ.sum (fun i => (messageDigits zeroMessage i).val) + checksum zeroMessage =
      len1 .bytes16 * (w - 1) :=
  message_sum_add_checksum zeroMessage

-- Every 0xff byte contributes two maximal digits, so its complement checksum is zero.
example : ∀ i, (messageDigits maxMessage i).val = 15 := by decide +kernel
example : checksum maxMessage = 0 := by decide +kernel
example : ∀ i, (checksumDigits maxMessage i).val = 0 := by decide +kernel

-- The public combined view has exactly len1 + len2 positions and exposes both regions.
example :
    (digits zeroMessage
      (Fin.castAdd len2 ⟨0, by simp [len1, SecurityBytes.count]⟩)).val = 0 := by decide
example :
    (digits zeroMessage
      (Fin.natAdd (len1 .bytes16) ⟨1, by simp [len2]⟩)).val = 14 := by decide

-- All standardized byte lengths use the FIPS 205 constants from Equations (5.1)--(5.4).
example : len1 .bytes16 = 32 ∧ len .bytes16 = 35 := by decide
example : len1 .bytes24 = 48 ∧ len .bytes24 = 51 := by decide
example : len1 .bytes32 = 64 ∧ len .bytes32 = 67 := by decide

end SLHDSAWOTSDigitTests
