/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Code.DuplicatedReedMuller

/-!
# Tests: the duplicated Reed–Muller decoder used by HQC

The HQC-1 and HQC-3/HQC-5 multiplicities have the published lengths and distance bounds.  A
single nonzero error is corrected for each multiplicity.  At the strict half-distance boundary,
two distinct codewords have a common word at distance `32`, so the theorem's strict inequality
cannot be weakened.
-/

namespace CslibFrontierTests.Code.DuplicatedReedMuller

open Cslib Cslib.BitString Cslib.Code

/-- One error in the first coordinate of an HQC-1 duplicated inner block. -/
private def oneError3 : DRMWord 3 :=
  fun p => decide (p = (0, 0))

/-- One error in the first coordinate of an HQC-3/HQC-5 duplicated inner block. -/
private def oneError5 : DRMWord 5 :=
  fun p => decide (p = (0, 0))

example : Fintype.card (Fin 3 × RMPoint) = 384 := card_drmWordIndex 3

example : Fintype.card (Fin 5 × RMPoint) = 640 := card_drmWordIndex 5

example {m m' : RMMessage} (h : m ≠ m') :
    192 ≤ hammingDist (drmEncode 3 m) (drmEncode 3 m') := by
  simpa using sixtyFour_mul_le_hammingDist_drmEncode 3 h

example {m m' : RMMessage} (h : m ≠ m') :
    320 ≤ hammingDist (drmEncode 5 m) (drmEncode 5 m') := by
  simpa using sixtyFour_mul_le_hammingDist_drmEncode 5 h

private theorem weight_oneError3 : weight oneError3 = 1 := by decide

-- This fixed 640-bit exhaustive check exceeds Lean's shallow default reduction stack.
set_option maxRecDepth 10000 in
private theorem weight_oneError5 : weight oneError5 = 1 := by decide

/-- The actual decoder corrects a nonzero HQC-1 inner-block error. -/
example (m : RMMessage) : drmDecode (drmEncode 3 m + oneError3) = m :=
  drmDecode_add_eq_of_two_mul_weight_lt m oneError3 (by rw [weight_oneError3]; decide)

/-- The actual decoder corrects a nonzero HQC-3/HQC-5 inner-block error. -/
example (m : RMMessage) : drmDecode (drmEncode 5 m + oneError5) = m :=
  drmDecode_add_eq_of_two_mul_weight_lt m oneError5 (by rw [weight_oneError5]; decide)

/-- The all-zero affine message. -/
private def zeroMessage : RMMessage := ⟨false, 0⟩

/-- The message whose low source-byte bit and first affine coefficient are set. -/
private def firstSlopeMessage : RMMessage :=
  ⟨false, ![true, false, false, false, false, false, false]⟩

/-- The source byte `0x81`: the sign and first (least-significant) slope bit are set. -/
private def byte81Message : RMMessage :=
  ⟨true, ![true, false, false, false, false, false, false]⟩

/-- The source byte `0x80`: only the sign bit is set. -/
private def byte80Message : RMMessage :=
  ⟨true, 0⟩

private theorem drmFindPeak_encode {μ : ℕ} (hμ : 0 < μ) (m : RMMessage) :
    drmFindPeak (drmEncode μ m) = m.slope := by
  simpa only [drmDecode] using congrArg RMMessage.slope (drmDecode_leftInverse hμ m)

example : rmMessageByteEquiv byte81Message =
    ![true, false, false, false, false, false, false, true] := by decide

/-- Generator column zero reads only the source sign bit. -/
example : rmEncode byte81Message 0 = true := by decide

/-- Generator column one also reads the least-significant slope bit. -/
example : rmEncode byte81Message ![true, false, false, false, false, false, false] = false := by
  decide

/-- An exact codeword with clear sign has a strictly negative selected coefficient. -/
example : drmHadamardCoeff (drmEncode 3 zeroMessage) (drmFindPeak (drmEncode 3 zeroMessage)) =
    -192 := by
  rw [drmFindPeak_encode (by decide)]
  simpa [zeroMessage] using drmHadamardCoeff_encode 3 zeroMessage

/-- An exact codeword with set sign has a strictly positive selected coefficient. -/
example : drmHadamardCoeff (drmEncode 3 byte80Message)
    (drmFindPeak (drmEncode 3 byte80Message)) = 192 := by
  rw [drmFindPeak_encode (by decide)]
  simpa [byte80Message] using drmHadamardCoeff_encode 3 byte80Message

example : hammingDist (drmEncode 3 zeroMessage) (drmEncode 3 firstSlopeMessage) = 192 := by
  simpa using hammingDist_drmEncode_of_slope_ne 3 (m := zeroMessage)
    (m' := firstSlopeMessage) (by decide)

example : hammingDist (drmEncode 5 zeroMessage) (drmEncode 5 firstSlopeMessage) = 320 := by
  simpa using hammingDist_drmEncode_of_slope_ne 5 (m := zeroMessage)
    (m' := firstSlopeMessage) (by decide)

/-- A word halfway between `zeroMessage` and `firstSlopeMessage`: `x₀ ∧ x₁`. -/
private def boundaryWord : DRMWord 1 :=
  fun p => p.2 0 && p.2 1

private def boundaryErrorZero : DRMWord 1 :=
  boundaryWord

private def boundaryErrorFirst : DRMWord 1 :=
  drmEncode 1 firstSlopeMessage + boundaryWord

example : zeroMessage ≠ firstSlopeMessage := by decide

example : weight boundaryErrorZero = 32 := by decide

example : weight boundaryErrorFirst = 32 := by decide

private theorem boundaryZero_eq : drmEncode 1 zeroMessage + boundaryErrorZero = boundaryWord := by
  funext p
  simp [drmEncode, rmEncode, zeroMessage, boundaryErrorZero, boundaryWord, hadamardCode]

private theorem boundaryFirst_eq :
    drmEncode 1 firstSlopeMessage + boundaryErrorFirst = boundaryWord := by
  simp [boundaryErrorFirst]

example : hammingDist (drmEncode 1 zeroMessage) boundaryWord = 32 := by decide

example : hammingDist (drmEncode 1 firstSlopeMessage) boundaryWord = 32 := by decide

/-- At the boundary `2 * weight = 64 * μ`, the strict decoder-correctness premise is false. -/
example : ¬2 * weight boundaryErrorZero < 64 * 1 := by decide

/-- No deterministic decoder can recover both distinct messages from their common boundary word. -/
example : ¬(drmDecode (drmEncode 1 zeroMessage + boundaryErrorZero) = zeroMessage ∧
    drmDecode (drmEncode 1 firstSlopeMessage + boundaryErrorFirst) = firstSlopeMessage) := by
  rw [boundaryZero_eq, boundaryFirst_eq]
  rintro ⟨hzero, hfirst⟩
  exact (show zeroMessage ≠ firstSlopeMessage by decide) (hzero.symm.trans hfirst)

/-- The unique word at multiplicity zero. -/
private def emptyWord : DRMWord 0 :=
  fun p => Fin.elim0 p.1

private theorem emptyWord_coeff (a : RMPoint) : drmHadamardCoeff emptyWord a = 0 := by
  rw [drmHadamardCoeff, drmHadamardTransform_eq_sum]
  simp [emptyWord, drmExpandAndSum]

/-- With every coefficient tied at zero, the strict scan keeps slope zero and the nonpositive sign
rule keeps the most-significant bit clear. -/
example : drmDecode emptyWord = zeroMessage := by
  have hfind : drmFindPeak emptyWord = 0 := by
    apply drmFindPeak_eq_zero_of_max
    intro a
    rw [emptyWord_coeff, emptyWord_coeff]
  unfold drmDecode zeroMessage
  rw [hfind]
  dsimp only
  rw [emptyWord_coeff]
  rfl

end CslibFrontierTests.Code.DuplicatedReedMuller
