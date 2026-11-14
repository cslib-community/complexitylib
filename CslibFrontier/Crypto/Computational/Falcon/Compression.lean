/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Falcon.Verification
public import CslibFrontier.Foundations.Data.BitString.List.Binary

/-!
# Falcon v1.2 compression rejection

This module formalizes the deterministic rejection boundary around Falcon v1.2 signature
compression. Algorithm 17 of [Falcon2020], Section 3.11.2 encodes each integer coefficient with
one sign bit, seven low magnitude bits in most-significant-first order, and a unary high part.
Consequently a coefficient `x` contributes exactly `9 + ⌊|x| / 128⌋` bits. The reference
`codec.c::comp_encode` additionally rejects coefficients outside `[-2047, 2047]` and fails when
the resulting byte string exceeds its output capacity.

`SigningCandidateAccepted` combines this exact reference-encoder boundary with Algorithm 10's
independent squared-norm rejection. It describes when a candidate may proceed; it does not
construct the encoded bytes or model the sampler, retry loop, termination probability, running
time, security reduction, or the still-developing FN-DSA / FIPS 206 standard.

## Main definitions

* `Cslib.Crypto.Falcon.coefficientCompressionBits`: Algorithm 17's bit word for one coefficient.
* `Cslib.Crypto.Falcon.compressedBits`, `Cslib.Crypto.Falcon.compressedBitLength`,
  `Cslib.Crypto.Falcon.compressedByteLength`: the concatenated word and its exact sizes.
* `Cslib.Crypto.Falcon.ReferenceCompressible`: the reference encoder's coefficient-range and
  output-capacity boundary.
* `Cslib.Crypto.Falcon.SigningCandidateAccepted`,
  `Cslib.Crypto.Falcon.signingCandidateAccepts`: Algorithm 10's norm and compression rejection
  boundary, as a proposition and executable Boolean.

## Main results

* `Cslib.Crypto.Falcon.length_coefficientCompressionBits`: the exact per-coefficient bit length.
* `Cslib.Crypto.Falcon.length_compressedBits`: the exact whole-polynomial bit length.
* `Cslib.Crypto.Falcon.referenceCompressible_iff_bitCapacity`: byte capacity is equivalently an
  exact bit-capacity inequality.
* `Cslib.Crypto.Falcon.signingCandidateAccepts_eq_true_iff`: executable candidate acceptance is
  exactly the conjunction of norm and compression acceptance.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Algorithm 10, Algorithm 17 and Table 3.3.
-/

public section

namespace Cslib.Crypto.Falcon

open Cslib.BitString

/-- Falcon v1.2 Algorithm 17's compressed bit word for one integer coefficient.

The first bit is the sign, the next seven are the low seven magnitude bits in
most-significant-first order, and the suffix is `⌊|x| / 128⌋` zeroes followed by a one. -/
@[expose] def coefficientCompressionBits (x : ℤ) : List Bool :=
  [decide (x < 0)] ++ binaryWord 7 (x.natAbs % 128) ++
    List.replicate (x.natAbs / 128) false ++ [true]

/-- A coefficient contributes one sign bit, seven low bits, its unary high part, and the unary
terminator. -/
@[simp] theorem length_coefficientCompressionBits (x : ℤ) :
    (coefficientCompressionBits x).length = 9 + x.natAbs / 128 := by
  have hlow : x.natAbs % 128 < 2 ^ 7 := by
    simpa using Nat.mod_lt x.natAbs (by decide : 0 < 128)
  simp [coefficientCompressionBits, length_binaryWord hlow]

/-- Concatenate Algorithm 17's coefficient words in increasing coefficient order. Padding is not
included; it is applied only after the size check. -/
@[expose] def compressedBits (P : VerificationParams) (s : IntegerPolynomial P) : List Bool :=
  (List.ofFn s).flatMap coefficientCompressionBits

/-- The exact unpadded compressed length of an integer polynomial, in bits. -/
@[expose] def compressedBitLength (P : VerificationParams) (s : IntegerPolynomial P) : ℕ :=
  ∑ i, 9 + (s i).natAbs / 128

/-- Algorithm 17's concatenated bit word has the coefficient-wise length sum. -/
@[simp] theorem length_compressedBits (P : VerificationParams) (s : IntegerPolynomial P) :
    (compressedBits P s).length = compressedBitLength P s := by
  simp [compressedBits, compressedBitLength, List.length_flatMap, List.sum_ofFn]

/-- The number of bytes emitted by the reference encoder before any fixed-width signature
padding. The final partial byte, if present, is padded with low zero bits. -/
@[expose] def compressedByteLength (P : VerificationParams) (s : IntegerPolynomial P) : ℕ :=
  (compressedBitLength P s + 7) / 8

/-- The coefficient-range check performed by the reference `codec.c::comp_encode` before it
emits any bytes. This `2047` restriction is a reference-implementation condition, not a condition
stated by Algorithm 17's mathematical pseudocode. -/
@[expose] def ReferenceCoefficientRange (P : VerificationParams)
    (s : IntegerPolynomial P) : Prop :=
  ∀ i, (s i).natAbs ≤ 2047

instance (P : VerificationParams) (s : IntegerPolynomial P) :
    Decidable (ReferenceCoefficientRange P s) := by
  unfold ReferenceCoefficientRange
  infer_instance

/-- The exact success boundary of the reference variable-length coefficient encoder with an
output capacity of `capacityBytes`: every coefficient is in `[-2047, 2047]`, and the complete
encoding fits in the buffer. -/
@[expose] def ReferenceCompressible (capacityBytes : ℕ) (P : VerificationParams)
    (s : IntegerPolynomial P) : Prop :=
  ReferenceCoefficientRange P s ∧ compressedByteLength P s ≤ capacityBytes

instance (capacityBytes : ℕ) (P : VerificationParams) (s : IntegerPolynomial P) :
    Decidable (ReferenceCompressible capacityBytes P s) := by
  unfold ReferenceCompressible
  infer_instance

/-- Rounding the unpadded bit length up to bytes fits exactly when the bits fit in the
corresponding multiple-of-eight capacity. -/
theorem compressedByteLength_le_iff (capacityBytes : ℕ) (P : VerificationParams)
    (s : IntegerPolynomial P) :
    compressedByteLength P s ≤ capacityBytes ↔
      compressedBitLength P s ≤ 8 * capacityBytes := by
  unfold compressedByteLength
  omega

/-- Reference compression succeeds exactly when the coefficients satisfy the implementation
range and the unpadded bit word fits the byte capacity. -/
theorem referenceCompressible_iff_bitCapacity (capacityBytes : ℕ)
    (P : VerificationParams) (s : IntegerPolynomial P) :
    ReferenceCompressible capacityBytes P s ↔
      ReferenceCoefficientRange P s ∧ compressedBitLength P s ≤ 8 * capacityBytes := by
  rw [ReferenceCompressible, compressedByteLength_le_iff]

/-- Falcon-512's compressed payload capacity from [Falcon2020], Table 3.3: the 666-byte padded
signature minus its one-byte header and 40-byte salt. -/
@[expose] def falcon512CompressedPayloadBytes : ℕ := 625

/-- Falcon-1024's compressed payload capacity from [Falcon2020], Table 3.3: the 1280-byte padded
signature minus its one-byte header and 40-byte salt. -/
@[expose] def falcon1024CompressedPayloadBytes : ℕ := 1239

/-- Algorithm 10's deterministic acceptance boundary for one sampled integer pair: its squared
norm is within `⌊β²⌋`, and its transmitted second component passes the reference coefficient
range and compressed-output capacity checks. -/
@[expose] def SigningCandidateAccepted (capacityBytes : ℕ) (P : VerificationParams)
    (s₁ s₂ : IntegerPolynomial P) : Prop :=
  pairSquaredNorm P s₁ s₂ ≤ P.squaredNormBound ∧
    ReferenceCompressible capacityBytes P s₂

instance (capacityBytes : ℕ) (P : VerificationParams) (s₁ s₂ : IntegerPolynomial P) :
    Decidable (SigningCandidateAccepted capacityBytes P s₁ s₂) := by
  unfold SigningCandidateAccepted
  infer_instance

/-- Executable form of Algorithm 10's norm-and-compression candidate acceptance boundary. -/
@[expose] def signingCandidateAccepts (capacityBytes : ℕ) (P : VerificationParams)
    (s₁ s₂ : IntegerPolynomial P) : Bool :=
  decide (SigningCandidateAccepted capacityBytes P s₁ s₂)

/-- The executable acceptance test is true exactly at the stated norm-and-compression boundary. -/
theorem signingCandidateAccepts_eq_true_iff (capacityBytes : ℕ) (P : VerificationParams)
    (s₁ s₂ : IntegerPolynomial P) :
    signingCandidateAccepts capacityBytes P s₁ s₂ = true ↔
      SigningCandidateAccepted capacityBytes P s₁ s₂ := by
  simp [signingCandidateAccepts]

end Cslib.Crypto.Falcon
