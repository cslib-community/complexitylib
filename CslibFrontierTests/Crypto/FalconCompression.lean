/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.Compression

/-!
# Tests for Falcon v1.2 compression rejection

These ordinary-import clients exercise Algorithm 17's sign/low-seven/unary convention, the
reference encoder's coefficient and byte-capacity failures, and both independent halves of the
Algorithm 10 candidate-rejection boundary.
-/

namespace CslibFrontierTests.Crypto.FalconCompression

open Cslib.Crypto.Falcon

public section

/-- Zero has a positive sign bit, seven zero low bits, and an immediate unary terminator. -/
example : coefficientCompressionBits 0 =
    [false, false, false, false, false, false, false, false, true] := by decide

/-- The low seven bits are most-significant first, while negativity changes only the sign bit. -/
example : coefficientCompressionBits 5 =
      [false, false, false, false, false, true, false, true, true] ∧
    coefficientCompressionBits (-5) =
      [true, false, false, false, false, true, false, true, true] := by decide

/-- Crossing from magnitude 127 to 128 adds the first unary zero without changing the eight-bit
sign/low part. -/
example : (coefficientCompressionBits 127).length = 9 ∧
    (coefficientCompressionBits 128).length = 10 ∧
    (coefficientCompressionBits (-128)).length = 10 := by decide

private abbrev oneParams : VerificationParams where
  n := 1
  q := 12289
  squaredNormBound := 10
  q_pos := by decide

private def coefficient (x : ℤ) : IntegerPolynomial oneParams := fun _ => x

/-- Magnitudes `2047` use exactly 24 bits and fit three bytes at either sign. A magnitude of
`2048` is rejected by the reference range check even with ample output capacity. -/
example : ReferenceCompressible 3 oneParams (coefficient 2047) ∧
    ReferenceCompressible 3 oneParams (coefficient (-2047)) ∧
    ¬ReferenceCompressible 4 oneParams (coefficient 2048) ∧
    ¬ReferenceCompressible 4 oneParams (coefficient (-2048)) := by decide

/-- One zero coefficient needs nine bits, hence exactly two bytes: the exact capacity succeeds
and a one-byte output buffer fails. -/
example : ReferenceCompressible 2 oneParams (coefficient 0) ∧
    ¬ReferenceCompressible 1 oneParams (coefficient 0) := by decide

private def zero : IntegerPolynomial oneParams := coefficient 0
private def four : IntegerPolynomial oneParams := coefficient 4

/-- Norm acceptance does not hide compression failure: `(0, 0)` is short but cannot fit in a
one-byte compressed payload. -/
example : pairSquaredNorm oneParams zero zero ≤ oneParams.squaredNormBound ∧
    ¬ReferenceCompressible 1 oneParams zero ∧
    signingCandidateAccepts 1 oneParams zero zero = false := by decide

/-- Compression acceptance does not hide norm failure: `(4, 0)` has a compressible second
component but exceeds the toy squared-norm bound. -/
example : ReferenceCompressible 2 oneParams zero ∧
    ¬pairSquaredNorm oneParams four zero ≤ oneParams.squaredNormBound ∧
    signingCandidateAccepts 2 oneParams four zero = false := by decide

/-- A short pair with a fitting second component passes both deterministic rejection tests. -/
example : signingCandidateAccepts 2 oneParams (coefficient 1) zero = true := by decide

/-- Table 3.3 leaves 625 and 1239 bytes after the one-byte header and 40-byte salt. The all-zero
polynomials require respectively 4608 and 9216 bits and therefore fit those capacities. The
scoped recursion depth covers evaluation of all 1024 coefficient checks. -/
set_option maxRecDepth 8192 in
example : falcon512CompressedPayloadBytes = 625 ∧
    falcon1024CompressedPayloadBytes = 1239 ∧
    ReferenceCompressible falcon512CompressedPayloadBytes VerificationParams.falcon512
      (fun _ => 0) ∧
    ReferenceCompressible falcon1024CompressedPayloadBytes VerificationParams.falcon1024
      (fun _ => 0) := by decide

end

end CslibFrontierTests.Crypto.FalconCompression
