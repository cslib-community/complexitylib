/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.VerificationFrontend

/-!
# Tests for Falcon v1.2 verification

These tests use the ordinary public import and exercise both sides of the squared-norm acceptance
boundary on a one-coefficient toy ring. The accepting example also applies the signing-relation
correctness theorem rather than merely evaluating the verifier. Frontend tests cover the NIST
signed-message layout, canonical and malformed compressed encodings, Algorithm 3 rejection, the
connection to algebraic verification, and compact decoder/hash fixtures derived from
`falcon512-KAT.rsp`, `count = 0`.
-/

namespace CslibFrontierTests.Crypto.Falcon

open Cslib.Crypto.Falcon

public section

abbrev toyParams : VerificationParams where
  n := 1
  q := 7
  squaredNormBound := 5
  q_pos := by decide

abbrev h : Polynomial toyParams := Cslib.Negacyclic.ofCoeffs fun _ => 1
abbrev c : Polynomial toyParams := Cslib.Negacyclic.ofCoeffs fun _ => 3
abbrev s₁ : IntegerPolynomial toyParams := fun _ => 2
abbrev s₂ : IntegerPolynomial toyParams := fun _ => 1
abbrev longS₂ : IntegerPolynomial toyParams := fun _ => 3

example : VerificationParams.falcon512.n = 512 ∧
    VerificationParams.falcon512.q = 12289 ∧
    VerificationParams.falcon512.squaredNormBound = 34034726 := by decide

example : VerificationParams.falcon1024.n = 1024 ∧
    VerificationParams.falcon1024.q = 12289 ∧
    VerificationParams.falcon1024.squaredNormBound = 70265242 := by decide

example : SigningRelation toyParams h c s₁ s₂ := by decide

example : IsCentered toyParams s₁ := by decide

example : pairSquaredNorm toyParams s₁ s₂ = 5 := by decide

/-- The relation witness `(2, 1)` reconstructs `2 + 1 = 3 mod 7` and meets the bound exactly. -/
example : verify toyParams h c s₂ = true :=
  verify_of_signingRelation toyParams (s₁ := s₁) (by decide) (by decide) (by decide)

/-- The decoded second component `3` reconstructs first component `0`, so its squared norm is
`9`, above the configured bound `5`. -/
example : verify toyParams h c longS₂ = false := by decide

/-! ### Encoded verification frontend -/

abbrev frontendParams : VerificationParams where
  n := 2
  q := 7
  squaredNormBound := 5
  q_pos := by decide

abbrev frontendH : Polynomial frontendParams := Cslib.Negacyclic.ofCoeffs fun _ => 0

private def frontendSignedMessage : ByteString :=
  [0, 4] ++ List.replicate 40 0 ++ [7, 8, 33, 1, 128, 64]

private def frontendXof (input : ByteString) : ByteString :=
  if input = List.replicate 40 0 ++ [7, 8] then [0, 2, 0, 0] else []

private def hexNibble (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

private def parseHexChars : List Char → Option ByteString
  | [] => some []
  | high :: low :: rest => do
      let highValue ← hexNibble high
      let lowValue ← hexNibble low
      let value := 16 * highValue + lowValue
      if hvalue : value < 256 then
        let tail ← parseHexChars rest
        some (⟨value, hvalue⟩ :: tail)
      else
        none
  | _ => none

private def parseHex (hex : String) : Option ByteString :=
  parseHexChars hex.toList

/-- The coefficients `(1, 0)` occupy 18 bits; the six unused bits in the final byte are zero. -/
example : decompressCoefficients 2 [1, 128, 64] = some [1, 0] := by decide

/-- Negative zero is not a canonical coefficient encoding. -/
example : decompressCoefficients 1 [128, 128] = none := by decide

/-- A nonzero unused bit and a redundant whole byte are both rejected. -/
example : decompressCoefficients 1 [0, 192] = none ∧
    decompressCoefficients 1 [0, 128, 0] = none := by decide

example : ((parseNistSignedMessage frontendParams frontendSignedMessage).map fun signed =>
    (signed.salt.length, signed.message, signed.second 0, signed.second 1)) =
      some (40, [7, 8], 1, 0) := by decide

/-- A length claiming one extra signature byte and a degree header for `n = 4` are rejected. -/
example : parseNistSignedMessage frontendParams
      ([0, 5] ++ List.replicate 40 0 ++ [7, 8, 33, 1, 128, 64]) = none ∧
    parseNistSignedMessage frontendParams
      ([0, 4] ++ List.replicate 40 0 ++ [7, 8, 34, 1, 128, 64]) = none := by decide

/-- The first 16-bit word is rejected; the following two are reduced as the first two point
coefficients. -/
example : hashToPointCoefficients 12289 2 [255, 255, 22, 224, 85, 201] =
    some [5856, 9672] := by decide

example : hashToPointCoefficients 12289 1 [255, 255] = none ∧
    hashToPointCoefficients 0 1 [0, 0] = none ∧
    hashToPointCoefficients 12289 0 [] = none := by decide

/- The first 20 compressed-signature bytes in `falcon512-KAT.rsp`, `count = 0`, encode its first
16 coefficients and end exactly at a byte boundary. The scoped depth covers hex and bit decoding. -/
set_option maxRecDepth 4096 in
example : (parseHex "0765843D1E460D17A527D2BCA405BD55BBC7DA09").bind
    (decompressCoefficients 16) =
      some [135, -406, 143, 158, 280, -34, -233, 39, -165, -357, 129, -189, 86, -350,
        -118, 4] := by decide

/- Python's standard SHAKE-256 applied to `falcon512-KAT.rsp`, `count = 0`'s `salt ++ message`
begins with this prefix; Algorithm 3 maps its first ten pairs to these ten coefficients. The scoped
depth covers the hexadecimal fixture parser. -/
set_option maxRecDepth 4096 in
example : (parseHex "16E055C90162B5FA1D15A88E88E0E19000556F02").bind
    (hashToPointCoefficients 12289 10) =
      some [5856, 9672, 354, 9719, 7445, 6283, 10462, 8588, 85, 3840] := by decide

/-- The parsed `(1, 0)` and hash point `(2, 0)` have squared norm `5` for zero public key, so the
encoded frontend reaches the algebraic verifier and accepts at the bound. -/
example : verifyNistWithXof frontendParams frontendXof frontendH frontendSignedMessage = true := by
  decide

end

end CslibFrontierTests.Crypto.Falcon
