/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.Verification

/-!
# Tests for the Falcon v1.2 verification algebra

These tests use the ordinary public import and exercise both sides of the squared-norm acceptance
boundary on a one-coefficient toy ring. The accepting example also applies the signing-relation
correctness theorem rather than merely evaluating the verifier.
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

end

end CslibFrontierTests.Crypto.Falcon
