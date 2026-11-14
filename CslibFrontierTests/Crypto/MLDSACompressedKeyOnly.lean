/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly

/-!
# Tests for the ML-DSA compressed key-only reduction

This ordinary-module client uses the full ML-DSA-44 coefficient shape. Its public key has a
nonzero `Power2Round` low part, its hint vector contains both set and clear positions, and its
hash checks a hinted coefficient so changing that hint makes verification fail.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Crypto Cslib.Crypto.MLDSA

namespace MLDSACompressedKeyOnlyTests

private abbrev standard := Params.mldsa44

private instance : NeZero standard.q := ⟨by decide⟩

private def row0 : Fin standard.k := ⟨0, by decide⟩

private def coeff0 : Fin standard.n := ⟨0, by decide⟩

private def coeff1 : Fin standard.n := ⟨1, by decide⟩

private def challenge : Fin standard.n → ZMod standard.q := fun j =>
  if j.val < standard.τ then 1 else 0

private theorem challenge_inBall : InBall standard.τ challenge := by decide +kernel

private def publicKey : PublicKey standard where
  A := 0
  t := fun i j => if i = row0 ∧ j = coeff0 then 4097 else 0

private def hints : Fin standard.k → Fin standard.n → Bool := fun i j =>
  decide (i = row0 ∧ j = coeff0)

private def signature : CompressedSignature standard where
  z := 0
  h := hints
  c := challenge

private theorem responseShort : ResponseShort standard signature.z := by decide +kernel

private def checkedValue : ℤ :=
  useHint standard.q standard.γ₂ true
    (compressedVerifierCommitment standard 13 publicKey signature.z signature.c row0 coeff0)

private def hash : Hash standard := fun x =>
  if x.1 row0 coeff0 = checkedValue then challenge else 0

example : signature.h row0 coeff0 = true := rfl

example : signature.h row0 coeff1 = false := rfl

-- `4097` is one past the positive tie for `d = 13`, so its low part is `-4095`.
example : (publicKeyLowPart standard 13 publicKey row0 coeff0).valMinAbs = -4095 := by
  decide +kernel

private theorem verifies : compressedVerify standard 13 hash publicKey [] signature = true := by
  simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨responseShort, challenge_inBall⟩, ?_⟩
  simp [hash, checkedValue, signature, hints, useHintVec]

-- The instantiated equation (9)--(10) identity for the standard-shaped fixture.
example :
    selfTargetMap standard publicKey
        (compressedForgeryLowPart standard 13 publicKey signature) signature.z signature.c =
      fun i j =>
        ((useHint standard.q standard.γ₂ (signature.h i j)
          (compressedVerifierCommitment standard 13 publicKey signature.z signature.c i j) *
            (2 * standard.γ₂ : ℕ) : ℤ) : ZMod standard.q) :=
  selfTargetMap_compressedForgeryLowPart 13 publicKey signature

-- The full bounded self-target conclusion is usable at the ML-DSA-44 dimensions.
example :
    IsSelfTargetSolution standard (selfTargetHash standard hash)
        (compressedSelfTargetRadius standard 13) publicKey
      (.ofCompressedForgery standard 13 publicKey [] signature) :=
  isSelfTargetSolution_of_compressedVerify Params.valid_mldsa44 (by decide) (by decide) verifies

private def changedSignature : CompressedSignature standard :=
  { signature with
    h := fun i j => if i = row0 ∧ j = coeff0 then false else signature.h i j }

-- Changing the checked set hint to clear changes `UseHint`, so the hash check rejects.
example : compressedVerify standard 13 hash publicKey [] changedSignature = false := by
  have hinj := useHint_injective (q := standard.q) (γ₂ := standard.γ₂)
    (by decide) (by decide) (by decide)
    (compressedVerifierCommitment standard 13 publicKey signature.z signature.c row0 coeff0)
  have hne :
      useHint standard.q standard.γ₂ false
          (compressedVerifierCommitment standard 13 publicKey signature.z signature.c row0 coeff0) ≠
        checkedValue := fun heq => Bool.false_ne_true (hinj (by simpa [checkedValue] using heq))
  have hne' :
      highBits standard.q standard.γ₂
          (compressedVerifierCommitment standard 13 publicKey signature.z signature.c row0 coeff0) ≠
        checkedValue := by simpa only [useHint_false] using hne
  have hcne : (0 : Fin standard.n → ZMod standard.q) ≠ challenge := by
    intro heq
    have h := congrFun heq coeff0
    have hchallenge : challenge coeff0 = 1 := by
      simp only [challenge]
      split
      · rfl
      · rename_i hnot
        exact (hnot (by decide)).elim
    have h' : (0 : ZMod standard.q) = 1 := by
      simpa only [Pi.zero_apply, hchallenge] using h
    change (0 : ZMod 8380417) = 1 at h'
    exact (by decide : (0 : ZMod 8380417) ≠ 1) h'
  have hne'' :
      highBits standard.q standard.γ₂
          (compressedVerifierCommitment standard 13 publicKey 0 challenge row0 coeff0) ≠
        checkedValue := by simpa only [signature] using hne'
  have hshort : ResponseShort standard changedSignature.z := by
    simpa only [changedSignature] using responseShort
  have hball : InBall standard.τ changedSignature.c := by
    simpa only [changedSignature, signature] using challenge_inBall
  have hdshort : decide (ResponseShort standard changedSignature.z) = true :=
    decide_eq_true hshort
  have hdball : decide (InBall standard.τ changedSignature.c) = true := decide_eq_true hball
  rw [compressedVerify, hdshort, hdball]
  simp [hash, changedSignature, signature, hints, useHintVec, hne'', hcne]

end MLDSACompressedKeyOnlyTests
