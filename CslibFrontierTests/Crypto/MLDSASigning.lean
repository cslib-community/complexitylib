/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.MLDSA.Signing
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for bounded ML-DSA signing

The one-coefficient fixture separates Algorithm 7's second-stage rejection checks from the
earlier response and low-bits checks. It also exercises counter-stepped first-success semantics.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Crypto Cslib.Crypto.MLDSA

namespace MLDSASigningTests

/-- Small executable parameters for the rejection predicates. The attempt tests do not claim
that this is a secure or standardized parameter set. -/
private abbrev toy : Params where
  n := 1
  q := 17
  k := 1
  ℓ := 1
  η := 1
  γ₁ := 8
  γ₂ := 2
  τ := 1
  β := 0

private def hash : Hash toy := fun _ => ![1]

/-- With `s₂ = 3`, `d = 2` gives `t₀ = -1`. The accepting mask makes the hint set. -/
private def hintSk : SecretKey toy :=
  ⟨Matrix.of fun _ _ => ![1], fun _ => ![0], fun _ => ![3]⟩

/-- With `s₂ = 2`, `d = 2` gives `t₀ = 2`, exactly the rejected `γ₂` boundary. -/
private def normSk : SecretKey toy :=
  ⟨Matrix.of fun _ _ => ![1], fun _ => ![0], fun _ => ![2]⟩

private def acceptingMask : Fin toy.ℓ → Fin toy.n → ZMod toy.q := fun _ => ![6]

private def normBoundaryMask : Fin toy.ℓ → Fin toy.n → ZMod toy.q := fun _ => ![7]

/-- This mask is rejected by the first-stage response check for `hintSk`. -/
private def firstStageRejectMask : Fin toy.ℓ → Fin toy.n → ZMod toy.q := fun _ => ![8]

example : hintWeight toy (fun _ => ![true]) = 1 := by decide +kernel

-- All checks pass when the single set hint is permitted.
example : (compressedSignAttempt toy 2 1 hash hintSk [] acceptingMask).isSome = true := by
  decide +kernel

-- The same candidate is rejected only because its hint weight exceeds `ω = 0`.
example : (compressedSignAttempt toy 2 0 hash hintSk [] acceptingMask).isNone = true := by
  decide +kernel

-- The line-28 product norm uses a strict bound and rejects `|c t₀| = γ₂`.
example : (compressedSignAttempt toy 2 1 hash normSk [] normBoundaryMask).isNone = true := by
  decide +kernel

private def acceptImmediately (_ : ℕ) : Fin toy.ℓ → Fin toy.n → ZMod toy.q :=
  acceptingMask

private def acceptSecond (κ : ℕ) : Fin toy.ℓ → Fin toy.n → ZMod toy.q :=
  if κ = 0 then firstStageRejectMask else acceptingMask

private def alwaysReject (_ : ℕ) : Fin toy.ℓ → Fin toy.n → ZMod toy.q :=
  firstStageRejectMask

-- No attempt means the single uniform failure result.
example : (compressedSignBounded toy 2 1 hash hintSk [] acceptImmediately 0).isNone = true := by
  decide +kernel

-- The first scheduled attempt succeeds.
example : (compressedSignBounded toy 2 1 hash hintSk [] acceptImmediately 1).isSome = true := by
  decide +kernel

-- Counter zero rejects, then line 31 advances by `ℓ = 1` and counter one succeeds.
example : (compressedSignBounded toy 2 1 hash hintSk [] acceptSecond 2).isSome = true := by
  decide +kernel

-- Exhausting two rejecting attempts returns the same failure value.
example : (compressedSignBounded toy 2 1 hash hintSk [] alwaysReject 2).isNone = true := by
  decide +kernel

example : signingAttemptCounter toy 5 (2 : Fin 3) = 7 := by decide

-- The published counter budget fits the two-byte `κ` encoding for every standardized module rank.
example : fips204PublishedSigningLoopLimit = 814 := rfl
example :
    fips204PublishedSigningLoopLimit * Params.mldsa44.ℓ < 2 ^ 16 ∧
      fips204PublishedSigningLoopLimit * Params.mldsa65.ℓ < 2 ^ 16 ∧
      fips204PublishedSigningLoopLimit * Params.mldsa87.ℓ < 2 ^ 16 := by
  decide

-- The exact IID failure law is usable without identifying IID masks with `ExpandMask`.
example (mask : PMF (Fin toy.ℓ → Fin toy.n → ZMod toy.q)) (K : ℕ) :
    compressedSignIID toy 2 1 hash hintSk [] mask K none =
      (compressedSignAttemptLaw toy 2 1 hash hintSk [] mask none) ^ K :=
  compressedSignIID_apply_none toy 2 1 hash hintSk [] mask K

end MLDSASigningTests
