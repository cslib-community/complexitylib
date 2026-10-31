/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Commitment.Basic

/-!
# Efficient public operations for commitment schemes

`CommitmentScheme.PublicOperations` supplies a deterministic commitment-and-opening evaluator
and polynomial-time certificates for evaluation and verification. Both machines receive the key
through exactly the public encoding `CommitmentScheme.encodeKey`; supplied randomness and all
message, commitment and opening words are charged as part of the input.

An ideal `PMF` law for the supplied randomness recovers the scheme's existing commitment law.
This is separate from an executable sampler: the record does not certify key generation,
randomness sampling, or a strict-PPT implementation of the commitment distribution. In particular,
an exact uniform law on a finite group need not have a strict-PPT fair-coin sampler.

This is additional evidence for an existing `CommitmentScheme`, rather than a new security model.
Its evaluation and verification certificates use the same plain native-machine predicate as
`BitCommitmentScheme`.

## Main definitions

* `Cslib.Crypto.CommitmentScheme.PublicOperations`: public deterministic operations, their
  polynomial-time certificates, and their exact relationship to the ideal commitment law.

## Main results

* `Cslib.Crypto.CommitmentScheme.PublicOperations.computableInPolyTime_commit`,
  `Cslib.Crypto.CommitmentScheme.PublicOperations.computableInPolyTime_verify`: composition with
  efficiently produced public keys and words.
-/

public section

namespace Cslib.Crypto.CommitmentScheme

open Turing.MultiTapeTM

/-- Efficient deterministic public operations for `S`, with an ideal supplied-randomness law.
The input encoding for both certificates is `S.encodeKey`, so the machine receives precisely the
public key word rather than additional semantic key data. The `randomness` field is an ideal law,
not an algorithm or an efficiency certificate for sampling. -/
structure PublicOperations {Key : Type} (S : CommitmentScheme Key) where
  /-- Compute a commitment and opening from a public key, message and supplied randomness word. -/
  commit : Key → List Bool → List Bool → List Bool × List Bool
  /-- Ideal law of the supplied randomness, independent of the message. No sampler is bundled. -/
  randomness : Key → PMF (List Bool)
  /-- Evaluation on the ideal randomness law gives exactly the existing commitment distribution. -/
  map_commit : ∀ k m, (randomness k).map (commit k m) = S.commitDist k m
  /-- Deterministic evaluation is polynomial-time in the public key, message and randomness word. -/
  commit_polyTime : ComputableInPolyTime
    (fun p : Key × List Bool × List Bool => commit p.1 p.2.1 p.2.2)
    (encPair S.encodeKey (encPair encBits encBits)) (encPair encBits encBits)
  /-- Verification is polynomial-time in the public key, message, commitment and opening words. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : Key × List Bool × List Bool × List Bool => S.verify p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair S.encodeKey (encPair encBits (encPair encBits encBits))) encBool

namespace PublicOperations

variable {Key α : Type} {S : CommitmentScheme Key} {input : α ↪ List Bool}

/-- Compose a public commitment evaluator with efficient producers of its full encoded input. -/
@[fun_prop]
theorem computableInPolyTime_commit (ops : S.PublicOperations)
    {key : α → Key} {message coins : α → List Bool}
    (hkey : ComputableInPolyTime key input S.encodeKey)
    (hmessage : ComputableInPolyTime message input encBits)
    (hcoins : ComputableInPolyTime coins input encBits) :
    ComputableInPolyTime (fun a => ops.commit (key a) (message a) (coins a))
      input (encPair encBits encBits) :=
  ops.commit_polyTime.comp (hkey.prod (hmessage.prod hcoins))

/-- Compose the scheme's verifier with efficient producers of its full encoded input. -/
theorem computableInPolyTime_verify (ops : S.PublicOperations)
    {key : α → Key} {message commitment opening : α → List Bool}
    (hkey : ComputableInPolyTime key input S.encodeKey)
    (hmessage : ComputableInPolyTime message input encBits)
    (hcommitment : ComputableInPolyTime commitment input encBits)
    (hopening : ComputableInPolyTime opening input encBits) :
    ComputableInPolyTime
      (fun a => S.verify (key a) (message a) (commitment a) (opening a)) input encBool :=
  ops.verify_polyTime.comp (hkey.prod (hmessage.prod (hcommitment.prod hopening)))

end PublicOperations

end Cslib.Crypto.CommitmentScheme
