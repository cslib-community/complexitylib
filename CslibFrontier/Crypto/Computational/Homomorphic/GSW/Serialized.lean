/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Sampling.Serialized
public import CslibFrontier.Foundations.Data.Matrix.Binary
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Executable serialized GSW ciphertexts

Ciphertext coordinates `(i, k)` are ordered by `i * w + k`, with `w`-bit residues least
significant first. Serialized LWE key generation (`LWE.keyGenSerialized`,
`LWE.serializePublicMatrix`, `LWE.serializeSecret`, `LWE.decodeSecret`) lives in
`Crypto.Computational.LWE.KeyGen`.

## Main definitions

* `serializeCiphertext`, `decodeCiphertext`: canonical ciphertext bit words and total decoder.
* `encryptWithCoinsSerialized`, `encryptSerialized`: actual ciphertext computations.

## Main results

* `decode_serializeCiphertext`, `length_serializeCiphertext`: exact typed ciphertext roundtrip
  and length.

Exact deterministic and distributional bridges are in `GSW.Serialized.Correctness`; native
certificates for encryption are in `GSW.Serialized.PolyTime`.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability BitString
open scoped BigOperators

/-- Ciphertext coordinates `(i, k)` are ordered by `i * w + k`, in rows and columns. -/
def serializeCiphertext {n w : ℕ} (C : Ciphertext n w) : List Bool :=
  List.ofFn (blocksEquiv.symm fun i => blocksEquiv.symm fun k =>
    blocksEquiv.symm fun j => fun l => C (i, k) (j, l))

/-- Total ciphertext decoding uses the declared dimensions and pads absent bits with `false`. -/
def decodeCiphertext (n w : ℕ) (word : List Bool) : Ciphertext n w :=
  fun i j => block (block (block
    (ofList ((n + 1) * (w * ((n + 1) * w))) word) i.1) i.2) j.1 j.2

/-- Canonical ciphertext words retain every bit. -/
@[simp] theorem decode_serializeCiphertext {n w : ℕ} (C : Ciphertext n w) :
    decodeCiphertext n w (serializeCiphertext C) = C := by
  ext i j
  simp [decodeCiphertext, serializeCiphertext]

/-- The complete ciphertext has the expected square number of bits. -/
@[simp] theorem length_serializeCiphertext {n w : ℕ} (C : Ciphertext n w) :
    (serializeCiphertext C).length = ((n + 1) * w) ^ 2 := by
  simp [serializeCiphertext, pow_two, Nat.mul_assoc]

/-- One entry of `message * G + R * A`, before its bit decomposition. -/
def encryptEntry (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedCoins) (i k j : ℕ) : ℕ :=
  ((if i = j then message.toNat * 2 ^ k else 0) +
    ((List.range m).map fun r =>
      if ((coins.getD i []).getD k []).getD r false then
        Cslib.Matrix.binaryEntry (n + 1) w publicWord r j else 0).sum) % 2 ^ w

/-- Compute all ciphertext bits from the actual public word, message and Boolean coins. -/
def encryptWithCoinsSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedCoins) : List Bool :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range w).flatMap fun k =>
      (List.range (n + 1)).flatMap fun j =>
        lowBits w (encryptEntry n m w publicWord message coins i k j)

/-- Sample the existing Boolean coins and run the actual ciphertext computation. -/
noncomputable def encryptSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp (List Bool) := do
  let coins ← sampleCoinsSerialized n m w
  return encryptWithCoinsSerialized n m w publicWord message coins

end Cslib.Crypto.Homomorphic.GSW
