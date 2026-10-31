/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Sampling.Serialized
public import Complexity.Foundations.Data.Matrix.Binary
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Executable serialized GSW keys and ciphertexts

Residues are written with exactly `w` bits, least significant first, and matrices are row major.
The dimensions are explicit inputs to the algorithms. Missing list entries and bits are zero;
excess data is ignored. Integer errors are reduced by Euclidean remainder, so negative errors
wrap correctly. These conventions specify total behavior on malformed inputs.

The programs below compute the public matrix and ciphertext of
[Gentry, Sahai and Waters, Section 3.1][GentrySahaiWaters2013]. The computational certificates
are separate from the exact algebraic bridges. No security or bootstrappability is asserted.

## Main definitions

* `serializePublicMatrix`, `serializeSecret`, `serializeCiphertext`: canonical typed words.
* `publicMatrixSerialized`, `encryptWithCoinsSerialized`: total deterministic computations.
* `keyGenSerialized`, `encryptSerialized`: the actual probabilistic word-valued algorithms.

## Main results

* `decode_serializeSecret`, `decode_serializeCiphertext`: exact typed roundtrips.
* `length_serializePublicMatrix`, `length_serializeSecret`, `length_serializeCiphertext`:
  complete fixed-width output lengths.

Exact deterministic and distributional bridges are in `GSW.Serialized.Correctness`; native
certificates for the complete programs are in `GSW.Serialized.PolyTime`.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability BitString
open scoped BigOperators

/-- Canonical public matrices use the generic fixed-width row-major representation. -/
def serializePublicMatrix {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) : List Bool :=
  Cslib.Matrix.toBinary A

/-- Canonical secret residues are consecutive low-order-first words. -/
def serializeSecret {n w : ℕ} (secret : Fin n → ZMod (2 ^ w)) : List Bool :=
  Cslib.Matrix.toBinary (fun _ : Fin 1 => secret)

/-- Total secret decoding reads the declared number of residue words, padding with zero bits. -/
def decodeSecret (n w : ℕ) (word : List Bool) : Fin n → ZMod (2 ^ w) :=
  Cslib.Matrix.ofBinary 1 n w word 0

/-- Canonical secret words retain every residue. -/
@[simp] theorem decode_serializeSecret {n w : ℕ} (secret : Fin n → ZMod (2 ^ w)) :
    decodeSecret n w (serializeSecret secret) = secret := by
  exact congrArg (fun A => A 0) (Cslib.Matrix.ofBinary_toBinary (fun _ : Fin 1 => secret))

@[simp] theorem length_serializePublicMatrix {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) :
    (serializePublicMatrix A).length = m * (n + 1) * w :=
  Cslib.Matrix.length_toBinary A

@[simp] theorem length_serializeSecret {n w : ℕ} (secret : Fin n → ZMod (2 ^ w)) :
    (serializeSecret secret).length = n * w := by
  simpa only [serializeSecret, Nat.one_mul] using
    Cslib.Matrix.length_toBinary (fun _ : Fin 1 => secret)

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

/-- Compute the leading entry `B * secret + error` of a public row in binary arithmetic. -/
def publicRowHead (n w : ℕ) (inputs : SerializedKeyInputs) (i : ℕ) : ℕ :=
  let pe := inputs.2
  (((((List.range n).map fun j =>
    (pe.1.getD i []).getD j 0 * inputs.1.getD j 0).sum : ℕ) +
      pe.2.getD i 0 : ℤ) % (2 ^ w : ℤ)).toNat

/-- Compute the public word from arbitrary serialized sampled inputs. -/
def publicMatrixSerialized (n m w : ℕ) (inputs : SerializedKeyInputs) : List Bool :=
  let pe := inputs.2
  (List.range m).flatMap fun i =>
    lowBits w (publicRowHead n w inputs i) ++
      (List.range n).flatMap fun j =>
        lowBits w ((pe.1.getD i []).getD j 0 % 2 ^ w)

/-- Normalize and serialize an arbitrary secret list to the declared dimensions. -/
def secretSerialized (n w : ℕ) (secret : List ℕ) : List Bool :=
  (List.range n).flatMap fun j => lowBits w (secret.getD j 0 % 2 ^ w)

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

/-- Sample the existing random inputs and run the actual public-key computation. -/
noncomputable def keyGenSerialized (n m w η : ℕ) : ProbComp (List Bool × List Bool) := do
  let inputs ← sampleKeyInputsSerialized n m w η
  return (publicMatrixSerialized n m w inputs, secretSerialized n w inputs.1)

/-- Sample the existing Boolean coins and run the actual ciphertext computation. -/
noncomputable def encryptSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp (List Bool) := do
  let coins ← sampleCoinsSerialized n m w
  return encryptWithCoinsSerialized n m w publicWord message coins

end Cslib.Crypto.Homomorphic.GSW
