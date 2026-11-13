/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TwoStage

/-!
# Symmetric ciphers and one-time security

A symmetric cipher `Cipher K M C` has typed keys, messages and ciphertexts. Encryption under a
key is a probabilistic program, and decryption is a function that returns `none` on a ciphertext
it rejects. The cipher carries no key generation: the security game draws the key from a sampler,
so one cipher serves as the data encapsulation mechanism (DEM) of a KEM–DEM hybrid, whose key
comes from the KEM. Correctness is a separate property (`Cipher.Correct`).

`Cipher.oneTimeExperiment` is the one-time chosen-plaintext experiment of a fixed cipher
([BonehShoup2023], Section 2.2, Attack Game 2.1, p. 16): draw a key from `sampleKey` and run the
left-or-right experiment `lrExperiment` under it. The adversary is a `TwoStage` adversary whose
first stage receives no public input; the admissibility predicate `valid` decides which challenge
pairs are allowed, and an inadmissible pair outputs `false` on both sides. Semantic security
(Definition 2.2) asks that the advantage between the two sides be negligible; the asymptotic
statement and the efficiency of the adversary sit on top of this experiment.

## Main definitions

* `Cslib.Crypto.Cipher`: a symmetric cipher with typed keys, messages and ciphertexts.
* `Cslib.Crypto.Cipher.Correct`: every encrypted message decrypts to itself under the same key.
* `Cslib.Crypto.Cipher.oneTimeExperiment`: the one-time chosen-plaintext experiment.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 2.2 (Attack Game 2.1 and Definition 2.2, p. 16).
-/

@[expose] public section

namespace Cslib.Crypto

/-- A symmetric cipher with keys `K`, messages `M` and ciphertexts `C`: probabilistic encryption
under a key and decryption that may reject. Keys are drawn by the game that uses the cipher. -/
structure Cipher (K M C : Type) where
  /-- Encryption of a message under a key. -/
  encrypt : K → M → ProbComp C
  /-- Decryption of a ciphertext with a key; `none` rejects the ciphertext. -/
  decrypt : K → C → Option M

namespace Cipher

variable {K M C : Type}

/-- A cipher is correct when decryption recovers every encrypted message: for every key, message
and ciphertext that encryption of the message under the key can output, decryption with the same
key returns the message. -/
def Correct (E : Cipher K M C) : Prop :=
  ∀ k m, ∀ c ∈ (ProbComp.eval (E.encrypt k m)).support, E.decrypt k c = some m

/-- The one-time chosen-plaintext experiment of the cipher `E` with keys drawn from `sampleKey` and
challenge-pair admissibility predicate `valid` ([BonehShoup2023], Section 2.2, Attack Game 2.1,
p. 16). Draw a key and run the left-or-right experiment under it: the adversary chooses two
messages with no public input; if `valid m₀ m₁` holds, the challenger encrypts the message selected
by `b` and returns the adversary's guess, and otherwise it returns `false`. The key is never passed
to the adversary. -/
def oneTimeExperiment {σ : Type} (E : Cipher K M C) (sampleKey : ProbComp K)
    (valid : M → M → Bool) (A : TwoStage Unit (MessagePair M) C Bool σ) (b : Bool) :
    Experiment := do
  let k ← sampleKey
  lrExperiment (fun _ => valid) (fun _ => E.encrypt k) A b ()

end Cipher

end Cslib.Crypto
