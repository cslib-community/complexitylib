/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TwoStage

/-!
# Public-key encryption schemes

A public-key encryption scheme `PKE PK SK M C` has typed public keys, secret keys, messages and
ciphertexts. Key generation and encryption are probabilistic programs; decryption is a function
that returns `none` on a ciphertext it rejects ([BonehShoup2023], Section 11.2, Definition 11.1).
Correctness is a separate property (`PKE.Correct`), so a scheme with decryption errors is still a
`PKE`.

`PKE.cpaExperiment` is the single-challenge chosen-plaintext experiment of one fixed scheme
([BonehShoup2023], Section 11.2, Attack Game 11.1, p. 436): draw a key pair and run the
left-or-right experiment `lrExperiment` on the public key. The adversary is a `TwoStage`
adversary with an arbitrary state type. The admissibility predicate `valid` decides which
challenge pairs are allowed; Attack Game 11.1 requires equal lengths, and an inadmissible pair
outputs `false` on both sides. Asymptotic security over a family of schemes and the efficiency of
the adversary are stated on top of this experiment.

## Main definitions

* `Cslib.Crypto.PKE`: a public-key encryption scheme with typed keys, messages and ciphertexts.
* `Cslib.Crypto.PKE.Correct`: every honestly encrypted message decrypts to itself.
* `Cslib.Crypto.PKE.cpaExperiment`: the single-challenge chosen-plaintext experiment.

## Main results

* `Cslib.Crypto.PKE.eval_cpaExperiment`: the experiment observes only the public-key marginal of
  key generation.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2 (Definition 11.1 and Attack Game 11.1, p. 436).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- A public-key encryption scheme ([BonehShoup2023], Definition 11.1) with public keys `PK`,
secret keys `SK`, messages `M` and ciphertexts `C`. -/
structure PKE (PK SK M C : Type) where
  /-- Key generation: draw a public key and its secret key. -/
  keyGen : ProbComp (PK × SK)
  /-- Encryption of a message under a public key. -/
  encrypt : PK → M → ProbComp C
  /-- Decryption of a ciphertext with a secret key; `none` rejects the ciphertext. -/
  decrypt : SK → C → Option M

namespace PKE

variable {PK SK M C : Type}

/-- A scheme is correct when decryption recovers every honestly encrypted message: for every key
pair that key generation can output and every ciphertext that encryption of `m` can output,
decryption with the secret key returns `m` ([BonehShoup2023], Definition 11.1). -/
def Correct (E : PKE PK SK M C) : Prop :=
  ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ m,
    ∀ c ∈ (ProbComp.eval (E.encrypt keys.1 m)).support, E.decrypt keys.2 c = some m

/-- The single-challenge chosen-plaintext experiment of the scheme `E` with challenge-pair
admissibility predicate `valid` ([BonehShoup2023], Section 11.2, Attack Game 11.1, p. 436). Draw a
key pair and run the left-or-right experiment on the public key: the adversary chooses two
messages from the public key; if `valid pk m₀ m₁` holds, the challenger encrypts the message
selected by `b` and returns the adversary's guess, and otherwise it returns `false`. The secret key
is never passed to the adversary. -/
def cpaExperiment {σ : Type} (E : PKE PK SK M C) (valid : PK → M → M → Bool)
    (A : TwoStage PK (MessagePair M) C Bool σ) (b : Bool) : Experiment := do
  let keys ← E.keyGen
  lrExperiment valid E.encrypt A b keys.1

/-- The chosen-plaintext experiment observes only the public-key marginal of key generation: it is
the left-or-right experiment on a public key drawn from that marginal. -/
theorem eval_cpaExperiment {σ : Type} (E : PKE PK SK M C) (valid : PK → M → M → Bool)
    (A : TwoStage PK (MessagePair M) C Bool σ) (b : Bool) :
    ProbComp.eval (E.cpaExperiment valid A b) =
      Game.withSetup ((ProbComp.eval E.keyGen).map Prod.fst)
        (lrExperiment valid E.encrypt A b) := by
  simp only [cpaExperiment, Game.withSetup, ProbComp.eval_bind, PMF.bind_map, Function.comp_def]

end PKE

end Cslib.Crypto
