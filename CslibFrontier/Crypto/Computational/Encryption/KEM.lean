/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment

/-!
# Key encapsulation mechanisms

A key encapsulation mechanism (KEM) `KEM PK SK CT K` has typed public keys, secret keys,
ciphertexts and keys. Key generation draws a key pair, encapsulation under a public key draws a
ciphertext together with the key it encapsulates, and decapsulation recovers the key from a
ciphertext with the secret key, returning `none` on a ciphertext it rejects
([HofheinzHoevelmannsKiltz2017], Section 2.2). Correctness is a separate property
(`KEM.Correct`), so a scheme with decapsulation errors is still a `KEM`. A KEM with implicit
rejection, whose decapsulation always returns a key, is the instance with `decaps sk c = some _`.

In the indistinguishability game for a KEM, the challenger generates a key pair, encapsulates a
key under the public key, and gives the adversary the public key, the challenge ciphertext and a
challenge key: the encapsulated key or an independent random key, depending on the hidden bit
([HofheinzHoevelmannsKiltz2017], Section 2.2, Definition 2.4). `KEM.Challenge PK CT K` is that
input, with named fields in place of a triple `PK × CT × K`. `KEM.cpaExperiment` is the game of
one fixed scheme against a distinguisher on the challenge; the random key is drawn from a sampler
`sampleKey`, uniform on `K` in the paper. Asymptotic security over a family of schemes and the
efficiency of the distinguisher are stated on top of this experiment.

## Main definitions

* `Cslib.Crypto.KEM.Challenge`: the public key, challenge ciphertext and challenge key given to a
  KEM adversary.
* `Cslib.Crypto.KEM`: a key encapsulation mechanism with typed keys and ciphertexts.
* `Cslib.Crypto.KEM.Correct`: decapsulation recovers every honestly encapsulated key.
* `Cslib.Crypto.KEM.cpaExperiment`: the chosen-plaintext indistinguishability experiment.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), Section 2.2, Definition 2.4.
-/

@[expose] public section

namespace Cslib.Crypto

/-- The input of a KEM indistinguishability adversary ([HofheinzHoevelmannsKiltz2017],
Section 2.2, Definition 2.4): the public key, the challenge ciphertext and the challenge key. -/
structure KEM.Challenge (PK CT K : Type) where
  /-- The public key. -/
  pk : PK
  /-- The challenge ciphertext, an encapsulation under `pk`. -/
  ct : CT
  /-- The challenge key: the key encapsulated in `ct`, or an independent random key, depending on
  the challenge bit. -/
  key : K

/-- A key encapsulation mechanism ([HofheinzHoevelmannsKiltz2017], Section 2.2) with public keys
`PK`, secret keys `SK`, ciphertexts `CT` and keys `K`. -/
structure KEM (PK SK CT K : Type) where
  /-- Key generation: draw a public key and its secret key. -/
  keyGen : ProbComp (PK × SK)
  /-- Encapsulation under a public key: draw a ciphertext and the key it encapsulates. -/
  encaps : PK → ProbComp (CT × K)
  /-- Decapsulation of a ciphertext with a secret key; `none` rejects the ciphertext. -/
  decaps : SK → CT → Option K

namespace KEM

variable {PK SK CT K : Type}

/-- A KEM is correct when decapsulation recovers every honestly encapsulated key: for every key
pair that key generation can output and every ciphertext and key that encapsulation under the
public key can output, decapsulation of the ciphertext with the secret key returns the key. -/
def Correct (E : KEM PK SK CT K) : Prop :=
  ∀ keys ∈ (ProbComp.eval E.keyGen).support,
    ∀ ck ∈ (ProbComp.eval (E.encaps keys.1)).support, E.decaps keys.2 ck.1 = some ck.2

/-- The chosen-plaintext indistinguishability experiment of the KEM `E` with random keys drawn
from `sampleKey` ([HofheinzHoevelmannsKiltz2017], Section 2.2, Definition 2.4). Draw a key pair
and encapsulate a key under the public key. On `b = false` the challenge key is the encapsulated
key; on `b = true` it is an independent key drawn from `sampleKey`. The distinguisher receives the
public key, the ciphertext and the challenge key, and its guess is the output. -/
def cpaExperiment (E : KEM PK SK CT K) (sampleKey : ProbComp K)
    (D : Challenge PK CT K → ProbComp Bool) (b : Bool) : Experiment := do
  let keys ← E.keyGen
  let encapsulated ← E.encaps keys.1
  let key ← if b then sampleKey else pure encapsulated.2
  D ⟨keys.1, encapsulated.1, key⟩

end KEM

end Cslib.Crypto
