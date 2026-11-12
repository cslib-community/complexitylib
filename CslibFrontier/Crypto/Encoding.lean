/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary

/-!
# Encodings of the inputs of cryptographic algorithms

Encryption, decryption, keyed hash functions, block ciphers and message authentication all run a
keyed algorithm at a security parameter `n`, and an experiment that has generated a key pair runs
its adversary with both keys at hand. A zero-knowledge experiment runs a malicious verifier and its
simulator on an instance and an auxiliary input, and the honest prover also on a witness. Their
efficiency certificates take the security parameter in unary first, as `1ⁿ`, followed by the
key and the payload, or by the instance, the witness and the auxiliary input. This module names
those input encodings by role, so that statements need not spell out the nested pairs.

All names are reducible abbreviations, so `fun_prop`, instance search and the combinators' lemmas
see through them. `omega` does not, since it compares atoms syntactically: state the bounds that it
combines with the same spelling.

## Main definitions

* `Cslib.Crypto.encKeyedInput`: the input `(1ⁿ, key, x)` of a keyed algorithm.
* `Cslib.Crypto.encKeyPairInput`: the input `(1ⁿ, pk, sk)` of an experiment after key generation.
* `Cslib.Crypto.encInstanceAuxInput`: the input `(1ⁿ, a, z)` with an instance and an auxiliary
  input word.
* `Cslib.Crypto.encInstanceWitnessAuxInput`: the input `(1ⁿ, a, w, z)` of a zero-knowledge
  experiment that also runs the honest prover.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- Input `(1ⁿ, key, x)` of a keyed algorithm, such as encryption, decryption, decapsulation or a
keyed hash: the security parameter `n` in unary, the key as a bit word, and `x` encoded by
`encX`. The parameter and the key are framed; `x` is not. -/
abbrev encKeyedInput {α : Type} (encX : α ↪ List Bool) : ℕ × List Bool × α ↪ List Bool :=
  encPair encUnary (encPair encBits encX)

/-- Input `(1ⁿ, pk, sk)` of an experiment after key generation, such as a run of the adversary
against a signing or decryption oracle: the security parameter `n` in unary, then the public key
and the secret key as bit words. The parameter and the public key are framed. The layout is that
of `encKeyedInput encBits`; the name records the role. -/
abbrev encKeyPairInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Input `(1ⁿ, a, z)` of an algorithm taking a unary security parameter `n`, an instance `a`
encoded by `enc`, and an auxiliary input word `z`, such as a malicious verifier or a
zero-knowledge simulator. The parameter and the instance are framed; `z` is not. A distinguisher
takes the same triple paired with a view, as `encPair (encInstanceAuxInput enc) encBits`, with an
auxiliary input word in the `z` slot. The layout is that of
`Cslib.Probability.encAuxTriple encUnary enc`; the name records the role. -/
abbrev encInstanceAuxInput {α : Type} (enc : α ↪ List Bool) : ℕ × α × List Bool ↪ List Bool :=
  encPair encUnary (encPair enc encBits)

/-- Input `(1ⁿ, a, w, z)` of a zero-knowledge experiment that runs the honest prover with witness
`w` against a malicious verifier with auxiliary input `z`, such as the honest interaction or a
hybrid reduction: the security parameter `n` in unary, the instance `a` encoded by `enc`, then the
witness and the auxiliary input as bit words. The parameter, the instance and the witness are
framed; `z` is not. It is `encInstanceAuxInput enc` with the witness inserted before `z`. -/
abbrev encInstanceWitnessAuxInput {α : Type} (enc : α ↪ List Bool) :
    ℕ × α × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair enc (encPair encBits encBits))

end Cslib.Crypto
