/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary

/-!
# Encodings of the inputs of cryptographic algorithms

Encryption, decryption, keyed hash functions, block ciphers and message authentication all run a
keyed algorithm at a security parameter `n`, and an experiment that has generated a key pair runs
its adversary with both keys at hand. Their efficiency certificates take the security parameter
in unary first, as `1ⁿ`, followed by the bit-word key and the payload. This module names those
input encodings by role, so that statements need not spell out the nested pairs.

Both names are reducible abbreviations, so `fun_prop`, instance search and the combinators' lemmas
see through them. `omega` does not, since it compares atoms syntactically: state the bounds that it
combines with the same spelling.

## Main definitions

* `Cslib.Crypto.encKeyedInput`: the input `(1ⁿ, key, x)` of a keyed algorithm.
* `Cslib.Crypto.encKeyPairInput`: the input `(1ⁿ, pk, sk)` of an experiment after key generation.
-/

@[expose] public section

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

end Cslib.Crypto
