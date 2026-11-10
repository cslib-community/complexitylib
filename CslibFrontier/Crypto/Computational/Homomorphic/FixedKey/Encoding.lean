/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Circular
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# Public artifacts for fixed-key bootstrapping

The public artifact is one base public key and one vector encrypting its secret-key bits.
Its encoding is the same one used by the explicit circular-security experiment. A total
native decoder handles arbitrary bit strings. The private key remains the base secret word.

## Main definitions

* `Cslib.Crypto.Homomorphic.FixedKey.encPublicKey`: the serialized public artifact.
* `Cslib.Crypto.Homomorphic.FixedKey.publicKeyDecoder`: its total decoder.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009], Section 2.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.FixedKey

open Turing.MultiTapeTM

/-- Use the joint circular-experiment encoding for the fixed public artifact. -/
abbrev encPublicKey : (List Bool × List (List Bool)) ↪ List Bool :=
  Encryption.encCircularPublicKey

/-- Decode every public string with the standard total framing behavior. -/
def publicKeyDecoder : Decoder encPublicKey := Decoder.bits.pair Decoder.bits.list

@[simp] theorem publicKeyDecoder_decode_enc (pk : List Bool) (encryptedKey : List (List Bool)) :
    publicKeyDecoder.decode (encPublicKey (pk, encryptedKey)) = (pk, encryptedKey) :=
  publicKeyDecoder.decode_enc _

end Cslib.Crypto.Homomorphic.FixedKey
