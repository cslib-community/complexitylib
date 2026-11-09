/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Encodings for acyclic leveled encryption

The public artifact contains the list of public keys and the adjacent encrypted secret-key
links. The private artifact contains only the initial and final secrets. Both use existing
framed encodings and total polynomial-time decoders; no private key is part of the public data.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.encPublicKey`: public keys and encrypted links.
* `Cslib.Crypto.Homomorphic.Leveled.publicKeyDecoder`: total public-artifact decoding.
* `Cslib.Crypto.Homomorphic.Leveled.encSecretKey`: the two endpoint secrets.
* `Cslib.Crypto.Homomorphic.Leveled.secretKeyDecoder`: total private-artifact decoding.

## References

The acyclic key chain follows [Gentry, Section 2][Gentry2009]. Retaining two private endpoints
supports both fresh and evaluated decryption through the same bit-string scheme interface.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Turing.MultiTapeTM

/-- Encode every public key and adjacent encrypted link, with no unencrypted secret key. -/
def encPublicKey :
    (List (List Bool) × List (List (List Bool))) ↪ List Bool :=
  encPair (encList encBits) (encList (encList encBits))

/-- Decode every public string; framing errors retain the standard total-decoder behavior. -/
def publicKeyDecoder : Decoder encPublicKey :=
  (Decoder.bits.list).pair (Decoder.bits.list.list)

/-- Encode the initial and final secret, independently of the length of the public key chain. -/
def encSecretKey : (List Bool × List Bool) ↪ List Bool := encPair encBits encBits

/-- Decode the two private endpoint secrets from any bit string. -/
def secretKeyDecoder : Decoder encSecretKey := Decoder.bits.pair Decoder.bits

@[simp] theorem publicKeyDecoder_decode_enc (keys : List (List Bool))
    (links : List (List (List Bool))) :
    publicKeyDecoder.decode (encPublicKey (keys, links)) = (keys, links) :=
  publicKeyDecoder.decode_enc _

@[simp] theorem secretKeyDecoder_decode_enc (first last : List Bool) :
    secretKeyDecoder.decode (encSecretKey (first, last)) = (first, last) :=
  secretKeyDecoder.decode_enc _

/-- The private representation charges the framing of its first endpoint. -/
@[simp] theorem length_encSecretKey (first last : List Bool) :
    (encSecretKey (first, last)).length = 2 * first.length + 1 + last.length := by
  simp [encSecretKey]

end Cslib.Crypto.Homomorphic.Leveled
