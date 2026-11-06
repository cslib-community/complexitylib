/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Serialized leveled public-key sizes

The length formula charges every framed public key, encrypted link and ciphertext. It is
independent of security assumptions and applies to every artifact with the given dimensions.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.publicKeyLengthBound`: the serialized artifact bound.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.publicKeyLengthBound_mono`: monotonicity of the bound.
* `Cslib.Crypto.Homomorphic.Leveled.length_encPublicKey_le`: the structural length estimate.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Turing.MultiTapeTM

/-- Explicit upper bound on the bit length of a serialized leveled public key
`encPublicKey (pks, links)` with `depth + 1` base public keys of length at most `pkBound` and
`depth` encrypted links each consisting of at most `width` base ciphertexts of length at most
`ctBound`. -/
def publicKeyLengthBound (depth width pkBound ctBound : ℕ) : ℕ :=
  2 * ((depth + 1) * (2 * pkBound + 1)) + 1 +
    depth * (2 * (width * (2 * ctBound + 1)) + 1)

/-- `publicKeyLengthBound` is monotone in all four parameters. -/
theorem publicKeyLengthBound_mono {d₁ d₂ w₁ w₂ p₁ p₂ c₁ c₂ : ℕ}
    (hd : d₁ ≤ d₂) (hw : w₁ ≤ w₂) (hp : p₁ ≤ p₂) (hc : c₁ ≤ c₂) :
    publicKeyLengthBound d₁ w₁ p₁ c₁ ≤ publicKeyLengthBound d₂ w₂ p₂ c₂ := by
  unfold publicKeyLengthBound
  gcongr

/-- Explicit bit-length bound for `encPublicKey (pks, links)` whenever the key list and link table
satisfy the stated length caps. -/
theorem length_encPublicKey_le (depth width pkBound ctBound : ℕ)
    (pks : List (List Bool)) (links : List (List (List Bool)))
    (hpks_len : pks.length ≤ depth + 1)
    (hpks : ∀ pk ∈ pks, pk.length ≤ pkBound)
    (hlinks_len : links.length ≤ depth)
    (hlinks : ∀ link ∈ links, link.length ≤ width ∧ ∀ ct ∈ link, ct.length ≤ ctBound) :
    (encPublicKey (pks, links)).length ≤ publicKeyLengthBound depth width pkBound ctBound := by
  have hpks_enc : (encList encBits pks).length ≤ (depth + 1) * (2 * pkBound + 1) :=
    (Turing.MultiTapeTM.length_encList_le encBits pks hpks).trans
      (Nat.mul_le_mul_right _ hpks_len)
  have hlink_enc (link : List (List Bool)) (hlink : link ∈ links) :
      (encList encBits link).length ≤ width * (2 * ctBound + 1) :=
    (Turing.MultiTapeTM.length_encList_le encBits link (hlinks link hlink).2).trans
      (Nat.mul_le_mul_right _ (hlinks link hlink).1)
  have hlinks_enc :
      (encList (encList encBits) links).length ≤
        depth * (2 * (width * (2 * ctBound + 1)) + 1) :=
    (Turing.MultiTapeTM.length_encList_le (encList encBits) links hlink_enc).trans
      (Nat.mul_le_mul_right _ hlinks_len)
  simp only [encPublicKey, length_encPair, publicKeyLengthBound]
  omega

end Cslib.Crypto.Homomorphic.Leveled
