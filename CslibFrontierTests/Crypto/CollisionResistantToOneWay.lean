/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.CollisionResistantToOneWay

/-!
# Tests for one-way functions from collision-resistant hash families

Exercises `CslibFrontier/Crypto/Computational/CollisionResistantToOneWay.lean`:
* concrete evaluation of `keyDigest`, including input lengths that are not multiples of three;
* `keyDigest_append` and `isCollision_or_eq_of_keyDigest_eq` on concrete words;
* the endpoint theorems for hash and compression families.
-/

namespace CslibFrontierTests.Crypto.CollisionResistantToOneWay

open Cslib.Crypto Cslib.Crypto.CollisionResistantToOneWay

/-- A toy keyed function with key-length digests: XOR the key into the first bits of the message,
padding with `false`. It is not collision-resistant; it only exercises the slicing in
`keyDigest`. -/
def xorPrefix (key message : List Bool) : List Bool :=
  List.zipWith Bool.xor key message ++ List.replicate (key.length - message.length) false

theorem length_xorPrefix (key message : List Bool) :
    (xorPrefix key message).length = key.length := by
  simp only [xorPrefix, List.length_append, List.length_zipWith, List.length_replicate]
  omega

/-! ### Concrete evaluation -/

/-- At length `6` the key is the first two bits and the message the remaining four. -/
example : keyDigest xorPrefix [true, false, true, true, false, false] =
    [true, false, false, true] := by decide

/-- At length `7 = 3 * 2 + 1` the key still has two bits and the message has five. -/
example : keyDigest xorPrefix [true, true, false, true, false, true, true] =
    [true, true, true, false] := by decide

/-- At length `8 = 3 * 2 + 2` the output still has twice the key's length. -/
example : (keyDigest xorPrefix [true, false, true, true, false, false, true, false]).length =
    4 := by decide

example (H : List Bool → List Bool → List Bool) (key message : List Bool)
    (hmessage : message.length = 2 * key.length + 2) :
    keyDigest H (key ++ message) = key ++ H key message :=
  keyDigest_append H hmessage (by norm_num)

/-- The candidate `[true, true, false]` has the same image as the key `[true]` followed by the
message `[true, true]`, so its message part either collides with `[true, true]` or equals it. -/
example :
    isCollision xorPrefix (fun _ _ => true) 1 [true] [true, true]
      ([true, true, false].drop ([true, true, false].length / 3)) = true ∨
    [true, true, false].drop ([true, true, false].length / 3) = [true, true] :=
  isCollision_or_eq_of_keyDigest_eq length_xorPrefix 1 (by decide)

/-- Here the message part `[true, false]` differs from `[true, true]`, so it is a collision. -/
example : isCollision xorPrefix (fun _ _ => true) 1 [true] [true, true] [true, false] = true := by
  decide

/-! ### Endpoint theorems -/

example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    OneWay (keyDigest H) :=
  hH.oneWay_keyDigest

example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ S : WordSignatureScheme, S.EUFCMA :=
  hH.exists_wordEUFCMA

example {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    (∃ f, OneWay f) ∧ ∃ S : WordSignatureScheme, S.EUFCMA :=
  ⟨hh.exists_oneWay, hh.exists_wordEUFCMA⟩

end CslibFrontierTests.Crypto.CollisionResistantToOneWay
