/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Hash.Sponge
import CslibFrontier.Crypto.Primitives.Hash.BlockCipherCompression

/-!
# Tests for the sponge construction and block-cipher compression functions

Concrete evaluations of `pad`, `toBlocks` and `hash` on small parameters, explicit sponge
collisions for a permutation acting separately on the rate and capacity parts, and explicit
collisions for the compression functions of [KatzLindell2020], Exercises 7.23 and 7.24. The
examples check that the hypotheses of the main results are satisfiable.
-/

namespace CslibFrontierTests.Crypto.Sponge

open Cslib Cslib.Crypto Cslib.Crypto.Sponge Cslib.Crypto.BlockCipherCompression

/-! ### Padding and parsing -/

example : pad 2 [] = [true, false] := rfl

example : pad 2 [true] = [true, true] := rfl

example : pad 3 [false, true, true] = [false, true, true, true, false, false] := rfl

example : toBlocks 2 [true, false, false, true, true] = [![true, false], ![false, true]] := by
  decide

/-! ### Sponge hashes on a rate-1, capacity-1 state -/

/-- The permutation swapping the rate and capacity bits of a two-bit state. -/
def swapState : Equiv.Perm (BitString 1 × BitString 1) :=
  Equiv.prodComm _ _

/-- Output the rate bit. -/
def rateBit (y : BitString 1 × BitString 1) : Bool :=
  y.1 0

example : hash swapState rateBit 2 [] = [false, true] := by decide

example : hash swapState rateBit 2 [true] = [true, true] := by decide

/-- With the swap permutation, the messages `[]` and `[false, false]` collide on two outputs. -/
example : hash swapState rateBit 2 [] = hash swapState rateBit 2 [false, false] := by decide

-- That collision triggers one of the bad events of Claim 7.8.
example :
    ImageCollision swapState rateBit (fun x => IsInput swapState (toBlocks 1 (pad 1 [])) x ∨
        IsInput swapState (toBlocks 1 (pad 1 [false, false])) x) ∨
      ZeroCapacity swapState (fun x => IsInput swapState (toBlocks 1 (pad 1 [])) x ∨
        IsInput swapState (toBlocks 1 (pad 1 [false, false])) x) ∨
      ImageCollision swapState Prod.snd (fun x => IsInput swapState (toBlocks 1 (pad 1 [])) x ∨
        IsInput swapState (toBlocks 1 (pad 1 [false, false])) x) :=
  badEvent_of_hash_eq one_pos swapState rateBit 1 (by decide) (by decide)

/-! ### Exercise 7.26: a permutation acting separately on rate and capacity -/

/-- A rate permutation of two-bit blocks: add the constant `10`. -/
def rateShift : Equiv.Perm (BitString 2) :=
  Equiv.addLeft ![true, false]

/-- A capacity permutation of two-bit blocks: flip both bits. -/
def capacitySwap : Equiv.Perm (BitString 2) :=
  Equiv.addLeft ![true, true]

example := hash_prodCongr_collision two_pos rateShift capacitySwap ![false, true] Prod.fst 3

-- The colliding pair is concrete: `0001` and `1110` have equal three-block hashes.
example : hash (rateShift.prodCongr capacitySwap) Prod.fst 3 [false, false, false, true] =
    hash (rateShift.prodCongr capacitySwap) Prod.fst 3 [true, true, true, false] := by
  decide

/-! ### Compression functions from block ciphers -/

/-- A toy two-bit cipher: `F_k(x) = k + x`. -/
def xorCipher (k : BitString 2) : Equiv.Perm (BitString 2) :=
  Equiv.addLeft k

-- Exercise 7.23(a): keys `00` and `11` with target `00`.
example := cipherOutput_collision xorCipher (k := ![false, false]) (k' := ![true, true])
    (by decide) 0

example : cipherOutput xorCipher (![false, false], 0) =
    cipherOutput xorCipher (![true, true], ![true, true]) := by decide

-- Exercise 7.23(c): with this cipher, `h(k, x) = k + x + k = x` ignores the key.
example : keyMasked xorCipher (![false, false], ![true, false]) =
    keyMasked xorCipher (![true, true], ![true, false]) := by decide

example (k k' : BitString 2) (hk : k ≠ k') :
    keyMasked xorCipher (k, (xorCipher k).symm (0 - k)) =
      keyMasked xorCipher (k', (xorCipher k').symm (0 - k')) :=
  (keyMasked_collision xorCipher hk 0).2

-- Exercise 7.24: under the identity cipher every block is a fixed point, so Davies–Meyer sends
-- every block to `0`.
example : daviesMeyer (fun _ : Unit => Equiv.refl (BitString 2)) ((), ![true, false]) =
    daviesMeyer (fun _ : Unit => Equiv.refl (BitString 2)) ((), ![false, true]) :=
  daviesMeyer_collision_of_fixedPoints _ rfl rfl

example : daviesMeyer (fun _ : Unit => Equiv.refl (BitString 2)) ((), ![true, false]) = 0 := by
  decide

end CslibFrontierTests.Crypto.Sponge
