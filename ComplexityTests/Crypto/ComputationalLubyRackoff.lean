/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.LubyRackoff
import Complexity.Tactic.PolyTime

/-!
# Tests for the computational Luby–Rackoff cipher

The toy family that masks the input with the key is length preserving and computable in
polynomial time, so it instantiates `lubyRackoffCipher`. Concrete encryptions follow the three
Feistel rounds of Boneh–Shoup, decryption inverts them, and the oracle rejects blocks of the wrong
length. The adapter's query program answers malformed blocks without querying. The Luby–Rackoff
theorem applies to every pseudorandom function. The four-round cipher of the toy family adds one
round, its strong oracle decrypts its own ciphertexts, and the four-round theorem applies to every
pseudorandom function.
-/

namespace ComplexityTests.Crypto.ComputationalLubyRackoff

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- A toy keyed family: the key masks the input. It is not pseudorandom. -/
def xorFamily (key query : List Bool) : List Bool := List.zipWith Bool.xor key query

theorem xorFamily_polyTime : ComputableInPolyTime
    (fun pair : List Bool × List Bool => xorFamily pair.1 pair.2) (encPair encBits encBits)
      encBits := by
  unfold xorFamily
  polytime

theorem length_xorFamily (key query : List Bool) (h : query.length = key.length) :
    (xorFamily key query).length = key.length := by
  simp [xorFamily, h]

/-- The Luby–Rackoff cipher of the toy family. -/
abbrev toyCipher : BlockCipher := lubyRackoffCipher xorFamily xorFamily_polyTime length_xorFamily

-- With `n = 1`, the key `[k₁, k₂, k₃]` and block `[u, v]`: `w = u ⊕ k₁ ⊕ v`,
-- `x = v ⊕ k₂ ⊕ w` and `y = w ⊕ k₃ ⊕ x`, so `[false, true]` encrypts to `[false, false]`
-- under the key `[true, true, false]`.
example : toyCipher.encrypt 1 [true, true, false] [false, true] = [false, false] := by decide
example : toyCipher.decrypt 1 [true, true, false] [false, false] = [false, true] := by decide
example : toyCipher.keyLen 5 = 15 := rfl
example : toyCipher.blockLen 5 = 10 := rfl

-- The encryption oracle rejects blocks of the wrong length.
example : toyCipher.prpOracle 1 [true, true, false] [false] = [] := by decide

-- Decryption inverts encryption on valid keys and blocks.
example : toyCipher.decrypt 2 [true, false, false, true, true, true]
    (toyCipher.encrypt 2 [true, false, false, true, true, true] [true, true, false, true]) =
      [true, true, false, true] :=
  toyCipher.decrypt_encrypt 2 _ _ (by decide) (by decide)

-- A malformed block is answered without any query.
example : lubyRackoffQuery 2 [true] = pure [] := by
  simp [lubyRackoffQuery]

-- The Luby–Rackoff theorem, applied to an arbitrary pseudorandom function.
example {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family)
    {adversary : OracleDistinguisher} (hadversary : Probability.IsOraclePPT encBool adversary) :
    Negligible fun n => Game.advantage
      (ProbComp.eval ((lubyRackoffCipher family hfamily.polyTime hfamily.length_eq).prpRealGame
        adversary n))
      (ProbComp.eval (prpIdealGame (fun n => 2 * n) adversary n)) :=
  hfamily.prp_lubyRackoffCipher adversary hadversary

/-- The four-round Luby–Rackoff cipher of the toy family. -/
abbrev toyCipher4 : BlockCipher := lubyRackoff4Cipher xorFamily xorFamily_polyTime length_xorFamily

-- A fourth round `(x, y) ↦ (y, x ⊕ k₄ ⊕ y)` follows the three-round output `[false, false]`.
example : toyCipher4.encrypt 1 [true, true, false, true] [false, true] = [false, true] := by
  decide
example : toyCipher4.decrypt 1 [true, true, false, true] [false, true] = [false, true] := by
  decide
example : toyCipher4.keyLen 5 = 20 := rfl

-- The decryption channel of the strong oracle inverts the encryption channel.
example : toyCipher4.strongPRPOracle 1 [true, true, false, true]
    (true, toyCipher4.strongPRPOracle 1 [true, true, false, true] (false, [true, false])) =
      [true, false] := by
  decide

-- A malformed bidirectional query is answered without any query.
example : strongLubyRackoffQuery 2 (true, [true]) = pure [] := by
  simp [strongLubyRackoffQuery]

-- The four-round theorem, applied to an arbitrary pseudorandom function.
example {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family)
    {adversary : StrongPRPDistinguisher}
    (hadversary : Probability.IsOraclePPT encBool adversary) :
    Negligible fun n => Game.advantage
      (ProbComp.eval
        ((lubyRackoff4Cipher family hfamily.polyTime hfamily.length_eq).strongPRPRealGame
          adversary n))
      (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n) adversary n)) :=
  hfamily.strongPRP_lubyRackoff4Cipher adversary hadversary

end ComplexityTests.Crypto.ComputationalLubyRackoff
