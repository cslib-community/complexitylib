/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.PseudorandomPermutation
import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Tactic.PolyTime

/-!
# Tests for block ciphers and pseudorandom permutations

The key-masking cipher `xorCipher` (encryption and decryption both XOR the key into the block)
satisfies every structural law of `BlockCipher`, so the bundled length, inversion and
polynomial-time hypotheses are satisfiable. Its induced permutation and its oracles are evaluated
on concrete words, including the rejection of malformed queries and the decryption channel.

Fixing the private coins of a program that flips a coin and then queries one of two points turns
it into the deterministic query selected by the fixed coin, without changing its query budget.
-/

namespace ComplexityTests.Crypto.PseudorandomPermutation

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- The key-masking cipher on `n`-bit keys and blocks. It is a permutation for every key but is
not pseudorandom: XORing two ciphertexts cancels the key. -/
def xorCipher : BlockCipher where
  keyLen := id
  blockLen := id
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt _ key block := List.zipWith Bool.xor key block
  decrypt _ key block := List.zipWith Bool.xor key block
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ hkey hblock := by simp [hkey, hblock]
  length_decrypt _ _ _ hkey hblock := by simp [hkey, hblock]
  decrypt_encrypt _ key block hkey hblock :=
    BitString.zipWith_xor_self_left key block (by simp [hkey, hblock])
  encrypt_decrypt _ key block hkey hblock :=
    BitString.zipWith_xor_self_left key block (by simp [hkey, hblock])

-- The key `[true, false]` flips the first bit of a two-bit block.
example : xorCipher.permEquiv 2 [true, false] rfl ![false, true] = ![true, true] := by
  funext i
  fin_cases i <;> rfl
example : (xorCipher.permEquiv 2 [true, false] rfl).symm ![true, true] = ![false, true] := by
  funext i
  fin_cases i <;> rfl

-- Valid encryption and decryption queries, and a malformed query of the wrong length.
example : xorCipher.prpOracle 2 [true, false] [false, true] = [true, true] := by decide
example : xorCipher.prpOracle 2 [true, false] [false] = [] := by decide
example : xorCipher.strongPRPOracle 2 [true, true] (true, [false, true]) = [true, false] := by
  decide

-- The ideal oracles read the sampled permutation and reject malformed words in the same way.
example : randomPermOracle 1 (Equiv.swap ![false] ![true]) [false] = [true] := by decide
example : randomPermOracle 1 (Equiv.swap ![false] ![true]) [false, false] = [] := by decide
example : strongRandomPermOracle 1 (Equiv.swap ![false] ![true]) (true, [true]) = [false] := by
  decide

-- A valid key answers as its induced permutation.
example : xorCipher.prpOracle 2 [true, false] [false, true] =
    randomPermOracle 2 (xorCipher.permEquiv 2 [true, false] rfl) [false, true] :=
  xorCipher.prpOracle_eq_randomPermOracle (n := 2) (key := [true, false]) rfl _

/-- Flip a fair coin, then query `0` or `1` and return the reply. -/
def coinThenQuery : ProbOracleComp (fun _ : Fin 2 => Bool) Bool := do
  let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
  ProbOracleComp.query (if c = 0 then 0 else 1)

-- Fixing the coin to `1` leaves the deterministic query of the point `1`.
example (ω : ProbOracleComp.Coins coinThenQuery) (hω : ω.1 = 1) :
    ProbOracleComp.fixCoins coinThenQuery ω =
      OracleComp.query (spec := fun _ : Fin 2 => Bool) 1 := by
  obtain ⟨c, ω'⟩ := ω
  subst hω
  rfl

-- Fixing coins keeps the one-query budget.
example (ω : ProbOracleComp.Coins coinThenQuery) :
    (ProbOracleComp.fixCoins coinThenQuery ω).IsQueryBounded 1 := by
  refine ProbOracleComp.isQueryBounded_fixCoins ?_ ω
  unfold coinThenQuery
  simpa using (ProbOracleComp.IsQueryBounded.sample _).bind fun c =>
    ProbOracleComp.IsQueryBounded.query (spec := fun _ : Fin 2 => Bool) (if c = 0 then 0 else 1)

end ComplexityTests.Crypto.PseudorandomPermutation
