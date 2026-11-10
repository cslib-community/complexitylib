/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.Encryption.HalfBlockPRP
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for real/ideal authenticated encryption and half-block encryption

The ideal oracle rejects every decryption query, and the real oracle rejects only ciphertexts it
returned earlier. The identity cipher on `2 n`-bit blocks satisfies every law of `BlockCipher`; its
half-block scheme drops the nonce from every word of length `2 n` and rejects all other words, so
the all-ones forger always wins and the scheme is not authenticated encryption.
-/

namespace CslibFrontierTests.Crypto.RealIdealAEAndHalfBlock

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-! ### The real and ideal oracles -/

-- The ideal oracle rejects every decryption query, and encryption queries of the wrong length.
example (E : SymmetricCipher) (n : ℕ) (k ct : List Bool) :
    ProbComp.eval ((E.aeIdealOracle n k (true, ct)).run ()) = PMF.pure ([], ()) := by
  simp [SymmetricCipher.aeIdealOracle, StateT.run]
example (E : SymmetricCipher) (k : List Bool) :
    ProbComp.eval ((E.aeIdealOracle 2 k (false, [true])).run ()) = PMF.pure ([], ()) := by
  simp [SymmetricCipher.aeIdealOracle, StateT.run]

-- The real oracle answers a decryption query on a returned ciphertext with `[]`, and decrypts
-- a fresh one.
example (E : SymmetricCipher) (n : ℕ) (k ct : List Bool) :
    ProbComp.eval (E.aeRealOracle n k (true, ct) [ct]) = PMF.pure ([], [ct]) := by
  simp [SymmetricCipher.aeRealOracle]
example (E : SymmetricCipher) (n : ℕ) (k ct : List Bool) :
    ProbComp.eval (E.aeRealOracle n k (true, ct) []) =
      PMF.pure (encOption encBits (E.decrypt n k ct), []) := by
  simp [SymmetricCipher.aeRealOracle]

/-! ### Half-block encryption over the identity cipher -/

/-- The identity block cipher on `2 n`-bit blocks with `n`-bit keys. It is a permutation for every
key but is not pseudorandom. -/
def idCipher : BlockCipher where
  keyLen := id
  blockLen n := 2 * n
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
    ComputableInPolyTime.id'
  encrypt _ _ block := block
  decrypt _ _ block := block
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ _ hblock := hblock
  length_decrypt _ _ _ _ hblock := hblock
  decrypt_encrypt _ _ _ _ _ := rfl
  encrypt_decrypt _ _ _ _ _ := rfl

theorem blockLen_idCipher (n : ℕ) : idCipher.blockLen n = 2 * n := rfl

/-- The half-block scheme over the identity cipher. -/
noncomputable abbrev scheme : SymmetricCipher := idCipher.halfBlockCipher blockLen_idCipher

-- Decryption drops the nonce from a word of length `2 n` and rejects every other length.
example : scheme.decrypt 1 [] [true, false] = some [false] := rfl
example : scheme.decrypt 2 [true, true] [true, false, true, true] = some [true, true] := rfl
example : scheme.decrypt 1 [] [true] = none := rfl

-- The all-ones forger wins the CI game, so the scheme is not authenticated encryption in either
-- sense.
example (n : ℕ) : ProbComp.eval (scheme.ciGame idCipher.allOnesForger n) = PMF.pure true :=
  idCipher.eval_ciGame_halfBlockCipher_allOnesForger blockLen_idCipher n
example : ¬ scheme.AuthenticatedEncryption :=
  idCipher.not_authenticatedEncryption_halfBlockCipher blockLen_idCipher
example : ¬ scheme.RealIdealAE := idCipher.not_realIdealAE_halfBlockCipher blockLen_idCipher

end CslibFrontierTests.Crypto.RealIdealAEAndHalfBlock
