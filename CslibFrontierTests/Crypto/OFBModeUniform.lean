/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Crypto.Computational.Encryption.OFBMode.Uniform

/-!
# Tests for uniform OFB mode

Checks for `CslibFrontier/Crypto/Computational/Encryption/OFBMode/Uniform.lean`: a concrete
keystream and correctness for a toy family, the concrete bound for a query-free adversary, and the
asymptotic theorem's premises.
-/

namespace CslibFrontierTests.Crypto.OFBModeUniform

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-- A toy keyed family: XOR of key and input (not pseudorandom). -/
def xorFamily (key query : List Bool) : List Bool := List.zipWith xor key query

theorem xorFamily_length (key query : List Bool) (h : query.length = key.length) :
    (xorFamily key query).length = key.length := by
  simp [xorFamily, h]

/-- The chain from `[false, false]` under key `[true, false]` alternates between
`[true, false]` and `[false, false]`. -/
example : ofbWordKeystream xorFamily 2 [true, false] [false, false] 3 =
    [true, false, false, false, true, false] := by
  decide

/-- Decryption inverts encryption on whole-block messages. -/
example {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (ofbWordEncrypt xorFamily 2 [true, false]
      [true, true, false, true])).support) :
    ofbWordDecrypt xorFamily 2 [true, false] ct = some [true, true, false, true] :=
  ofbWordDecrypt_ofbWordEncrypt (n := 2) (k := [true, false]) xorFamily_length rfl (by decide) hct

/-- A query-free adversary: the concrete bound holds with `Q = L = 0`. -/
example {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (n : ℕ) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ofbWordEncrypt family) (fun _ _ => pure true) false n))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ofbWordEncrypt family) (fun _ _ => pure true) true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ofbToPrfDistinguisher (fun _ _ => pure true) false) n))
        (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher (fun _ _ => pure true) false) n)) :
          ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ofbToPrfDistinguisher (fun _ _ => pure true) true) n))
        (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher (fun _ _ => pure true) true) n)) :
          ℝ) +
      2 * (((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ)) * (((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)) /
        2 ^ n :=
  advantage_ofbWordCPAGame_le hlen _ (OracleComp.IsCostBounded.pure _ 0)
    (OracleComp.QueriesSatisfy.pure _)

/-- The reduction is certified for every certified adversary. -/
example {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (ofbToPrfDistinguisher adversary false) :=
  isOraclePPT_ofbToPrfDistinguisher hadversary false

/-- OFB mode is CPA-secure for every pseudorandom function; the only premise is the PRF
assumption. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList (ofbWordEncrypt family) :=
  hprf.indcpa_ofbWordEncrypt

end CslibFrontierTests.Crypto.OFBModeUniform
