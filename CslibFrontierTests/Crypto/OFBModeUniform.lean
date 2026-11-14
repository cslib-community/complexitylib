/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.OFBMode.Uniform
import CslibFrontierTests.Crypto.CTRModeUniform

/-!
# Tests for uniform OFB mode

Checks for `CslibFrontier/Crypto/Computational/Encryption/OFBMode/Uniform.lean`: a concrete
keystream and correctness for a toy family, the reduction certificate and a non-vacuous concrete
bound for a certified one-query adversary, and the asymptotic theorem's premises. The toy family
`xorFamily` and the adversary `oneBlockAdversary` with its certificates come from the counter-mode
tests. The file is a `module` client with ordinary imports.
-/

namespace CslibFrontierTests.Crypto.OFBModeUniform

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open CslibFrontierTests.Crypto.CTRModeUniform

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

/-! ### A querying adversary -/

/-- The reduction built from the one-query adversary is uniform strict oracle PPT. -/
example : IsOraclePPT encBool (ofbToPrfDistinguisher oneBlockAdversary false) :=
  isOraclePPT_ofbToPrfDistinguisher isOraclePPT_oneBlockAdversary false

/-- At `n = 16`, the concrete bound for the one-query adversary (`Q = 1` request of `L = 50` bits)
has collision term `2 · 50 · (50 + 50) / 2¹⁶`. -/
example {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ofbWordEncrypt family) oneBlockAdversary false 16))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ofbWordEncrypt family) oneBlockAdversary true 16)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ofbToPrfDistinguisher oneBlockAdversary false) 16))
        (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher oneBlockAdversary false) 16)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ofbToPrfDistinguisher oneBlockAdversary true) 16))
        (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher oneBlockAdversary true) 16)) : ℝ) +
      2 * (((1 : ℕ) : ℝ) * ((50 : ℕ) : ℝ)) *
        (((1 : ℕ) : ℝ) * ((50 : ℕ) : ℝ) + ((50 : ℕ) : ℝ)) / 2 ^ 16 :=
  advantage_ofbWordCPAGame_le hlen oneBlockAdversary (isQueryBounded_oneBlockAdversary 16)
    (queriesSatisfy_oneBlockAdversary 16)

/-- That collision term is below `1`, so the bound is not vacuous. -/
example : 2 * (((1 : ℕ) : ℝ) * ((50 : ℕ) : ℝ)) *
    (((1 : ℕ) : ℝ) * ((50 : ℕ) : ℝ) + ((50 : ℕ) : ℝ)) / 2 ^ 16 < 1 := by
  norm_num

/-! ### The asymptotic theorem -/

/-- OFB mode is CPA-secure for every pseudorandom function; the only premise is the PRF
assumption. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList (ofbWordEncrypt family) :=
  hprf.indcpa_ofbWordEncrypt

end CslibFrontierTests.Crypto.OFBModeUniform
