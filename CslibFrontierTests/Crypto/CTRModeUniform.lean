/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.CTRMode.Uniform
import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC

/-!
# Tests for uniform counter mode

Checks for `CslibFrontier/Crypto/Computational/Encryption/CTRMode/Uniform.lean` and
`CslibFrontier/Crypto/Computational/Encryption/SymmetricCPA.lean`: concrete counter blocks and
keystreams, correctness for a toy family, the `n`-bit special case of the CPA notion, the concrete
bound for a query-free adversary, and the asymptotic theorem's premises. The file is a `module`
client with ordinary imports.
-/

namespace CslibFrontierTests.Crypto.CTRModeUniform

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-! ### Counter blocks -/

/-- The counter adds to the initial value least significant bit first. -/
example : ctrWordCounter 4 [true, false, false, false] 1 = [false, true, false, false] := by
  decide

/-- The counter wraps modulo `2 ^ n`. -/
example : ctrWordCounter 2 [true, true] 1 = [false, false] := by decide

/-- Admissible pairs have equal length and whole blocks. -/
example : blockPairValid 2 [true, false, true, true] [false, false, false, false] = true ∧
    blockPairValid 2 [true, false, true] [false, false, false] = false ∧
    blockPairValid 2 [true, false] [false, false, false, false] = false := by
  decide

/-! ### A toy family -/

/-- A toy keyed family: XOR of key and input (not pseudorandom). -/
public def xorFamily (key query : List Bool) : List Bool := List.zipWith xor key query

public theorem xorFamily_length (key query : List Bool) (h : query.length = key.length) :
    (xorFamily key query).length = key.length := by
  simp [xorFamily, h]

/-- The keystream of two 2-bit blocks under key `[true, false]` from initial value `[false, false]`
is `[true, false] ++ [false, false]`. -/
example : ctrWordKeystream xorFamily 2 [true, false] [false, false] 2 =
    [true, false, false, false] := by
  decide

/-- Decryption inverts encryption on whole-block messages. -/
example {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (ctrWordEncrypt xorFamily 2 [true, false]
      [true, true, false, true])).support) :
    ctrWordDecrypt xorFamily 2 [true, false] ct = some [true, true, false, true] :=
  ctrWordDecrypt_ctrWordEncrypt (n := 2) (k := [true, false]) xorFamily_length rfl (by decide) hct

/-! ### The notion -/

/-- `SymmetricCipher.INDCPA` of `prfCipher` is `SymmetricINDCPAOn` on `n`-bit pairs. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn (fun n m₀ m₁ => (m₀.length == n) && (m₁.length == n))
      (prfCipher family hprf.polyTime hprf.length_eq).keyGen
      (prfCipher family hprf.polyTime hprf.length_eq).encrypt :=
  (SymmetricCipher.indcpa_iff _).mp hprf.indcpa_prfCipher

/-! ### Bounds and the asymptotic theorem -/

/-- A query-free adversary: the concrete bound holds with `Q = L = 0`. -/
example {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (n : ℕ) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ctrWordEncrypt family) (fun _ _ => pure true) false n))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ctrWordEncrypt family) (fun _ _ => pure true) true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ctrToPrfDistinguisher (fun _ _ => pure true) false) n))
        (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher (fun _ _ => pure true) false) n)) :
          ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ctrToPrfDistinguisher (fun _ _ => pure true) true) n))
        (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher (fun _ _ => pure true) true) n)) :
          ℝ) +
      2 * ((0 : ℕ) * ((0 : ℕ) : ℝ)) ^ 2 / 2 ^ n :=
  advantage_ctrWordCPAGame_le hlen _ (OracleComp.IsCostBounded.pure _ 0)
    (OracleComp.QueriesSatisfy.pure _) (Nat.zero_le _)

/-- The reduction is certified for every certified adversary. -/
example {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (ctrToPrfDistinguisher adversary true) :=
  isOraclePPT_ctrToPrfDistinguisher hadversary true

/-- Counter mode is CPA-secure for every pseudorandom function; the only premise is the PRF
assumption. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList (ctrWordEncrypt family) :=
  hprf.indcpa_ctrWordEncrypt

end CslibFrontierTests.Crypto.CTRModeUniform
