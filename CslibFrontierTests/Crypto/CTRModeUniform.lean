/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.CTRMode.Uniform
import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for uniform counter mode

Checks for `CslibFrontier/Crypto/Computational/Encryption/CTRMode/Uniform.lean` and
`CslibFrontier/Crypto/Computational/Encryption/SymmetricCPA.lean`: concrete counter blocks and
keystreams, correctness for a toy family, the `n`-bit special case of the CPA notion, a certified
one-query adversary with its reduction certificate and a non-vacuous concrete bound, and the
asymptotic theorem's premises. The file is a `module` client with ordinary imports.
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

/-! ### A querying adversary -/

/-- A one-query adversary: it submits the pair of one-block messages `(0ⁿ, 1ⁿ)` and outputs whether
the ciphertext block after the initial value is `0ⁿ`. -/
public def oneBlockAdversary : OracleDistinguisher :=
  fun n _ =>
    (fun reply => reply.drop n == List.replicate n false) <$>
      (List.take (2 * n) <$> ProbOracleComp.query
        ((), encPair encBits encBits (List.replicate n false, List.replicate n true)))

/-- The one-query adversary is uniform strict oracle PPT. -/
public theorem isOraclePPT_oneBlockAdversary : IsOraclePPT encBool oneBlockAdversary := by
  have hrequest : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        encPair encBits encBits (List.replicate p.1 false, List.replicate p.1 true))
      (encPair encUnary encBits) encBits := by
    polytime
  have hlimit : ComputableInPolyTime (fun p : ℕ × List Bool => 2 * p.1)
      (encPair encUnary encBits) encUnary := by
    polytime
  have hout : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => p.2.drop p.1.1 == List.replicate p.1.1 false)
      (encPair (encPair encUnary encBits) encBits) encBool := by
    polytime
  unfold oneBlockAdversary
  exact ((IsOraclePPTOn.query_take' () hrequest hlimit).map_with' hout).isOraclePPT

/-- The adversary makes one request. -/
public theorem isQueryBounded_oneBlockAdversary (n : ℕ) :
    (oneBlockAdversary n []).IsQueryBounded 1 := by
  simp only [oneBlockAdversary, OracleComp.isCostBounded_map_iff]
  exact ProbOracleComp.IsQueryBounded.query _

/-- Its request has `3 n + 2` bits. -/
public theorem queriesSatisfy_oneBlockAdversary (n : ℕ) :
    (oneBlockAdversary n []).QueriesSatisfy fun request => request.2.length ≤ 3 * n + 2 := by
  simp only [oneBlockAdversary, OracleComp.queriesSatisfy_map_iff]
  exact ProbOracleComp.QueriesSatisfy.query (by simp; omega)

/-- The reduction built from the one-query adversary is uniform strict oracle PPT. -/
example : IsOraclePPT encBool (ctrToPrfDistinguisher oneBlockAdversary true) :=
  isOraclePPT_ctrToPrfDistinguisher isOraclePPT_oneBlockAdversary true

/-- At `n = 16`, the concrete bound for the one-query adversary (`Q = 1` request of `L = 50` bits)
has collision term `2 · 50² / 2¹⁶`. -/
example {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ctrWordEncrypt family) oneBlockAdversary false 16))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ctrWordEncrypt family) oneBlockAdversary true 16)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ctrToPrfDistinguisher oneBlockAdversary false) 16))
        (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher oneBlockAdversary false) 16)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ctrToPrfDistinguisher oneBlockAdversary true) 16))
        (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher oneBlockAdversary true) 16)) : ℝ) +
      2 * (((1 : ℕ) : ℝ) * ((50 : ℕ) : ℝ)) ^ 2 / 2 ^ 16 :=
  advantage_ctrWordCPAGame_le hlen oneBlockAdversary (isQueryBounded_oneBlockAdversary 16)
    (queriesSatisfy_oneBlockAdversary 16) (by norm_num)

/-- That collision term is below `1`, so the bound is not vacuous. -/
example : 2 * (((1 : ℕ) : ℝ) * ((50 : ℕ) : ℝ)) ^ 2 / 2 ^ 16 < 1 := by norm_num

/-! ### The asymptotic theorem -/

/-- Counter mode is CPA-secure for every pseudorandom function; the only premise is the PRF
assumption. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList (ctrWordEncrypt family) :=
  hprf.indcpa_ctrWordEncrypt

end CslibFrontierTests.Crypto.CTRModeUniform
