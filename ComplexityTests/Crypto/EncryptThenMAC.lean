/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Encryption.EncryptThenMAC
import Complexity.Probability.BitString

/-!
# Tests for Encrypt-then-MAC and Randomized PRF-Based Encryption

Provides concrete instantiations of `prfCipher`, `encryptThenMAC`, and `prfEncryptThenMAC`,
verifies decryption completeness and tamper rejection on concrete inputs, and exercises the
composed runtime certificates (`IsPPT`, `IsOraclePPT`) and quantitative security bounds for
Boneh–Shoup Theorem 5.2 (`PRF ⇒ INDCPA` for `prfCipher`) and Theorem 9.2 (`Encrypt-then-MAC`) on
`echoPrfCipher`, `echoPrfMAC`, and `echoPrfEtM`.
-/

namespace ComplexityTests.Crypto.EncryptThenMAC

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete message-echo family `fun _ x => x`, used to exercise `prfCipher` and
`prfEncryptThenMAC` on concrete inputs. -/
def echoFamily (_ x : List Bool) : List Bool := x

theorem echoFamily_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => echoFamily p.1 p.2)
      (encPair encBits encBits) encBits := by
  dsimp [echoFamily]
  polytime

theorem echoFamily_length (key query : List Bool) (h : query.length = key.length) :
    (echoFamily key query).length = key.length :=
  h

/-- Concrete instantiation of the randomized `prfCipher` on `echoFamily`. -/
noncomputable def echoPrfCipher : SymmetricCipher :=
  prfCipher echoFamily echoFamily_polyTime echoFamily_length

/-- Concrete instantiation of `prfEncryptThenMAC` on `echoFamily`, combining `echoPrfCipher`
(`2 * n`-bit ciphertexts) with reindexed `prfMAC` (`msgLen n = 2 * n`). -/
noncomputable def echoPrfEtM : SymmetricCipher :=
  prfEncryptThenMAC echoFamily echoFamily_polyTime echoFamily_length

-- Valid `prfCipher` ciphertext `r ++ (r ⊕ m)` decrypts back to `m`.
example :
    echoPrfCipher.decrypt 2 [true, false] [true, false, false, true] =
      some [true, true] := by
  rfl

-- `prfCipher.encrypt` is genuinely randomized: two distinct ciphertexts of the same plaintext
-- `[true, true]` under the same key `[true, false]` both lie in the support of `encrypt`.
example :
    [false, false, true, true] ∈
        (ProbComp.eval (echoPrfCipher.encrypt 2 [true, false] [true, true])).support ∧
      [true, false, false, true] ∈
        (ProbComp.eval (echoPrfCipher.encrypt 2 [true, false] [true, true])).support ∧
      ([false, false, true, true] : List Bool) ≠ [true, false, false, true] := by
  simp only [echoPrfCipher, prfCipher, echoFamily, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff,
    BitString.eval_sampleList, BitString.mem_support_uniformList_iff]
  refine ⟨⟨[false, false], rfl, rfl⟩, ⟨[true, false], rfl, rfl⟩, by decide⟩

-- Wrong-length ciphertext is rejected by `prfCipher.decrypt`.
example :
    echoPrfCipher.decrypt 2 [true, false] [true, false, false] = none := by
  rfl

-- Valid `encryptThenMAC` ciphertext decrypts back to the original `n`-bit plaintext.
example :
    echoPrfEtM.decrypt 2
      (encPair encBits encBits ([true, false], [false, true, true, false]))
      (encPair encBits encBits
        ([true, false, false, true], [true, false, false, true])) =
    some [true, true] := by
  rfl

-- Tampering with the MAC tag causes `encryptThenMAC.decrypt` to reject with `none`.
example :
    echoPrfEtM.decrypt 2
      (encPair encBits encBits ([true, false], [false, true, true, false]))
      (encPair encBits encBits
        ([true, false, false, true], [true, false, false, false])) =
    none := by
  rfl

-- Non-canonical framing is rejected by `encryptThenMAC.decrypt`.
example :
    echoPrfEtM.decrypt 2
      (encPair encBits encBits ([true, false], [false, true, true, false]))
      [false, true] =
    none := by
  rfl

/-! ### Concrete Reduction Certificates and Quantitative Bounds on `echoPrfCipher` and `echoPrfEtM`
-/

/-- Concrete reindexed `prfMAC` on `echoFamily` authenticating `2 * n`-bit ciphertexts. -/
noncomputable def echoPrfMAC : MACScheme :=
  (prfMAC echoFamily echoFamily_polyTime).reindex (fun n => 2 * n) (by polytime)

/-- Zero-query CPA distinguisher that always outputs `false`. -/
def zeroCPAAdversary : OracleDistinguisher :=
  fun _ _ => ProbOracleComp.sample (pure false)

theorem isOraclePPT_zeroCPAAdversary : IsOraclePPT encBool zeroCPAAdversary := by
  have hbody : IsPPTOn (encPair encUnary encBits) encBool
      (fun _ : ℕ × List Bool => (pure false : ProbComp Bool)) :=
    (ComputableInPolyTime.const false).isPPTOn
  exact hbody.isOraclePPTOn.isOraclePPT

theorem isQueryBounded_zeroCPAAdversary (n : ℕ) :
    (zeroCPAAdversary n []).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample (pure false)

/-- Zero-query CI adversary that outputs `0^n`. -/
def zeroCIAdversary : CIAdversary :=
  fun n _ => ProbOracleComp.sample (pure (List.replicate n false))

theorem isOraclePPT_zeroCIAdversary : IsOraclePPT encBits zeroCIAdversary := by
  have hrep : ComputableInPolyTime
      (fun p : ℕ × List Bool => List.replicate p.1 false)
      (encPair encUnary encBits) encBits := by polytime
  exact hrep.isPPTOn.isOraclePPTOn.isOraclePPT

-- Composed closed-game `IsPPT` and Theorem 9.2 / Theorem 5.2 reduction `IsOraclePPT` certificates
-- on `echoPrfCipher` and `echoPrfMAC`.
example (bit : Bool) :
    IsPPT encBool
      (fun n _ =>
        echoPrfMAC.sufCmaGame
          (etmToMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary) n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfCipher.cpaGame (etmToCPAAdversary echoPrfMAC zeroCPAAdversary) bit n) ∧
    IsOraclePPT encBool
      (cpaToPrfDistinguisher (etmToCPAAdversary echoPrfMAC zeroCPAAdversary) bit) :=
  ⟨echoPrfMAC.isPPT_sufCmaGame
    (isOraclePPT_etmToMACForger echoPrfCipher echoPrfMAC (by polytime) isOraclePPT_zeroCIAdversary),
   echoPrfCipher.isPPT_cpaGame
    (isOraclePPT_etmToCPAAdversary echoPrfMAC isOraclePPT_zeroCPAAdversary) bit,
   isOraclePPT_cpaToPrfDistinguisher
    (isOraclePPT_etmToCPAAdversary echoPrfMAC isOraclePPT_zeroCPAAdversary) bit⟩

-- Quantitative Theorem 9.2 and Theorem 5.2 equations and bounds instantiated on `echoPrfCipher`,
-- `echoPrfMAC`, and `echoPrfEtM`.
example (n : ℕ) :
    Game.succProbability (ProbComp.eval (echoPrfEtM.ciGame zeroCIAdversary n)) =
      Game.succProbability
        (ProbComp.eval
          (echoPrfMAC.sufCmaGame
            (etmToMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary) n)) := by
  have htag (km : List Bool) (hkm : km ∈ (ProbComp.eval (echoPrfMAC.keyGen n)).support)
      (c : List Bool) (_hc : c.length = echoPrfMAC.msgLen n)
      (tag : List Bool) (htag : tag ∈ (ProbComp.eval (echoPrfMAC.sign km c)).support) :
      tag.length ≤ 2 * n := by
    change km ∈ (ProbComp.eval (BitString.sampleList (2 * n))).support at hkm
    rw [BitString.eval_sampleList, BitString.mem_support_uniformList_iff] at hkm
    change tag ∈ (ProbComp.eval (pure (prfOracle echoFamily km.length km c))).support at htag
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    unfold prfOracle
    split_ifs with hlen
    · exact (echoFamily_length km c hlen).le.trans hkm.le
    · simp
  exact succProbability_ciGame_encryptThenMAC_eq echoPrfCipher echoPrfMAC
    (prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length)
    (fun n => 2 * n) zeroCIAdversary n htag

example (n Q : ℕ) (cpaAdv : OracleDistinguisher)
    (hq : (etmToCPAAdversary echoPrfMAC cpaAdv n []).IsQueryBounded Q) :
    (Game.advantage
        (ProbComp.eval (echoPrfEtM.cpaGame cpaAdv false n))
        (ProbComp.eval (echoPrfEtM.cpaGame cpaAdv true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval
          (prfRealGame echoFamily
            (cpaToPrfDistinguisher (etmToCPAAdversary echoPrfMAC cpaAdv) false) n))
        (ProbComp.eval
          (prfIdealGame
            (cpaToPrfDistinguisher (etmToCPAAdversary echoPrfMAC cpaAdv) false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval
          (prfRealGame echoFamily
            (cpaToPrfDistinguisher (etmToCPAAdversary echoPrfMAC cpaAdv) true) n))
        (ProbComp.eval
          (prfIdealGame
            (cpaToPrfDistinguisher (etmToCPAAdversary echoPrfMAC cpaAdv) true) n)) : ℝ) +
      2 * (Q : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  have heq :
      Game.advantage
        (ProbComp.eval (echoPrfEtM.cpaGame cpaAdv false n))
        (ProbComp.eval (echoPrfEtM.cpaGame cpaAdv true n)) =
      Game.advantage
        (ProbComp.eval
          (echoPrfCipher.cpaGame (etmToCPAAdversary echoPrfMAC cpaAdv) false n))
        (ProbComp.eval
          (echoPrfCipher.cpaGame (etmToCPAAdversary echoPrfMAC cpaAdv) true n)) :=
    advantage_cpaGame_encryptThenMAC_eq echoPrfCipher echoPrfMAC
      (prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length)
      cpaAdv n
  rw [heq]
  exact advantage_cpaGame_prfCipher_le echoFamily echoFamily_polyTime echoFamily_length
    (etmToCPAAdversary echoPrfMAC cpaAdv) n Q hq

example (n : ℕ) :
    (Game.advantage
        (ProbComp.eval (echoPrfCipher.cpaGame zeroCPAAdversary false n))
        (ProbComp.eval (echoPrfCipher.cpaGame zeroCPAAdversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame echoFamily (cpaToPrfDistinguisher zeroCPAAdversary false) n))
        (ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher zeroCPAAdversary false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame echoFamily (cpaToPrfDistinguisher zeroCPAAdversary true) n))
        (ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher zeroCPAAdversary true) n)) : ℝ) := by
  have h := advantage_cpaGame_prfCipher_le echoFamily echoFamily_polyTime echoFamily_length
    zeroCPAAdversary n 0 (isQueryBounded_zeroCPAAdversary n)
  simpa [echoPrfCipher] using h

/-! ### One-Time Encrypt-then-MAC and Query-Count Preservation Certificates -/

theorem isQueryBounded_zeroCIAdversary (n : ℕ) :
    (zeroCIAdversary n []).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample (pure (List.replicate n false))

-- Composed closed-game `IsPPT` and query-bound preservation certificates for multi-query and
-- one-time Theorem 9.2 reductions on `echoPrfCipher` and `echoPrfMAC`.
example (bit : Bool) (n : ℕ) :
    IsPPT encBool
      (fun n _ =>
        echoPrfMAC.sufOneTimeGame
          (etmToOneTimeMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary) n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfCipher.cpaOneTimeGame
          (etmToOneTimeCPAAdversary echoPrfMAC zeroCPAAdversary) bit n) ∧
    (etmToMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary n []).IsQueryBounded
      0 ∧
    (etmToOneTimeMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary n
      []).IsQueryBounded 0 ∧
    (etmToCPAAdversary echoPrfMAC zeroCPAAdversary n []).IsQueryBounded 0 ∧
    (etmToOneTimeCPAAdversary echoPrfMAC zeroCPAAdversary n []).IsQueryBounded 0 :=
  ⟨echoPrfMAC.isPPT_sufOneTimeGame
    (isOraclePPT_etmToOneTimeMACForger echoPrfCipher echoPrfMAC (by polytime)
      isOraclePPT_zeroCIAdversary),
   echoPrfCipher.isPPT_cpaOneTimeGame
    (isOraclePPT_etmToOneTimeCPAAdversary echoPrfMAC isOraclePPT_zeroCPAAdversary) bit,
   isQueryBounded_etmToMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary n []
    (isQueryBounded_zeroCIAdversary n),
   isQueryBounded_etmToOneTimeMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary n
    [] (isQueryBounded_zeroCIAdversary n),
   isQueryBounded_etmToCPAAdversary echoPrfMAC zeroCPAAdversary n []
    (isQueryBounded_zeroCPAAdversary n),
   isQueryBounded_etmToOneTimeCPAAdversary echoPrfMAC zeroCPAAdversary n []
    (isQueryBounded_zeroCPAAdversary n)⟩

-- Quantitative one-time Theorem 9.2 equalities instantiated on `echoPrfCipher`, `echoPrfMAC`, and
-- `echoPrfEtM`.
example (n : ℕ) :
    Game.succProbability (ProbComp.eval (echoPrfEtM.ciOneTimeGame zeroCIAdversary n)) =
      Game.succProbability
        (ProbComp.eval
          (echoPrfMAC.sufOneTimeGame
            (etmToOneTimeMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary)
            n)) ∧
    Game.advantage
        (ProbComp.eval (echoPrfEtM.cpaOneTimeGame zeroCPAAdversary false n))
        (ProbComp.eval (echoPrfEtM.cpaOneTimeGame zeroCPAAdversary true n)) =
      Game.advantage
        (ProbComp.eval
          (echoPrfCipher.cpaOneTimeGame
            (etmToOneTimeCPAAdversary echoPrfMAC zeroCPAAdversary) false n))
        (ProbComp.eval
          (echoPrfCipher.cpaOneTimeGame
            (etmToOneTimeCPAAdversary echoPrfMAC zeroCPAAdversary) true n)) := by
  have htag (km : List Bool) (hkm : km ∈ (ProbComp.eval (echoPrfMAC.keyGen n)).support)
      (c : List Bool) (_hc : c.length = echoPrfMAC.msgLen n)
      (tag : List Bool) (htag : tag ∈ (ProbComp.eval (echoPrfMAC.sign km c)).support) :
      tag.length ≤ 2 * n := by
    change km ∈ (ProbComp.eval (BitString.sampleList (2 * n))).support at hkm
    rw [BitString.eval_sampleList, BitString.mem_support_uniformList_iff] at hkm
    change tag ∈ (ProbComp.eval (pure (prfOracle echoFamily km.length km c))).support at htag
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    unfold prfOracle
    split_ifs with hlen
    · exact (echoFamily_length km c hlen).le.trans hkm.le
    · simp
  exact ⟨succProbability_ciOneTimeGame_encryptThenMAC_eq echoPrfCipher echoPrfMAC
    (prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length)
    (fun n => 2 * n) zeroCIAdversary n htag,
   advantage_cpaOneTimeGame_encryptThenMAC_eq echoPrfCipher echoPrfMAC
    (prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length)
    zeroCPAAdversary n⟩

end ComplexityTests.Crypto.EncryptThenMAC
