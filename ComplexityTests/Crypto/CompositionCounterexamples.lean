/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Computational.Encryption.CompositionCounterexamples
import Complexity.Probability.BitString

/-!
# Tests for Fresh-Message Encryption Unforgeability and AE Composition Counterexamples

Exercises the definitions, concrete evaluations, runtime certificates (`IsPPT`, `IsOraclePPT`),
quantitative game bounds, and generic composition counterexamples from
`Complexity.Crypto.Computational.Encryption.CompositionCounterexamples` on concrete PRF-based
schemes (`echoPrfCipher`, `echoPrfMAC`, `echoPrfEtM`, `echoPrfEtM.tailFallback`, and
`echoPrfEtMRedundant`).
-/

namespace ComplexityTests.Crypto.CompositionCounterexamples

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete message-echo family `fun _ x => x`, used to exercise `prfCipher`, `prfMAC`,
`prfEncryptThenMAC`, `tailFallback`, and `prfEncryptThenMACRedundantTag` on concrete inputs. -/
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

/-- Concrete reindexed `prfMAC` on `echoFamily` authenticating `2 * n`-bit ciphertexts. -/
noncomputable def echoPrfMAC : MACScheme :=
  (prfMAC echoFamily echoFamily_polyTime).reindex (fun n => 2 * n) (by polytime)

/-- Concrete instantiation of `prfEncryptThenMAC` on `echoFamily`. -/
noncomputable def echoPrfEtM : SymmetricCipher :=
  prfEncryptThenMAC echoFamily echoFamily_polyTime echoFamily_length

/-- Concrete instantiation of `prfEncryptThenMACRedundantTag` on `echoFamily`. -/
noncomputable def echoPrfEtMRedundant : SymmetricCipher :=
  prfEncryptThenMACRedundantTag echoFamily echoFamily_polyTime echoFamily_length

/-- Zero-query CI adversary that outputs `0^n`. -/
def zeroCIAdversary : CIAdversary :=
  fun n _ => ProbOracleComp.sample (pure (List.replicate n false))

theorem isOraclePPT_zeroCIAdversary : IsOraclePPT encBits zeroCIAdversary := by
  have hrep : ComputableInPolyTime
      (fun p : ℕ × List Bool => List.replicate p.1 false)
      (encPair encUnary encBits) encBits := by polytime
  exact hrep.isPPTOn.isOraclePPTOn.isOraclePPT

theorem isQueryBounded_zeroCIAdversary (n : ℕ) :
    (zeroCIAdversary n []).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample (pure (List.replicate n false))

/-! ### Concrete Evaluation of `tailFallback`, `redundantTag`, and `prfEncryptThenMACRedundantTag`
-/

-- Both an honest `echoPrfEtM` ciphertext `ct` and its prepended-`false` maul `false :: ct`
-- decrypt to the same plaintext under `echoPrfEtM.tailFallback`.
example :
    echoPrfEtM.tailFallback.decrypt 2
      (encPair encBits encBits ([true, false], [false, true, true, false]))
      (encPair encBits encBits
        ([true, false, false, true], [true, false, false, true])) =
      some [true, true] ∧
    echoPrfEtM.tailFallback.decrypt 2
      (encPair encBits encBits ([true, false], [false, true, true, false]))
      (false :: encPair encBits encBits
        ([true, false, false, true], [true, false, false, true])) =
      some [true, true] := by
  exact ⟨rfl, rfl⟩

-- `echoPrfMAC.redundantTag.verify` accepts both the honest tag and `false :: tag`, while
-- rejecting a tag whose direct and tail verifications both fail.
example :
    echoPrfMAC.redundantTag.verify
      [false, true, true, false]
      [true, false, false, true]
      [true, false, false, true] = true ∧
    echoPrfMAC.redundantTag.verify
      [false, true, true, false]
      [true, false, false, true]
      [false, true, false, false, true] = true ∧
    echoPrfMAC.redundantTag.verify
      [false, true, true, false]
      [true, false, false, true]
      [false, false, false, true] = false := by
  exact ⟨rfl, rfl, rfl⟩

-- `echoPrfEtMRedundant.decrypt` accepts both the honest ciphertext `encPair (c, tag)` and its
-- tag-prepended maul `encPair (c, false :: tag)`.
example :
    echoPrfEtMRedundant.decrypt 2
      (encPair encBits encBits ([true, false], [false, true, true, false]))
      (encPair encBits encBits
        ([true, false, false, true], [true, false, false, true])) =
      some [true, true] ∧
    echoPrfEtMRedundant.decrypt 2
      (encPair encBits encBits ([true, false], [false, true, true, false]))
      (encPair encBits encBits
        ([true, false, false, true], [false, true, false, false, true])) =
      some [true, true] := by
  exact ⟨rfl, rfl⟩

/-! ### Composed `IsPPT` and `IsOraclePPT` Certificates -/

example (bit : Bool) (n : ℕ) :
    IsPPT encBool (fun n _ => echoPrfEtM.encForgeGame zeroCIAdversary n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfEtM.encForgeGame (SymmetricCipher.tailCIAdversary zeroCIAdversary) n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfEtM.tailFallback.ciOneTimeGame
          (SymmetricCipher.prependFalseBitCIAdversary false (fun m => 6 * m + 2)) n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfEtM.tailFallback.ccaOneTimeGame
          (SymmetricCipher.tailFallbackCCAAdversary (fun m => 6 * m + 2)) bit n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfMAC.redundantTag.sufOneTimeGame
          (echoPrfMAC.redundantTagForger (fun m => 2 * m)) n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfEtMRedundant.ciOneTimeGame
          (etmRedundantCIAdversary (fun m => 6 * m + 2)) n) ∧
    IsPPT encBool
      (fun n _ =>
        echoPrfEtMRedundant.ccaOneTimeGame
          (etmRedundantCCAAdversary (fun m => 6 * m + 2)) bit n) ∧
    (SymmetricCipher.tailCIAdversary zeroCIAdversary n []).IsQueryBounded 0 :=
  ⟨echoPrfEtM.isPPT_encForgeGame isOraclePPT_zeroCIAdversary,
   echoPrfEtM.isPPT_encForgeGame
    (SymmetricCipher.isOraclePPT_tailCIAdversary isOraclePPT_zeroCIAdversary),
   echoPrfEtM.tailFallback.isPPT_ciOneTimeGame
    (SymmetricCipher.isOraclePPT_prependFalseBitCIAdversary false (by polytime)),
   echoPrfEtM.tailFallback.isPPT_ccaOneTimeGame
    (SymmetricCipher.isOraclePPT_tailFallbackCCAAdversary (by polytime)) bit,
   echoPrfMAC.redundantTag.isPPT_sufOneTimeGame
    (echoPrfMAC.isOraclePPT_redundantTagForger (by polytime)),
   echoPrfEtMRedundant.isPPT_ciOneTimeGame
    (isOraclePPT_etmRedundantCIAdversary (by polytime)),
   echoPrfEtMRedundant.isPPT_ccaOneTimeGame
    (isOraclePPT_etmRedundantCCAAdversary (by polytime)) bit,
   SymmetricCipher.isQueryBounded_tailCIAdversary zeroCIAdversary n []
    (isQueryBounded_zeroCIAdversary n)⟩

/-! ### Quantitative `encForgeGame` and `eufCmaGame` Bounds -/

example (n : ℕ) (forger : Forger) :
    Game.succProbability (ProbComp.eval (echoPrfEtM.encForgeGame zeroCIAdversary n)) ≤
      Game.succProbability (ProbComp.eval (echoPrfEtM.ciGame zeroCIAdversary n)) ∧
    Game.succProbability (ProbComp.eval (echoPrfEtM.encForgeGame zeroCIAdversary n)) ≤
      Game.succProbability
        (ProbComp.eval
          (echoPrfMAC.eufCmaGame
            (etmToMACForger echoPrfCipher echoPrfMAC (fun n => 2 * n) zeroCIAdversary) n)) ∧
    Game.succProbability
        (ProbComp.eval (echoPrfEtM.tailFallback.encForgeGame zeroCIAdversary n)) ≤
      Game.succProbability (ProbComp.eval (echoPrfEtM.encForgeGame zeroCIAdversary n)) +
        Game.succProbability
          (ProbComp.eval
            (echoPrfEtM.encForgeGame (SymmetricCipher.tailCIAdversary zeroCIAdversary) n)) ∧
    Game.succProbability (ProbComp.eval (echoPrfMAC.redundantTag.eufCmaGame forger n)) ≤
      Game.succProbability (ProbComp.eval (echoPrfMAC.eufCmaGame forger n)) +
        Game.succProbability
          (ProbComp.eval (echoPrfMAC.eufCmaGame (MACScheme.tailTagForger forger) n)) := by
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
  exact ⟨echoPrfEtM.succProbability_encForgeGame_le_ciGame zeroCIAdversary n,
    succProbability_encForgeGame_encryptThenMAC_le echoPrfCipher echoPrfMAC
      (prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length)
      (fun n => 2 * n) zeroCIAdversary n htag,
    echoPrfEtM.succProbability_encForgeGame_tailFallback_le zeroCIAdversary n,
    echoPrfMAC.succProbability_eufCmaGame_redundantTag_le forger n⟩

/-! ### Concrete Attack Evaluations and Insecurity of `echoPrfEtM.tailFallback` (KL Ex. 5.10) -/

example (n : ℕ) :
    ProbComp.eval
      (echoPrfEtM.tailFallback.ciOneTimeGame
        (SymmetricCipher.prependFalseBitCIAdversary false (fun m => 6 * m + 2)) n) =
        PMF.pure true ∧
    ProbComp.eval
      (echoPrfEtM.tailFallback.ciGame
        (SymmetricCipher.prependFalseBitCIAdversary false (fun m => 6 * m + 2)) n) =
        PMF.pure true ∧
    ¬ echoPrfEtM.tailFallback.OneTimeCiphertextIntegrity ∧
    ¬ echoPrfEtM.tailFallback.CiphertextIntegrity ∧
    ¬ echoPrfEtM.tailFallback.OneTimeAuthenticatedEncryption ∧
    ¬ echoPrfEtM.tailFallback.AuthenticatedEncryption := by
  have hctLen : ∀ m ke, ke ∈ (ProbComp.eval (echoPrfCipher.keyGen m)).support →
      ∀ msg, msg.length = m →
      ∀ c ∈ (ProbComp.eval (echoPrfCipher.encrypt m ke msg)).support,
        c.length = echoPrfMAC.msgLen m :=
    prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length
  have hct (k : List Bool) (hk : k ∈ (ProbComp.eval (echoPrfEtM.keyGen n)).support)
      (m : List Bool) (hm : m.length = n)
      (ct : List Bool) (hct : ct ∈ (ProbComp.eval (echoPrfEtM.encrypt n k m)).support) :
      ct.length ≤ 6 * n + 2 := by
    change k ∈ (ProbComp.eval
      ((encryptThenMAC echoPrfCipher echoPrfMAC hctLen).keyGen n)).support at hk
    simp only [encryptThenMAC, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
    change ct ∈ (ProbComp.eval ((encryptThenMAC echoPrfCipher echoPrfMAC hctLen).encrypt n
      (encPair encBits encBits (ke, km)) m)).support at hct
    simp only [encryptThenMAC, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
    obtain ⟨c, hc, tag, htag, rfl⟩ := hct
    have hunfK : unframe (encPair encBits encBits (ke, km)) = ke := by
      simp [encPair_apply, unframe_frame_append]
    have hdropK : dropFrame (encPair encBits encBits (ke, km)) = km := by
      simp [encPair_apply, dropFrame_frame_append]
    rw [hunfK] at hc
    rw [hdropK] at htag
    have hcLen : c.length = 2 * n :=
      prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length n ke hke m hm
        c hc
    change km ∈ (ProbComp.eval (BitString.sampleList (2 * n))).support at hkm
    rw [BitString.eval_sampleList, BitString.mem_support_uniformList_iff] at hkm
    change tag ∈ (ProbComp.eval (pure (prfOracle echoFamily km.length km c))).support at htag
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    have htagLen : (prfOracle echoFamily km.length km c).length ≤ 2 * n := by
      unfold prfOracle
      split_ifs with hlen
      · exact (echoFamily_length km c hlen).le.trans hkm.le
      · simp
    simp only [length_encPair, encBits_apply, hcLen]
    omega
  exact ⟨echoPrfEtM.eval_ciOneTimeGame_tailFallback_prependFalseBitCIAdversary
      false (fun m => 6 * m + 2) n hct,
    echoPrfEtM.eval_ciGame_tailFallback_prependFalseBitCIAdversary
      false (fun m => 6 * m + 2) n hct,
    echoPrfEtM.not_oneTimeCiphertextIntegrity_tailFallback,
    echoPrfEtM.not_ciphertextIntegrity_tailFallback,
    echoPrfEtM.not_oneTimeAuthenticatedEncryption_tailFallback,
    echoPrfEtM.not_authenticatedEncryption_tailFallback⟩

/-! ### Concrete Attack Evaluations and Insecurity of `echoPrfMAC.redundantTag` and
`echoPrfEtMRedundant` (KL Ex. 5.4) -/

example (n : ℕ) :
    ProbComp.eval
      (echoPrfMAC.redundantTag.sufOneTimeGame
        (echoPrfMAC.redundantTagForger (fun m => 2 * m)) n) = PMF.pure true ∧
    ProbComp.eval
      (echoPrfMAC.redundantTag.sufCmaGame
        (echoPrfMAC.redundantTagForger (fun m => 2 * m)) n) = PMF.pure true ∧
    ProbComp.eval
      (echoPrfEtMRedundant.ciOneTimeGame
        (etmRedundantCIAdversary (fun m => 6 * m + 2)) n) = PMF.pure true ∧
    ProbComp.eval
      (echoPrfEtMRedundant.ciGame
        (etmRedundantCIAdversary (fun m => 6 * m + 2)) n) = PMF.pure true ∧
    ¬ echoPrfMAC.redundantTag.OneTimeSUFCMA ∧
    ¬ echoPrfMAC.redundantTag.SUFCMA ∧
    ¬ echoPrfEtMRedundant.OneTimeCiphertextIntegrity ∧
    ¬ echoPrfEtMRedundant.CiphertextIntegrity ∧
    ¬ echoPrfEtMRedundant.OneTimeAuthenticatedEncryption ∧
    ¬ echoPrfEtMRedundant.AuthenticatedEncryption ∧
    ¬ echoPrfEtMRedundant.OneTimeINDCCA ∧
    ¬ echoPrfEtMRedundant.INDCCA := by
  have htag_le (km : List Bool) (hkm : km ∈ (ProbComp.eval (echoPrfMAC.keyGen n)).support)
      (m : List Bool) (_hm : m.length = echoPrfMAC.msgLen n)
      (tag : List Bool) (htag : tag ∈ (ProbComp.eval (echoPrfMAC.sign km m)).support) :
      tag.length ≤ 2 * n := by
    change km ∈ (ProbComp.eval (BitString.sampleList (2 * n))).support at hkm
    rw [BitString.eval_sampleList, BitString.mem_support_uniformList_iff] at hkm
    change tag ∈ (ProbComp.eval (pure (prfOracle echoFamily km.length km m))).support at htag
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    unfold prfOracle
    split_ifs with hlen
    · exact (echoFamily_length km m hlen).le.trans hkm.le
    · simp
  have hctLen : ∀ m ke, ke ∈ (ProbComp.eval (echoPrfCipher.keyGen m)).support →
      ∀ msg, msg.length = m →
      ∀ c ∈ (ProbComp.eval (echoPrfCipher.encrypt m ke msg)).support,
        c.length = echoPrfMAC.msgLen m :=
    prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length
  have hctBound (k : List Bool) (hk : k ∈ (ProbComp.eval (echoPrfEtMRedundant.keyGen n)).support)
      (m : List Bool) (hm : m.length = n)
      (ct : List Bool) (hct : ct ∈ (ProbComp.eval (echoPrfEtMRedundant.encrypt n k m)).support) :
      ct.length ≤ 6 * n + 2 := by
    change k ∈ (ProbComp.eval
      ((encryptThenMAC echoPrfCipher echoPrfMAC.redundantTag hctLen).keyGen n)).support at hk
    simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
    change ct ∈ (ProbComp.eval
      ((encryptThenMAC echoPrfCipher echoPrfMAC.redundantTag hctLen).encrypt n
        (encPair encBits encBits (ke, km)) m)).support at hct
    simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
    obtain ⟨c, hc, tag, htag, rfl⟩ := hct
    have hunfK : unframe (encPair encBits encBits (ke, km)) = ke := by
      simp [encPair_apply, unframe_frame_append]
    have hdropK : dropFrame (encPair encBits encBits (ke, km)) = km := by
      simp [encPair_apply, dropFrame_frame_append]
    rw [hunfK] at hc
    rw [hdropK] at htag
    have hcLen : c.length = 2 * n := hctLen n ke hke m hm c hc
    have htagLen : tag.length ≤ 2 * n := htag_le km hkm c hcLen tag htag
    simp only [length_encPair, encBits_apply, hcLen]
    omega
  exact ⟨echoPrfMAC.eval_sufOneTimeGame_redundantTag_redundantTagForger (fun m => 2 * m) n htag_le,
    echoPrfMAC.eval_sufCmaGame_redundantTag_redundantTagForger (fun m => 2 * m) n htag_le,
    eval_ciOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCIAdversary
      echoPrfCipher echoPrfMAC hctLen (fun m => 6 * m + 2) n hctBound,
    eval_ciGame_encryptThenMAC_redundantTag_etmRedundantCIAdversary
      echoPrfCipher echoPrfMAC hctLen (fun m => 6 * m + 2) n hctBound,
    echoPrfMAC.not_oneTimeSUFCMA_redundantTag,
    echoPrfMAC.not_sufCma_redundantTag,
    not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag echoPrfCipher echoPrfMAC hctLen,
    not_ciphertextIntegrity_encryptThenMAC_redundantTag echoPrfCipher echoPrfMAC hctLen,
    not_oneTimeAuthenticatedEncryption_encryptThenMAC_redundantTag echoPrfCipher echoPrfMAC hctLen,
    not_authenticatedEncryption_encryptThenMAC_redundantTag echoPrfCipher echoPrfMAC hctLen,
    not_oneTimeINDCCA_encryptThenMAC_redundantTag echoPrfCipher echoPrfMAC hctLen,
    not_indcca_encryptThenMAC_redundantTag echoPrfCipher echoPrfMAC hctLen⟩

end ComplexityTests.Crypto.CompositionCounterexamples
