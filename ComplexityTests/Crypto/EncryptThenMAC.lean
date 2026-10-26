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
runtime certificates (`IsOraclePPT`), quantitative bounds, and asymptotic security theorems for
Boneh–Shoup Theorem 5.2 (`PRF ⇒ INDCPA` for `prfCipher`) and Theorem 9.2 (`Encrypt-then-MAC`).
-/

namespace ComplexityTests.Crypto.EncryptThenMAC

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete message-echo family `fun _ x => x`, used to exercise `prfCipher` and
`prfEncryptThenMAC` on concrete inputs. -/
def echoFamily (_ x : List Bool) : List Bool := x

theorem echoFamily_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => echoFamily p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy (ComputableTidilyInPolyTime.snd _ _)

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

/-! ### API, Certificate, and Non-Vacuity Smoke Checks -/

section CertificatesAndReductions

variable (E : SymmetricCipher) (M : MACScheme)
  (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
    ∀ msg, msg.length = n →
    ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
  {tagBound : ℕ → ℕ} (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
  {cpaAdv : OracleDistinguisher} (hcpaAdv : IsOraclePPT encBool cpaAdv)
  {ciAdv : CIAdversary} (hciAdv : IsOraclePPT encBits ciAdv)
  (family : List Bool → List Bool → List Bool)
  (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
    (encPair encBits encBits) encBits)
  (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
  (hprf : PseudorandomFunction family)

-- Theorem 9.2 and Theorem 5.2 reduction `IsOraclePPT` certificates.
example : IsOraclePPT (encPair encBits encBits) (etmToMACForger E M tagBound ciAdv) :=
  isOraclePPT_etmToMACForger E M htagBound hciAdv

example : IsOraclePPT encBool (etmToCPAAdversary M cpaAdv) :=
  isOraclePPT_etmToCPAAdversary M hcpaAdv

example (bit : Bool) : IsOraclePPT encBool (cpaToPrfDistinguisher cpaAdv bit) :=
  isOraclePPT_cpaToPrfDistinguisher hcpaAdv bit

-- Quantitative security equations and bounds (Theorem 9.2 and Theorem 5.2).
example (n : ℕ)
    (htagBoundN : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    Game.succProbability (ProbComp.eval ((encryptThenMAC E M hctLen).ciGame ciAdv n)) =
      Game.succProbability
        (ProbComp.eval (M.sufCmaGame (etmToMACForger E M tagBound ciAdv) n)) :=
  succProbability_ciGame_encryptThenMAC_eq E M hctLen tagBound ciAdv n htagBoundN

example (n : ℕ) :
    Game.advantage
      (ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame cpaAdv false n))
      (ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame cpaAdv true n)) =
    Game.advantage
      (ProbComp.eval (E.cpaGame (etmToCPAAdversary M cpaAdv) false n))
      (ProbComp.eval (E.cpaGame (etmToCPAAdversary M cpaAdv) true n)) :=
  advantage_cpaGame_encryptThenMAC_eq E M hctLen cpaAdv n

example (n Q : ℕ) (hq : (cpaAdv n []).IsQueryBounded Q) :
    (Game.advantage
        (ProbComp.eval ((prfCipher family hpoly hlen).cpaGame cpaAdv false n))
        (ProbComp.eval ((prfCipher family hpoly hlen).cpaGame cpaAdv true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (cpaToPrfDistinguisher cpaAdv false) n))
        (ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher cpaAdv false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (cpaToPrfDistinguisher cpaAdv true) n))
        (ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher cpaAdv true) n)) : ℝ) +
      2 * (Q : ℝ) ^ 2 / (2 : ℝ) ^ n :=
  advantage_cpaGame_prfCipher_le family hpoly hlen cpaAdv n Q hq

-- Generic asymptotic compositions (Theorem 9.2).
example (hmac : M.SUFCMA) : (encryptThenMAC E M hctLen).CiphertextIntegrity :=
  ciphertextIntegrity_encryptThenMAC E M hctLen hmac

example (hcpa : E.INDCPA) : (encryptThenMAC E M hctLen).INDCPA :=
  indcpa_encryptThenMAC E M hctLen hcpa

example (hcpa : E.INDCPA) (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).AuthenticatedEncryption :=
  authenticatedEncryption_encryptThenMAC E M hctLen hcpa hmac

example (hcpa : E.INDCPA) (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).INDCCA :=
  indcca_encryptThenMAC E M hctLen hcpa hmac

-- Reindexed `prfMAC` corollaries.
example {ctLen : ℕ → ℕ}
    (hctPoly : ComputableInPolyTime ctLen encUnary encUnary)
    (hctMono : StrictMono ctLen)
    (hctLenPrf : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = ctLen n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E
      ((prfMAC family hprf.polyTime).reindex ctLen hctPoly)
      hctLenPrf).AuthenticatedEncryption :=
  authenticatedEncryption_encryptThenMAC_prfMAC E hprf hctPoly hctMono hctLenPrf hcpa

example {ctLen : ℕ → ℕ}
    (hctPoly : ComputableInPolyTime ctLen encUnary encUnary)
    (hctMono : StrictMono ctLen)
    (hctLenPrf : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = ctLen n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E
      ((prfMAC family hprf.polyTime).reindex ctLen hctPoly)
      hctLenPrf).INDCCA :=
  indcca_encryptThenMAC_prfMAC E hprf hctPoly hctMono hctLenPrf hcpa

-- End-to-end non-vacuous instantiation from `PseudorandomFunction` (Theorems 5.2 and 9.2).
example : (prfCipher family hprf.polyTime hprf.length_eq).INDCPA :=
  hprf.indcpa_prfCipher

example : (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).AuthenticatedEncryption :=
  hprf.authenticatedEncryption_prfEncryptThenMAC

example : (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).INDCCA :=
  hprf.indcca_prfEncryptThenMAC

end CertificatesAndReductions

end ComplexityTests.Crypto.EncryptThenMAC
