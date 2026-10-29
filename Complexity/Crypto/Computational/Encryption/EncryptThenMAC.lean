/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.Authenticated
public import Complexity.Crypto.Computational.MAC
import Complexity.Crypto.Computational.PseudorandomFunction.RandomOracle
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Tidy
import Complexity.Crypto.Game.Hybrid
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.BitString.List
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Encrypt-then-MAC Authenticated Encryption and PRF-Based Instantiation

This module formalizes the generic **Encrypt-then-MAC** composition (`encryptThenMAC`) and its
security reductions ([Boneh and Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6,
Section 9.4.1 and Theorem 9.2][BonehShoup2023], printed pp. 367–368), together with a concrete
randomized PRF-based symmetric cipher (`prfCipher`, [BonehShoup2023], Section 5.4.1, Example 5.2
and Theorem 5.2, printed pp. 183–189) that witnesses joint non-vacuity of all hypotheses:

1. **Generic Encrypt-then-MAC composition (`encryptThenMAC`, `etmToMACForger`,
   `etmToCPAAdversary`, `succProbability_ciGame_encryptThenMAC_eq`,
   `advantage_cpaGame_encryptThenMAC_eq`, `ciphertextIntegrity_encryptThenMAC`,
   `indcpa_encryptThenMAC`, `authenticatedEncryption_encryptThenMAC`, `indcca_encryptThenMAC`)**
   ([BonehShoup2023], Section 9.4.1, Theorem 9.2, printed pp. 367–368): given a symmetric cipher
   `E : SymmetricCipher` whose ciphertexts on `n`-bit plaintexts under supported keys at security
   parameter `n` have length `M.msgLen n`, and a message authentication code `M : MACScheme`
   authenticating `M.msgLen n`-bit messages:
   * `keyGen n` samples independent keys `ke ← E.keyGen n` and `km ← M.keyGen n` and encodes the
     pair as `encPair encBits encBits (ke, km)`.
   * `encrypt n k msg` encrypts `c ← E.encrypt n (unframe k) msg`, signs
     `tag ← M.sign (dropFrame k) c`, and returns `encPair encBits encBits (c, tag)`.
   * `decrypt n k ct` checks canonical pair framing
     `encPair encBits encBits (unframe ct, dropFrame ct) == ct`, checks
     `(unframe ct).length == M.msgLen n`, and verifies `M.verify (dropFrame k) (unframe ct)
     (dropFrame ct)`; if all three hold, it returns `E.decrypt n (unframe k) (unframe ct)`, and
     otherwise `none`.
   Because `encPair encBits encBits` is injective, ciphertext freshness in `ciGame` coincides with
   message-tag pair freshness in `M.sufCmaGame`, yielding exact per-parameter equalities for both
   ciphertext integrity (`succProbability_ciGame_encryptThenMAC_eq`) and CPA advantage
   (`advantage_cpaGame_encryptThenMAC_eq`). Combining Theorem 9.2 with Theorem 9.1
   (`AuthenticatedEncryption.indcca`) yields `indcca_encryptThenMAC`, and combining with
   `MACScheme.reindex` on `prfMAC` yields `authenticatedEncryption_encryptThenMAC_prfMAC` and
   `indcca_encryptThenMAC_prfMAC`.
2. **Concrete non-vacuous PRF-based symmetric cipher and end-to-end Encrypt-then-MAC instance
   (`prfCipher`, `cpaToPrfDistinguisher`, `advantage_cpaGame_prfCipher_le`,
   `PseudorandomFunction.indcpa_prfCipher`, `prfEncryptThenMAC`,
   `PseudorandomFunction.authenticatedEncryption_prfEncryptThenMAC`,
   `PseudorandomFunction.indcca_prfEncryptThenMAC`)** ([BonehShoup2023], Section 5.4.1, Example 5.2
   and Theorem 5.2, printed pp. 183–189): for any `PseudorandomFunction family`, `prfCipher`
   encrypts an `n`-bit message `msg` under an `n`-bit key `k` by sampling a random nonce
   `r ← BitString.sampleList n` and outputting the `2 * n`-bit ciphertext
   `r ++ List.zipWith xor (family k r) msg`. Using `OracleComp.IdenticalUntilBad.advantage_le`
   between the lazy random-function game (Boneh–Shoup Game 2, "faithful gnome") and the fresh
   one-time-pad game (Boneh–Shoup Game 3, "forgetful gnome"), we prove the quantitative CPA bound
   of Theorem 5.2 and derive `PseudorandomFunction.indcpa_prfCipher`. Combining `prfCipher` with
   `(prfMAC family hprf.polyTime).reindex (fun n => 2 * n) _` produces `prfEncryptThenMAC`, which
   satisfies `AuthenticatedEncryption` and `INDCCA` assuming only `PseudorandomFunction family`.

## Specializations and omissions relative to Boneh–Shoup Section 9.4.1 and Section 5.4.1

* **Ciphertext-length compatibility (`c.length = M.msgLen n`)**: in Section 9.4.1 (printed p. 367),
  `E` is defined over `(Ke, M, C)` and `I` over `(Km, C, T)`. Here plaintexts at security parameter
  `n` have length `n` and ciphertexts under supported keys have length `M.msgLen n`. Because
  `(M.reindex ctLen hctLen).msgLen n = M.msgLen (ctLen n)`, reindexing `M` by `ctLen` supplies
  message length `ctLen n` when the base MAC has `M.msgLen = id` (as holds for `prfMAC`), while
  transferring `M.SUFCMA` to `(M.reindex ctLen hctLen).SUFCMA` via `MACScheme.SUFCMA.reindex`
  additionally requires `StrictMono ctLen` (both hold for `prfEncryptThenMAC` with
  `ctLen := fun n => 2 * n`).
* **Omitted 1AE half and query-count preservation in Theorem 9.2**: Theorem 9.2 in
  [BonehShoup2023] (printed p. 367) also states that "Also, EEtM is 1AE-secure assuming E is
  semantically secure and I is a one-time secure MAC system." and that `Bmac` (resp. `Bcpa`)
  "makes no more signing queries than Aci makes encryption queries" (resp. "makes no more
  encryption queries than does Acpa"). This module formalizes the multi-query adaptive
  `AuthenticatedEncryption` and `INDCCA` statements; the one-time `1AE` half and separate
  query-count preservation theorems are omitted.
* **Specialization of Theorem 5.2 to the Example 5.2 one-time-pad instantiation (`prfCipher`) and
  two-world CPA bound with a factor-`2` collision term**: Theorem 5.2 in [BonehShoup2023] (printed
  p. 184; proof on printed pp. 184–189) is stated for the general hybrid cipher `E'` combining a
  PRF `F` with a semantically secure cipher `E`, with bound
  `CPAadv[A, E'] <= Q^2 / N + 2 * PRFadv[B_F, F] + Q * SSadv[B_E, E]` in the bit-guessing CPA
  game (where `Q^2 / N` arises from the birthday bound `Pr[Z] <= Q^2 / (2 * N)` in equation (5.11)
  on printed p. 187). Here `prfCipher` formalizes the Example 5.2 instantiation (printed
  pp. 183–184) where `E` is the one-time pad `k xor m` on `{0, 1}^n` (`SSadv = 0`, `N = 2^n`), and
  `advantage_cpaGame_prfCipher_le` bounds two-world `cpaGame` distinguishing advantage by
  `PRFadv[cpaToPrfDistinguisher adversary false, F] +
  PRFadv[cpaToPrfDistinguisher adversary true, F] + 2 * Q^2 / 2^n`: it uses two fixed-bit PRF
  distinguishers instead of one coin-flipping distinguisher `B_F` with factor `2`, and its
  collision term `2 * Q^2 / 2^n` is `2×` the source's `Q^2 / N = Q^2 / 2^n` because
  `bad_prfCipherForgetfulWithBadOracle_le` uses a per-step union bound `Q * Q / 2^n` per challenge
  bit rather than the birthday sum `sum_{i < Q} i / 2^n <= Q^2 / 2^(n + 1)`.

## Main definitions

* `Cslib.Crypto.encryptThenMAC`: generic Encrypt-then-MAC symmetric cipher (`Section 9.4.1`).
* `Cslib.Crypto.etmToMACHandler`, `Cslib.Crypto.etmToMACForger`: ciphertext-integrity to SUF-CMA
  forger reduction (`Theorem 9.2, Part 1`).
* `Cslib.Crypto.etmToCPAHandler`, `Cslib.Crypto.etmToCPAAdversary`: IND-CPA reduction for
  `encryptThenMAC` (`Theorem 9.2, Part 2`).
* `Cslib.Crypto.prfCipher`: concrete randomized PRF-based symmetric cipher with `2 * n`-bit
  ciphertexts (`Example 5.2`).
* `Cslib.Crypto.cpaToPrfHandler`, `Cslib.Crypto.cpaToPrfDistinguisher`: CPA-to-PRF distinguisher
  reduction for `prfCipher` (`Theorem 5.2, Figure 5.1`).
* `Cslib.Crypto.prfEncryptThenMAC`: concrete Encrypt-then-MAC cipher combining `prfCipher` with
  reindexed `prfMAC` on `2 * n`-bit ciphertexts.

## Main results

* `Cslib.Crypto.isOraclePPT_etmToMACForger`, `Cslib.Crypto.eval_sufCmaGame_etmToMACForger`,
  `Cslib.Crypto.succProbability_ciGame_encryptThenMAC_eq`: exact CI-to-MAC reduction (`CIadv =
  MACadv`).
* `Cslib.Crypto.isOraclePPT_etmToCPAAdversary`, `Cslib.Crypto.eval_cpaGame_etmToCPAAdversary`,
  `Cslib.Crypto.advantage_cpaGame_encryptThenMAC_eq`: exact CPA reduction (`CPAadv = CPAadv`).
* `Cslib.Crypto.ciphertextIntegrity_encryptThenMAC`, `Cslib.Crypto.indcpa_encryptThenMAC`,
  `Cslib.Crypto.authenticatedEncryption_encryptThenMAC`, `Cslib.Crypto.indcca_encryptThenMAC`,
  `Cslib.Crypto.authenticatedEncryption_encryptThenMAC_prfMAC`,
  `Cslib.Crypto.indcca_encryptThenMAC_prfMAC`: asymptotic AE and IND-CCA security of
  Encrypt-then-MAC (`Theorem 9.2` and `Theorem 9.1`).
* `Cslib.Crypto.prfCipher_ciphertext_length`, `Cslib.Crypto.isOraclePPT_cpaToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfRealGame_cpaToPrfDistinguisher`,
  `Cslib.Crypto.advantage_cpaGame_prfCipher_le`,
  `Cslib.Crypto.PseudorandomFunction.indcpa_prfCipher`: quantitative and asymptotic IND-CPA security
  of `prfCipher` (`Theorem 5.2`).
* `Cslib.Crypto.PseudorandomFunction.authenticatedEncryption_prfEncryptThenMAC`,
  `Cslib.Crypto.PseudorandomFunction.indcca_prfEncryptThenMAC`: non-vacuous end-to-end AE and
  IND-CCA security of `prfEncryptThenMAC` from `PseudorandomFunction family`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 5.4.1 (Example 5.2, Theorem 5.2, printed pp. 183–189) and
  Section 9.4.1 (Theorem 9.2, printed pp. 367–368).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal BigOperators

/-! ### Generic Encrypt-then-MAC Construction and Security (Boneh–Shoup Section 9.4.1) -/

/-- **Encrypt-then-MAC symmetric cipher** ([BonehShoup2023], Section 9.4.1, printed p. 367):
given a symmetric cipher `E : SymmetricCipher` whose ciphertexts on `n`-bit messages under supported
keys at security parameter `n` have length `M.msgLen n`, and a message authentication code
`M : MACScheme` on `M.msgLen n`-bit messages:
* `keyGen n` samples independent keys `ke ← E.keyGen n` and `km ← M.keyGen n` and returns
  `encPair encBits encBits (ke, km)`.
* `encrypt n k msg` encrypts `c ← E.encrypt n (unframe k) msg`, computes a tag
  `tag ← M.sign (dropFrame k) c`, and returns `encPair encBits encBits (c, tag)`.
* `decrypt n k ct` checks canonical pair framing
  `encPair encBits encBits (unframe ct, dropFrame ct) == ct`, checks
  `(unframe ct).length == M.msgLen n`, and verifies
  `M.verify (dropFrame k) (unframe ct) (dropFrame ct)`; if all three hold, it returns
  `E.decrypt n (unframe k) (unframe ct)`, and otherwise `none`.

Canonical pair framing `encPair encBits encBits (c, tag)` establishes a bijection between valid
encoded ciphertexts `ct` and pairs `(c, tag)` with `c.length = M.msgLen n`, so ciphertext freshness
in `ciGame` coincides with pair freshness in `M.sufCmaGame`. -/
noncomputable def encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    SymmetricCipher where
  keyGen n := do
    let ke ← E.keyGen n
    let km ← M.keyGen n
    return encPair encBits encBits (ke, km)
  encrypt n k msg := do
    let c ← E.encrypt n (unframe k) msg
    let tag ← M.sign (dropFrame k) c
    return encPair encBits encBits (c, tag)
  decrypt n k ct :=
    if (encPair encBits encBits (unframe ct, dropFrame ct) == ct) &&
        ((unframe ct).length == M.msgLen n) &&
        M.verify (dropFrame k) (unframe ct) (dropFrame ct) then
      E.decrypt n (unframe k) (unframe ct)
    else
      none
  keyGen_ppt := by
    have hpost : ComputableInPolyTime
        (fun p : (ℕ × List Bool) × List Bool => encPair encBits encBits (p.1.2, p.2))
        (encPair (encPair encUnary encBits) encBits) encBits :=
      ComputableInPolyTime.encoding_comp
        (((ComputableInPolyTime.snd encUnary encBits).comp
          (ComputableInPolyTime.fst (encPair encUnary encBits) encBits)).prod
            (ComputableInPolyTime.snd (encPair encUnary encBits) encBits))
    exact E.keyGen_ppt.bind_with
      ((M.keyGen_ppt.preprocess (ComputableInPolyTime.fst encUnary encBits)).bind_with
        hpost.isPPTOn)
  encrypt_ppt := by
    let I := encPair encUnary (encPair encBits encBits)
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
    have hk := (ComputableInPolyTime.fst encBits encBits).comp hrest
    have hm := (ComputableInPolyTime.snd encBits encBits).comp hrest
    have hrun := E.isPPTOn_encrypt_comp hn (ComputableInPolyTime.unframe.comp hk) hm
    have hsign := M.isPPTOn_sign_comp
      (ComputableInPolyTime.dropFrame.comp (hk.comp (ComputableInPolyTime.fst I encBits)))
      (ComputableInPolyTime.snd I encBits)
    have hpost : ComputableInPolyTime
        (fun p : ((ℕ × List Bool × List Bool) × List Bool) × List Bool =>
          encPair encBits encBits (p.1.2, p.2))
        (encPair (encPair I encBits) encBits) encBits :=
      ComputableInPolyTime.encoding_comp
        (((ComputableInPolyTime.snd I encBits).comp
          (ComputableInPolyTime.fst (encPair I encBits) encBits)).prod
            (ComputableInPolyTime.snd (encPair I encBits) encBits))
    exact hrun.bind_with (hsign.bind_with hpost.isPPTOn)
  decrypt_polyTime := by
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
    have hk := (ComputableInPolyTime.fst encBits encBits).comp hrest
    have hct := (ComputableInPolyTime.snd encBits encBits).comp hrest
    have hmsgLen := M.msgLen_polyTime.comp hn
    have hmsg := ComputableInPolyTime.unframe.comp hct
    have htag := ComputableInPolyTime.dropFrame.comp hct
    have hver := M.computableInPolyTime_verify_comp
      (ComputableInPolyTime.dropFrame.comp hk) hmsg htag
    have hroundTrip := ComputableInPolyTime.beq (encB := encBits)
      (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.frame.comp hmsg) htag) hct
    have hsize := ComputableInPolyTime.beq (encB := encUnary)
      (ComputableInPolyTime.length_bits.comp hmsg) hmsgLen
    have hcond := ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.bool_and.comp (hroundTrip.prod hsize)).prod hver)
    have hyes := E.decrypt_polyTime.comp
      (hn.prod ((ComputableInPolyTime.unframe.comp hk).prod hmsg))
    exact ComputableInPolyTime.ite hcond hyes (ComputableInPolyTime.const none)
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hk hct
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
    have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
      simp [encPair_apply, dropFrame_frame_append]
    rw [hunframe_k, hdrop_k] at hct
    obtain ⟨c, hc, tag, htag, rfl⟩ := hct
    have hunframe_ct : unframe (encPair encBits encBits (c, tag)) = c := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_ct : dropFrame (encPair encBits encBits (c, tag)) = tag := by
      simp [encPair_apply, dropFrame_frame_append]
    have hcLen : c.length = M.msgLen n := hctLen n ke hke msg hmsg c hc
    have hver : M.verify km c tag = true := M.verify_sign n km hkm c hcLen tag htag
    have hdec : E.decrypt n ke c = some msg := E.decrypt_encrypt n ke hke msg hmsg c hc
    rw [hunframe_k, hdrop_k, hunframe_ct, hdrop_ct]
    simp [hcLen, hver, hdec]

/-! #### Ciphertext-Integrity to SUF-CMA Reduction for Theorem 9.2 -/

/-- Open stateful handler that simulates the `ciEncryptionOracle` of `encryptThenMAC E M` inside
`M.sufCmaGame` ([BonehShoup2023], Section 9.4.1, Theorem 9.2, Part 1): on an `n`-bit message query
`request.2`, it encrypts `c ← E.encrypt n ke request.2`, queries the external MAC signing oracle on
`((), c)` (truncating the returned tag to `tagBound` bits), and returns
`encPair encBits encBits (c, tag)`. -/
noncomputable def etmToMACHandler (E : SymmetricCipher) (n tagBound : ℕ) (ke : List Bool)
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    if request.2.length == n then do
      let c ← ProbOracleComp.sample (E.encrypt n ke request.2)
      (fun tag => (encPair encBits encBits (c, tag), ())) <$>
        (List.take tagBound <$> ProbOracleComp.query ((), c))
    else
      pure ([], ())

/-- Ciphertext-integrity to SUF-CMA reduction `etmToMACForger` ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 1, printed pp. 367–368): samples `ke ← E.keyGen n`, runs `adversary n []`
against `etmToMACHandler E n (tagBound n) ke`, and when the candidate ciphertext `out.1` has
canonical pair framing and `E.decrypt n ke (unframe out.1)` succeeds, outputs the candidate forgery
pair `(unframe out.1, dropFrame out.1)`; otherwise outputs a dummy pair of first-component length
`≠ M.msgLen n` that is rejected by `M.sufCmaGame`. -/
noncomputable def etmToMACForger (E : SymmetricCipher) (M : MACScheme) (tagBound : ℕ → ℕ)
    (adversary : CIAdversary) : Forger :=
  fun n _ => do
    let ke ← ProbOracleComp.sample (E.keyGen n)
    (fun out : List Bool × Unit =>
      if (encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
          (E.decrypt n ke (unframe out.1)).isSome then
        (unframe out.1, dropFrame out.1)
      else
        (if M.msgLen n == 0 then [false] else [], [])) <$>
      (OracleComp.interpret
        (ProbOracleComp.handler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (etmToMACHandler E n (tagBound n) ke))
        (adversary n [])).run ()

private theorem isOraclePPTOn_etmToMACHandler (E : SymmetricCipher) {tagBound : ℕ → ℕ}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        etmToMACHandler E pair.1.1.1 (tagBound pair.1.1.1) pair.1.2 pair.2.1 pair.2.2) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EIn := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  unfold etmToMACHandler
  have hcond : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        p.2.1.2.length == p.1.1.1)
      EIn encBool := by
    dsimp only [EIn, ECaller]; polytime
  have hencArg : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        (p.1.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn, ECaller]; fun_prop
  have henc : IsOraclePPTOn (Operation := Unit) EIn encBits
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        ProbOracleComp.sample (E.encrypt p.1.1.1 p.1.2 p.2.1.2)) :=
    (E.encrypt_ppt.preprocess hencArg).isOraclePPTOn (Operation := Unit)
  have hqReq : ComputableInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool => q.2)
      (encPair EIn encBits) encBits := by
    fun_prop
  have hqN : ComputableInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        q.1.1.1.1)
      (encPair EIn encBits) encUnary := by
    dsimp only [EIn, ECaller]; fun_prop
  have hqLim : ComputableInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        tagBound q.1.1.1.1)
      (encPair EIn encBits) encUnary :=
    htagBound.comp hqN
  have hq : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits) encBits
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        List.take (tagBound q.1.1.1.1) <$> ProbOracleComp.query ((), q.2)) :=
    IsOraclePPTOn.query_take' (Operation := Unit) () hqReq hqLim
  have hpairArg : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (r.1.2, r.2))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits encBits) := by
    fun_prop
  have hmap : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (encPair encBits encBits (r.1.2, r.2), ()))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits (encFinEnum Unit)) :=
    ComputableTidilyInPolyTime.prod hpairArg.encoded (ComputableTidilyInPolyTime.const ())
  have hqMap : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits)
      (encPair encBits (encFinEnum Unit))
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (fun tag => (encPair encBits encBits (q.2, tag), ())) <$>
          (List.take (tagBound q.1.1.1.1) <$> ProbOracleComp.query ((), q.2))) :=
    hq.map_with hmap
  have hyes : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinEnum Unit))
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => do
        let c ← ProbOracleComp.sample (E.encrypt p.1.1.1 p.1.2 p.2.1.2)
        (fun tag => (encPair encBits encBits (c, tag), ())) <$>
          (List.take (tagBound p.1.1.1) <$> ProbOracleComp.query ((), c))) :=
    henc.bind_with hqMap
  have hno : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinEnum Unit))
      (fun _ : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        pure ([], ())) :=
    (ComputableInPolyTime.const ([], ())).isOraclePPTOn (Operation := Unit)
  exact IsOraclePPTOn.cond' hcond hyes hno

/-- `etmToMACForger` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_etmToMACForger (E : SymmetricCipher) (M : MACScheme) {tagBound : ℕ → ℕ}
    {adversary : CIAdversary}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
    (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT (encPair encBits encBits) (etmToMACForger E M tagBound adversary) := by
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hke : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => ProbOracleComp.sample (E.keyGen caller.1)) :=
    (E.keyGen_ppt.preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn (Operation := Unit)
  have hhandler := isOraclePPTOn_etmToMACHandler E htagBound
  have hprepare : ComputableInPolyTime
      (fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        2 * (ce * (2 * pair.1.1.1 + 2 * pair.1.2.length + pair.2.length + 3) ^ de) +
          tagBound pair.1.1.1 + 2)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; polytime
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBits (encFinEnum Unit))
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (etmToMACHandler E caller.1.1 (tagBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open'
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        etmToMACHandler E caller.1.1 (tagBound caller.1.1) caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller query =>
        2 * (ce * (2 * caller.1.1 + 2 * caller.2.length + query.length + 3) ^ de) +
          tagBound caller.1.1 + 2)
      hprepare hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold etmToMACHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨c, hc, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      change c ∈ OracleComp.support
        (ProbOracleComp.sample (E.encrypt caller.1.1 caller.2 request.2)) at hc
      rw [ProbOracleComp.support_sample] at hc
      have hcLen := hlenEnc (caller.1.1, caller.2, request.2) c hc
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hcLen
      have hcBound : c.length ≤
          ce * (2 * caller.1.1 + 2 * caller.2.length + request.2.length + 3) ^ de :=
        hcLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
      obtain ⟨tag, htag, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨rawTag, _, rfl⟩ := ProbOracleComp.mem_support_map htag
      have htagTake : (List.take (tagBound caller.1.1) rawTag).length ≤ tagBound caller.1.1 :=
        List.length_take_le _ _
      refine ⟨trivial, ?_, by lia⟩
      simp only [length_encPair, encBits_apply]
      lia
    · have hresEq := ProbOracleComp.eq_of_mem_support_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, by lia⟩
  have hdecArg : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (p.1.1.1, p.1.2, unframe p.2.1))
      (encPair ECaller (encPair encBits (encFinEnum Unit)))
      (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [ECaller]; fun_prop
  have hdecSome : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (E.decrypt p.1.1.1 p.1.2 (unframe p.2.1)).isSome)
      (encPair ECaller (encPair encBits (encFinEnum Unit))) encBool :=
    (E.decrypt_polyTime.tidy.comp hdecArg).optionIsSome
  have hpostYes : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (unframe p.2.1, dropFrame p.2.1))
      (encPair ECaller (encPair encBits (encFinEnum Unit))) (encPair encBits encBits) := by
    dsimp only [ECaller]; fun_prop
  have hframeEq : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => p.1 == p.2)
      (encPair encBits encBits) encBool := by
    polytime
  have houtProj : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) => p.2.1)
      (encPair ECaller (encPair encBits (encFinEnum Unit))) encBits := by
    fun_prop
  have hframeCond : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        encPair encBits encBits (unframe p.2.1, dropFrame p.2.1) == p.2.1)
      (encPair ECaller (encPair encBits (encFinEnum Unit))) encBool :=
    hframeEq.comp (hpostYes.encoded.prod houtProj)
  have hand : ComputableTidilyInPolyTime
      (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := by
    polytime
  have hpostCond : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (encPair encBits encBits (unframe p.2.1, dropFrame p.2.1) == p.2.1) &&
          (E.decrypt p.1.1.1 p.1.2 (unframe p.2.1)).isSome)
      (encPair ECaller (encPair encBits (encFinEnum Unit))) encBool :=
    hand.comp (hframeCond.prod hdecSome)
  have hnProj : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) => M.msgLen p.1.1.1)
      (encPair ECaller (encPair encBits (encFinEnum Unit))) encUnary := by
    dsimp only [ECaller]
    exact (M.computableInPolyTime_msgLen_comp ((by polytime))).tidy
  have hpostNo : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (if M.msgLen p.1.1.1 == 0 then [false] else [], ([] : List Bool)))
      (encPair ECaller (encPair encBits (encFinEnum Unit))) (encPair encBits encBits) :=
    ComputableTidilyInPolyTime.prod
      (ComputableTidilyInPolyTime.cond
        (ComputableTidilyInPolyTime.unary_beq hnProj (ComputableTidilyInPolyTime.const 0))
        (ComputableTidilyInPolyTime.const [false])
        (ComputableTidilyInPolyTime.const []))
      (ComputableTidilyInPolyTime.const [])
  have hpost : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        if (encPair encBits encBits (unframe p.2.1, dropFrame p.2.1) == p.2.1) &&
            (E.decrypt p.1.1.1 p.1.2 (unframe p.2.1)).isSome then
          (unframe p.2.1, dropFrame p.2.1)
        else
          (if M.msgLen p.1.1.1 == 0 then [false] else [], []))
      (encPair ECaller (encPair encBits (encFinEnum Unit)))
      (encPair encBits encBits) :=
    ComputableTidilyInPolyTime.cond hpostCond hpostYes hpostNo
  have hrunMap : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBits encBits)
      (fun caller : (ℕ × List Bool) × List Bool =>
        (fun out : List Bool × Unit =>
          if (encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
              (E.decrypt caller.1.1 caller.2 (unframe out.1)).isSome then
            (unframe out.1, dropFrame out.1)
          else
            (if M.msgLen caller.1.1 == 0 then [false] else [], [])) <$>
          (OracleComp.interpret
            (ProbOracleComp.handler
              (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
              (etmToMACHandler E caller.1.1 (tagBound caller.1.1) caller.2))
            (adversary caller.1.1 [])).run ()) :=
    hrun.map_with hpost
  unfold etmToMACForger
  exact (hke.bind_with hrunMap).isOraclePPT

private theorem list_contains_map_encPair (pairs : List (List Bool × List Bool))
    (p : List Bool × List Bool) :
    (pairs.map (encPair encBits encBits)).contains (encPair encBits encBits p) =
      pairs.contains p := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact List.mem_map_of_injective (encPair encBits encBits).injective

private theorem etm_sufCma_win_eq_ci_win (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (n : ℕ) (ke km out : List Bool) (queriedPairs : List (List Bool × List Bool)) :
    (let pair :=
      if (encPair encBits encBits (unframe out, dropFrame out) == out) &&
          (E.decrypt n ke (unframe out)).isSome then
        (unframe out, dropFrame out)
      else
        (if M.msgLen n == 0 then [false] else [], [])
     (pair.1.length == M.msgLen n) && !queriedPairs.contains pair && M.verify km pair.1 pair.2) =
      (!(queriedPairs.map (encPair encBits encBits)).contains out &&
        ((encryptThenMAC E M hctLen).decrypt n (encPair encBits encBits (ke, km)) out).isSome) := by
  have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
    simp [encPair_apply, unframe_frame_append]
  have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
    simp [encPair_apply, dropFrame_frame_append]
  dsimp only [encryptThenMAC]
  rw [hunframe_k, hdrop_k]
  by_cases hframe : (encPair encBits encBits (unframe out, dropFrame out) == out) = true
  · by_cases hdec : (E.decrypt n ke (unframe out)).isSome = true
    · simp only [hframe, hdec, Bool.true_and, ↓reduceIte]
      have houtEq : encPair encBits encBits (unframe out, dropFrame out) = out :=
        beq_iff_eq.mp hframe
      rw [← list_contains_map_encPair queriedPairs (unframe out, dropFrame out), houtEq]
      cases hlen : ((unframe out).length == M.msgLen n) <;>
        cases hmem : (queriedPairs.map (encPair encBits encBits)).contains out <;>
        cases hver : M.verify km (unframe out) (dropFrame out) <;>
        simp [hdec]
    · have hdecF : (E.decrypt n ke (unframe out)).isSome = false := Bool.eq_false_iff.mpr hdec
      have hlenDummy :
          ((if M.msgLen n == 0 then [false] else []).length == M.msgLen n) = false := by
        cases M.msgLen n <;> rfl
      simp only [hframe, hdecF, Bool.true_and, Bool.false_eq_true, ↓reduceIte, hlenDummy,
        Bool.false_and]
      split_ifs <;> simp [hdecF]
  · have hframeF : (encPair encBits encBits (unframe out, dropFrame out) == out) = false :=
      Bool.eq_false_iff.mpr hframe
    have hlenDummy : ((if M.msgLen n == 0 then [false] else []).length == M.msgLen n) = false := by
      cases M.msgLen n <;> rfl
    simp only [hframeF, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlenDummy,
      Option.isSome_none, Bool.and_false]

/-- Running `etmToMACForger E M tagBound adversary` in `M.sufCmaGame` produces the exact same
winning distribution as running `adversary` in `(encryptThenMAC E M hctLen).ciGame` whenever
`tagBound n` bounds all MAC tag lengths on `M.msgLen n`-bit ciphertexts under supported keys at
security parameter `n`. -/
theorem eval_sufCmaGame_etmToMACForger (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (tagBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.sufCmaGame (etmToMACForger E M tagBound adversary) n) =
      ProbComp.eval ((encryptThenMAC E M hctLen).ciGame adversary n) := by
  simp only [MACScheme.sufCmaGame, SymmetricCipher.ciGame, etmToMACForger,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret]
  have hinner (km : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (M.signingPairOracle km q s)))
        (do
          let ke ← ProbOracleComp.sample (E.keyGen n)
          (fun out : List Bool × Unit =>
            if (encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
                (E.decrypt n ke (unframe out.1)).isSome then
              (unframe out.1, dropFrame out.1)
            else
              (if M.msgLen n == 0 then [false] else [], [])) <$>
            (OracleComp.interpret
              (ProbOracleComp.handler
                (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
                (etmToMACHandler E n (tagBound n) ke))
              (adversary n [])).run ())).run []).bind
        (fun out => PMF.pure
          ((out.1.1.length == M.msgLen n) && !out.2.contains out.1 &&
            M.verify km out.1.1 out.1.2)) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (M.signingPairOracle km q s)))
          ((OracleComp.interpret
            (ProbOracleComp.handler
              (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
              (etmToMACHandler E n (tagBound n) ke))
            (adversary n [])).run ())).run []).bind
          (fun out => PMF.pure
            (let pair :=
              if (encPair encBits encBits (unframe out.1.1, dropFrame out.1.1) == out.1.1) &&
                  (E.decrypt n ke (unframe out.1.1)).isSome then
                (unframe out.1.1, dropFrame out.1.1)
              else
                (if M.msgLen n == 0 then [false] else [], [])
             (pair.1.length == M.msgLen n) && !out.2.contains pair &&
               M.verify km pair.1 pair.2))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
    congr 1; funext ke
    rw [OracleComp.interpret_map, StateT.run_map]
    simp only [_root_.PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
  simp only [hinner]
  rw [PMF.bind_comm]
  have hkeyGen : ProbComp.eval ((encryptThenMAC E M hctLen).keyGen n) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [encryptThenMAC, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hkeyGen]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
  refine PMF.bind_congr_on_support _ _ _ fun km hkm => ?_
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  conv_lhs =>
    rhs; ext x
    rw [etm_sufCma_win_eq_ci_win E M hctLen n ke km x.1 x.2.2]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q (state : Unit × List (List Bool × List Bool)) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (M.signingPairOracle km q s)))
        (etmToMACHandler E n (tagBound n) ke q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s =>
      ProbComp.eval ((encryptThenMAC E M hctLen).ciEncryptionOracle n
        (encPair encBits encBits (ke, km)) q s))
    (represent := fun s : Unit × List (List Bool × List Bool) =>
      s.2.map (encPair encBits encBits))
    (step := by
      intro ⟨⟨⟩, msg⟩ ⟨⟨⟩, queriedPairs⟩
      have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      unfold etmToMACHandler SymmetricCipher.ciEncryptionOracle
      dsimp only [encryptThenMAC]
      rw [hunframe_k, hdrop_k]
      by_cases hlenEq : (msg.length == n) = true
      · simp only [hlenEq, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
          ProbOracleComp.run_interpret_sample, Probability.PMF.monad_bind_eq_bind,
          PMF.bind_map, Function.comp_def, PMF.map_bind, ProbComp.eval_bind,
          ProbComp.eval_pure, PMF.bind_bind]
        apply PMF.bind_congr_on_support
        intro c hc
        have hcLen : c.length = M.msgLen n := hctLen n ke hke msg (beq_iff_eq.mp hlenEq) c hc
        simp only [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          _root_.PMF.monad_map_eq_map, MACScheme.signingPairOracle, ProbComp.eval_bind,
          ProbComp.eval_pure]
        dsimp only [StateT.run]
        simp only [PMF.map_bind, PMF.pure_map, PMF.pure_bind]
        apply PMF.bind_congr_on_support
        intro tag htag
        rw [List.take_of_length_le (htagBound km hkm c hcLen tag htag)]
        rfl
      · simp [hlenEq, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure])
    (adversary n []) ((), [])
  dsimp only [List.map] at hsim
  rw [← hsim, PMF.bind_map, Function.comp_def]
  rfl

/-- **Quantitative Ciphertext-Integrity to SUF-CMA equality** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 1, printed pp. 367–368): when `tagBound n` bounds all MAC tag lengths on
`M.msgLen n`-bit ciphertexts under supported keys at security parameter `n`, the
ciphertext-integrity winning probability of `adversary` against `encryptThenMAC E M hctLen` equals
the SUF-CMA winning probability of `etmToMACForger E M tagBound adversary` against `M`
(`CIadv[Aci, EEtM] = MACadv[Bmac, I]`). -/
theorem succProbability_ciGame_encryptThenMAC_eq (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (tagBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    Game.succProbability (ProbComp.eval ((encryptThenMAC E M hctLen).ciGame adversary n)) =
      Game.succProbability
        (ProbComp.eval (M.sufCmaGame (etmToMACForger E M tagBound adversary) n)) := by
  rw [eval_sufCmaGame_etmToMACForger E M hctLen tagBound adversary n htagBound]

/-! #### IND-CPA Reduction for Theorem 9.2 -/

/-- Open stateful handler that simulates the `cpaEncryptionOracle` of `encryptThenMAC E M` inside
`E.cpaGame` ([BonehShoup2023], Section 9.4.1, Theorem 9.2, Part 2): on a valid pair of `n`-bit
messages `request.2`, it forwards `request` to the external CPA encryption oracle of `E`
(truncating the returned ciphertext `c` to `M.msgLen n` bits), computes `tag ← M.sign km c`, and
returns `encPair encBits encBits (c, tag)`. -/
noncomputable def etmToCPAHandler (M : MACScheme) (n : ℕ) (km : List Bool)
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then do
      let c ← List.take (M.msgLen n) <$> ProbOracleComp.query ((), request.2)
      (fun tag => (encPair encBits encBits (c, tag), ())) <$>
        ProbOracleComp.sample (M.sign km c)
    else
      pure ([], ())

/-- IND-CPA reduction `etmToCPAAdversary` for `encryptThenMAC E M` ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 2, printed pp. 367–368): samples a secret MAC key `km ← M.keyGen n` privately and
runs `adversary n []` against `etmToCPAHandler M n km`. -/
noncomputable def etmToCPAAdversary (M : MACScheme) (adversary : OracleDistinguisher) :
    OracleDistinguisher :=
  fun n _ => do
    let km ← ProbOracleComp.sample (M.keyGen n)
    Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (etmToCPAHandler M n km))
      (adversary n [])).run ()

private theorem isOraclePPTOn_etmToCPAHandler (M : MACScheme) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        etmToCPAHandler M pair.1.1.1 pair.1.2 pair.2.1 pair.2.2) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EIn := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  unfold etmToCPAHandler
  have hcond : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1.1) && ((dropFrame p.2.1.2).length == p.1.1.1))
      EIn encBool := by
    dsimp only [EIn, ECaller]; polytime
  have hqReq : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => p.2.1.2)
      EIn encBits := by
    dsimp only [EIn, ECaller]; fun_prop
  have hqLim : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => M.msgLen p.1.1.1)
      EIn encUnary := by
    dsimp only [EIn, ECaller]
    exact M.computableInPolyTime_msgLen_comp (by polytime)
  have hq : IsOraclePPTOn (Operation := Unit) EIn encBits
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        List.take (M.msgLen p.1.1.1) <$> ProbOracleComp.query ((), p.2.1.2)) :=
    IsOraclePPTOn.query_take' (Operation := Unit) () hqReq hqLim
  have hsignArg : ComputableInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (q.1.1.2, q.2))
      (encPair EIn encBits) (encPair encBits encBits) := by
    dsimp only [EIn, ECaller]; fun_prop
  have hsign : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits) encBits
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        ProbOracleComp.sample (M.sign q.1.1.2 q.2)) :=
    (M.sign_ppt.preprocess hsignArg).isOraclePPTOn (Operation := Unit)
  have hpairArg : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (r.1.2, r.2))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits encBits) := by
    fun_prop
  have hmap : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (encPair encBits encBits (r.1.2, r.2), ()))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits (encFinEnum Unit)) :=
    ComputableTidilyInPolyTime.prod hpairArg.encoded (ComputableTidilyInPolyTime.const ())
  have hsignMap : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits)
      (encPair encBits (encFinEnum Unit))
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (fun tag => (encPair encBits encBits (q.2, tag), ())) <$>
          ProbOracleComp.sample (M.sign q.1.1.2 q.2)) :=
    hsign.map_with hmap
  have hyes : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinEnum Unit))
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => do
        let c ← List.take (M.msgLen p.1.1.1) <$> ProbOracleComp.query ((), p.2.1.2)
        (fun tag => (encPair encBits encBits (c, tag), ())) <$>
          ProbOracleComp.sample (M.sign p.1.2 c)) :=
    hq.bind_with hsignMap
  have hno : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinEnum Unit))
      (fun _ : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        pure ([], ())) :=
    (ComputableInPolyTime.const ([], ())).isOraclePPTOn (Operation := Unit)
  exact IsOraclePPTOn.cond' hcond hyes hno

/-- `etmToCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_etmToCPAAdversary (M : MACScheme) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (etmToCPAAdversary M adversary) := by
  obtain ⟨cs, ds, hlenSign⟩ := M.sign_ppt.length_le
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hkm : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => ProbOracleComp.sample (M.keyGen caller.1)) :=
    (M.keyGen_ppt.preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn (Operation := Unit)
  have hhandler := isOraclePPTOn_etmToCPAHandler M
  have hprepare : ComputableInPolyTime
      (fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hmsgLenPair : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => M.msgLen pair.1.1.1)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]
    exact M.computableInPolyTime_msgLen_comp (by polytime)
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        2 * M.msgLen pair.1.1.1 +
          cs * (2 * pair.1.2.length + M.msgLen pair.1.1.1 + 2) ^ ds + 2)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller] at hmsgLenPair ⊢; polytime
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBool (encFinEnum Unit))
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (etmToCPAHandler M caller.1.1 caller.2))
          (adversary caller.1.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open'
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        etmToCPAHandler M caller.1.1 caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller _ =>
        2 * M.msgLen caller.1.1 +
          cs * (2 * caller.2.length + M.msgLen caller.1.1 + 2) ^ ds + 2)
      hprepare hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold etmToCPAHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨c, hc, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hc
      have hcTake : (List.take (M.msgLen caller.1.1) rawCt).length ≤ M.msgLen caller.1.1 :=
        List.length_take_le _ _
      obtain ⟨tag, htag, rfl⟩ := ProbOracleComp.mem_support_map hresult
      rw [ProbOracleComp.support_sample] at htag
      have htagLen := hlenSign (caller.2, List.take (M.msgLen caller.1.1) rawCt) tag htag
      simp only [length_encPair, encBits_apply] at htagLen
      have htagBound : tag.length ≤ cs * (2 * caller.2.length + M.msgLen caller.1.1 + 2) ^ ds :=
        htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))
      refine ⟨trivial, ?_, by lia⟩
      simp only [length_encPair, encBits_apply]
      lia
    · have hresEq := ProbOracleComp.eq_of_mem_support_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, by lia⟩
  have hrunMap : IsOraclePPTOn (Operation := Unit) ECaller encBool
      (fun caller : (ℕ × List Bool) × List Bool =>
        Prod.fst <$> (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (etmToCPAHandler M caller.1.1 caller.2))
          (adversary caller.1.1 [])).run ()) :=
    hrun.map' (ComputableInPolyTime.fst encBool (encFinEnum Unit))
  unfold etmToCPAAdversary
  exact (hkm.bind_with hrunMap).isOraclePPT

/-- Running `etmToCPAAdversary M adversary` in `E.cpaGame` at challenge bit `bit` produces the
exact same output distribution as running `adversary` in
`(encryptThenMAC E M hctLen).cpaGame` at challenge bit `bit`. -/
theorem eval_cpaGame_etmToCPAAdversary (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (E.cpaGame (etmToCPAAdversary M adversary) bit n) =
      ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame adversary bit n) := by
  simp only [SymmetricCipher.cpaGame, etmToCPAAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hkeyGen : ProbComp.eval ((encryptThenMAC E M hctLen).keyGen n) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [encryptThenMAC, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hkeyGen]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
  rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample]
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun km _ => ?_
  rw [OracleComp.interpret_map, StateT.run_map]
  simp only [_root_.PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q (state : Unit × Unit) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.cpaEncryptionOracle n ke bit q s)))
        (etmToCPAHandler M n km q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s =>
      ProbComp.eval ((encryptThenMAC E M hctLen).cpaEncryptionOracle n
        (encPair encBits encBits (ke, km)) bit q s))
    (represent := fun _ : Unit × Unit => ())
    (step := by
      intro ⟨⟨⟩, payload⟩ ⟨⟨⟩, ⟨⟩⟩
      have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      unfold etmToCPAHandler SymmetricCipher.cpaEncryptionOracle
      dsimp only [encryptThenMAC]
      rw [hunframe_k, hdrop_k]
      by_cases hlenEq : ((unframe payload).length == n && (dropFrame payload).length == n) = true
      · simp only [hlenEq, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          ProbOracleComp.run_interpret_sample,
          _root_.PMF.monad_map_eq_map, Probability.PMF.monad_bind_eq_bind,
          ProbComp.eval_bind, ProbComp.eval_pure]
        simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
        have hmbLen : (if bit then dropFrame payload else unframe payload).length = n := by
          cases bit <;> simp [hlenEq]
        dsimp only [StateT.run]
        simp only [PMF.map_comp, PMF.map_bind, Function.comp_def,
          PMF.pure_map, PMF.pure_bind, PMF.bind_bind]
        apply PMF.bind_congr_on_support
        intro c hc
        rw [List.take_of_length_le (le_of_eq (hctLen n ke hke _ hmbLen c hc))]
        rfl
      · simp [hlenEq, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure])
    (adversary n []) ((), ())
  have hsim' := congrArg (PMF.map Prod.fst) hsim
  simp only [PMF.map_comp, Function.comp_def] at hsim'
  exact hsim'

/-- **Quantitative IND-CPA equality for Encrypt-then-MAC** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 2, printed pp. 367–368): the CPA distinguishing advantage of `adversary` against
`encryptThenMAC E M hctLen` equals the CPA distinguishing advantage of
`etmToCPAAdversary M adversary` against `E` (`CPAadv[Acpa, EEtM] = CPAadv[Bcpa, E]`). -/
theorem advantage_cpaGame_encryptThenMAC_eq (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (adversary : OracleDistinguisher) (n : ℕ) :
    Game.advantage
      (ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame adversary false n))
      (ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame adversary true n)) =
    Game.advantage
      (ProbComp.eval (E.cpaGame (etmToCPAAdversary M adversary) false n))
      (ProbComp.eval (E.cpaGame (etmToCPAAdversary M adversary) true n)) := by
  rw [eval_cpaGame_etmToCPAAdversary E M hctLen adversary false n,
    eval_cpaGame_etmToCPAAdversary E M hctLen adversary true n]

/-! #### Asymptotic Security of Encrypt-then-MAC (Boneh–Shoup Theorem 9.2) -/

/-- **SUF-CMA security implies Ciphertext Integrity for Encrypt-then-MAC** ([BonehShoup2023],
Section 9.4.1, Theorem 9.2, Part 1, printed pp. 367–368): if `M` is strongly unforgeable
(`M.SUFCMA`), then `encryptThenMAC E M hctLen` satisfies `CiphertextIntegrity`. -/
theorem ciphertextIntegrity_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).CiphertextIntegrity := by
  obtain ⟨ck, dk, hlenKey⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlenSign⟩ := M.sign_ppt.length_le
  let tagBound : ℕ → ℕ := fun n => cs * (2 * (ck * (n + 1) ^ dk) + M.msgLen n + 2) ^ ds
  have htagBoundPoly : ComputableInPolyTime tagBound encUnary encUnary := by
    dsimp only [tagBound]; polytime
  have htagBound (n : ℕ) (km : List Bool) (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
      (c : List Bool) (hc : c.length = M.msgLen n) (tag : List Bool)
      (htag : tag ∈ (ProbComp.eval (M.sign km c)).support) : tag.length ≤ tagBound n := by
    have hkmLen := hlenKey n km hkm
    have htagLen := hlenSign (km, c) tag htag
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkmLen
    simp only [length_encPair, encBits_apply, hc] at htagLen
    exact htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))
  apply SymmetricCipher.CiphertextIntegrity.of_negligible
  intro adversary hadversary
  have hmacNeg := hmac.negligible (etmToMACForger E M tagBound adversary)
    (isOraclePPT_etmToMACForger E M htagBoundPoly hadversary)
  refine hmacNeg.congr fun n => ?_
  exact (succProbability_ciGame_encryptThenMAC_eq E M hctLen tagBound adversary n
    (htagBound n)).symm

/-- **IND-CPA security transfers to Encrypt-then-MAC** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 2, printed pp. 367–368): if `E` satisfies `INDCPA`, then
`encryptThenMAC E M hctLen` also satisfies `INDCPA`. -/
theorem indcpa_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E M hctLen).INDCPA := by
  intro adversary hadversary
  have hred := hcpa (etmToCPAAdversary M adversary) (isOraclePPT_etmToCPAAdversary M hadversary)
  refine hred.congr fun n => ?_
  exact (advantage_cpaGame_encryptThenMAC_eq E M hctLen adversary n).symm

/-- **Encrypt-then-MAC Authenticated Encryption Theorem** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, printed pp. 367–368): if `E` is `INDCPA`-secure and `M` is `SUFCMA`-secure, then
`encryptThenMAC E M hctLen` is an `AuthenticatedEncryption` cipher
(`INDCPA ∧ CiphertextIntegrity`). -/
theorem authenticatedEncryption_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (hcpa : E.INDCPA) (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).AuthenticatedEncryption :=
  ⟨indcpa_encryptThenMAC E M hctLen hcpa, ciphertextIntegrity_encryptThenMAC E M hctLen hmac⟩

/-- **Encrypt-then-MAC Adaptive Chosen-Ciphertext Security** ([BonehShoup2023], combining
Theorem 9.2 and Theorem 9.1): if `E` is `INDCPA`-secure and `M` is `SUFCMA`-secure, then
`encryptThenMAC E M hctLen` is `INDCCA`-secure. -/
theorem indcca_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (hcpa : E.INDCPA) (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).INDCCA :=
  (authenticatedEncryption_encryptThenMAC E M hctLen hcpa hmac).indcca

/-- **Encrypt-then-MAC with a reindexed PRF-based MAC is Authenticated Encryption**
([BonehShoup2023], combining Theorem 6.2 and Theorem 9.2): if `E` is `INDCPA`-secure with
ciphertext-length schedule `ctLen` (strictly monotone and computable in plain polynomial time) and
`family` is a uniform `PseudorandomFunction`, then
`encryptThenMAC E ((prfMAC family hprf.polyTime).reindex ctLen hctPoly) hctLen` satisfies
`AuthenticatedEncryption`. -/
theorem authenticatedEncryption_encryptThenMAC_prfMAC (E : SymmetricCipher)
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    {ctLen : ℕ → ℕ}
    (hctPoly : ComputableInPolyTime ctLen encUnary encUnary)
    (hctMono : StrictMono ctLen)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = ctLen n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E ((prfMAC family hprf.polyTime).reindex ctLen hctPoly)
      hctLen).AuthenticatedEncryption :=
  authenticatedEncryption_encryptThenMAC E
    ((prfMAC family hprf.polyTime).reindex ctLen hctPoly) hctLen hcpa
    (hprf.sufCma_prfMAC.reindex hctPoly hctMono)

/-- **Encrypt-then-MAC with a reindexed PRF-based MAC is IND-CCA secure** ([BonehShoup2023],
combining Theorem 6.2, Theorem 9.2, and Theorem 9.1): if `E` is `INDCPA`-secure with
ciphertext-length schedule `ctLen` (strictly monotone and computable in plain polynomial time) and
`family` is a uniform `PseudorandomFunction`, then
`encryptThenMAC E ((prfMAC family hprf.polyTime).reindex ctLen hctPoly) hctLen` satisfies
`INDCCA`. -/
theorem indcca_encryptThenMAC_prfMAC (E : SymmetricCipher)
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    {ctLen : ℕ → ℕ}
    (hctPoly : ComputableInPolyTime ctLen encUnary encUnary)
    (hctMono : StrictMono ctLen)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = ctLen n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E ((prfMAC family hprf.polyTime).reindex ctLen hctPoly) hctLen).INDCCA :=
  (authenticatedEncryption_encryptThenMAC_prfMAC E hprf hctPoly hctMono hctLen hcpa).indcca

/-! ### Concrete Non-Vacuous PRF-Based Cipher (Boneh–Shoup Example 5.2 & Theorem 5.2) -/

/-- **Randomized PRF-based symmetric cipher** ([BonehShoup2023], Section 5.4.1, Example 5.2 and
Theorem 5.2, printed pp. 183–189): given a keyed function family
`family : List Bool → List Bool → List Bool` computable in plain polynomial time that maps `n`-bit
keys and `n`-bit inputs to `n`-bit outputs:
* `keyGen n` samples a uniform `n`-bit key `k ← BitString.sampleList n`.
* `encrypt n k msg` samples a uniform `n`-bit nonce `r ← BitString.sampleList n` and outputs the
  `2 * n`-bit ciphertext `r ++ List.zipWith xor (family k r) msg`.
* `decrypt n k ct` checks `ct.length == 2 * n`; if so, splits `r := ct.take n` and `c := ct.drop n`
  and outputs `some (List.zipWith xor (family k r) c)`, and otherwise outputs `none`. -/
noncomputable def prfCipher (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    SymmetricCipher where
  keyGen n := BitString.sampleList n
  encrypt n k msg := do
    let r ← BitString.sampleList n
    return (r ++ List.zipWith xor (family k r) msg)
  decrypt n k ct :=
    if ct.length == 2 * n then
      some (List.zipWith xor (family k (ct.take n)) (ct.drop n))
    else
      none
  keyGen_ppt := by
    ppt
  encrypt_ppt := by
    have hfamTidy := hpoly.tidy
    ppt
  decrypt_polyTime := by
    have hfamTidy := hpoly.tidy
    have hcond : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool × List Bool => p.2.2.length == 2 * p.1)
        (encPair encUnary (encPair encBits encBits)) encBool := by polytime
    have hyes : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          (some (List.zipWith xor (family p.2.1 (p.2.2.take p.1)) (p.2.2.drop p.1)) :
            Option (List Bool)))
        (encPair encUnary (encPair encBits encBits)) (encOption encBits) := by polytime
    have hno : ComputableTidilyInPolyTime
        (fun _ : ℕ × List Bool × List Bool => (none : Option (List Bool)))
        (encPair encUnary (encPair encBits encBits)) (encOption encBits) :=
      ComputableTidilyInPolyTime.const none
    exact .of_tidy (ComputableTidilyInPolyTime.cond hcond hyes hno)
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    rw [BitString.eval_sampleList] at hk
    have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
    obtain ⟨r, hr, rfl⟩ := hct
    have hrLen : r.length = n := BitString.length_of_mem_support_uniformList hr
    have hpadLen : (family k r).length = n := by
      rw [hlen k r (by rw [hrLen, hkLen]), hkLen]
    have hzipLen : (List.zipWith xor (family k r) msg).length = n := by
      simp [hpadLen, hmsg]
    have hctLen : (r ++ List.zipWith xor (family k r) msg).length = 2 * n := by
      rw [List.length_append, hrLen, hzipLen]; lia
    have htake : (r ++ List.zipWith xor (family k r) msg).take n = r := by
      rw [← hrLen, List.take_left]
    have hdrop : (r ++ List.zipWith xor (family k r) msg).drop n =
        List.zipWith xor (family k r) msg := by
      rw [← hrLen, List.drop_left]
    simp [hctLen, htake, hdrop,
      BitString.zipWith_xor_self_left (family k r) msg (by rw [hpadLen, hmsg])]

/-- Every supported ciphertext of `prfCipher family hpoly hlen` on an `n`-bit plaintext under a
supported key at security parameter `n` has length `2 * n`. -/
theorem prfCipher_ciphertext_length (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (n : ℕ) (k : List Bool)
    (hk : k ∈ (ProbComp.eval ((prfCipher family hpoly hlen).keyGen n)).support)
    (msg : List Bool) (hmsg : msg.length = n) (ct : List Bool)
    (hct : ct ∈ (ProbComp.eval ((prfCipher family hpoly hlen).encrypt n k msg)).support) :
    ct.length = 2 * n := by
  dsimp only [prfCipher] at hk hct
  rw [BitString.eval_sampleList] at hk
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  obtain ⟨r, hr, rfl⟩ := hct
  have hrLen : r.length = n := BitString.length_of_mem_support_uniformList hr
  have hpadLen : (family k r).length = n := by
    rw [hlen k r (by rw [hrLen, hkLen]), hkLen]
  rw [List.length_append, List.length_zipWith, hrLen, hpadLen, hmsg, min_self]
  lia

/-! #### CPA-to-PRF Reduction and Game Hops for Theorem 5.2 -/

/-- Open stateful handler that simulates the `cpaEncryptionOracle` of `prfCipher` inside the PRF
distinguishing experiment ([BonehShoup2023], Section 5.4.1, Theorem 5.2, Figure 5.1, printed
pp. 185–186): on a pair of `n`-bit messages `(m0, m1)`, it samples a random nonce
`r ← BitString.sampleList n`, queries the external PRF/random-function oracle at `((), r)`
(truncating the returned pad to `n` bits), and returns `r ++ List.zipWith xor pad msg` where
`msg := if bit then m1 else m0`. -/
noncomputable def cpaToPrfHandler (n : ℕ) (bit : Bool) (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then do
      let msg := if bit then m1 else m0
      let r ← ProbOracleComp.sample (BitString.sampleList n)
      (fun pad => (r ++ List.zipWith xor pad msg, ())) <$>
        (List.take n <$> ProbOracleComp.query ((), r))
    else
      pure ([], ())

/-- CPA-to-PRF reduction `cpaToPrfDistinguisher` ([BonehShoup2023], Section 5.4.1, Theorem 5.2,
Figure 5.1, printed pp. 185–186): runs `adversary n []` against `cpaToPrfHandler n bit`. -/
noncomputable def cpaToPrfDistinguisher (adversary : OracleDistinguisher) (bit : Bool) :
    OracleDistinguisher :=
  fun n _ =>
    Prod.fst <$>
      (OracleComp.interpret
        (ProbOracleComp.handler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (cpaToPrfHandler n bit))
        (adversary n [])).run ()

private theorem isOraclePPTOn_cpaToPrfHandler (bit : Bool) :
    IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        cpaToPrfHandler pair.1.1 bit pair.2.1 pair.2.2) := by
  let ECaller := encPair encUnary encBits
  let EIn := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  unfold cpaToPrfHandler
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn, ECaller]; polytime
  have hr : IsOraclePPTOn (Operation := Unit) EIn encBits
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        ProbOracleComp.sample (BitString.sampleList p.1.1)) :=
    (ComputableInPolyTime.sampleList
      (by dsimp only [EIn, ECaller]; fun_prop)).isOraclePPTOn (Operation := Unit)
  have hqReq : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × Unit)) × List Bool => q.2)
      (encPair EIn encBits) encBits := by
    fun_prop
  have hqLim : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × Unit)) × List Bool => q.1.1.1)
      (encPair EIn encBits) encUnary := by
    dsimp only [EIn, ECaller]; fun_prop
  have hq : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits) encBits
      (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        List.take q.1.1.1 <$> ProbOracleComp.query ((), q.2)) :=
    IsOraclePPTOn.query_take' (Operation := Unit) () hqReq hqLim
  have hmap : ComputableInPolyTime
      (fun r : (((ℕ × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) × List Bool =>
        (r.1.2 ++ List.zipWith xor r.2
          (if bit then dropFrame r.1.1.2.1.2 else unframe r.1.1.2.1.2), ()))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits (encFinEnum Unit)) := by
    dsimp only [EIn, ECaller]
    cases bit <;> polytime
  have hqMap : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits)
      (encPair encBits (encFinEnum Unit))
      (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (fun pad => (q.2 ++ List.zipWith xor pad
          (if bit then dropFrame q.1.2.1.2 else unframe q.1.2.1.2), ())) <$>
          (List.take q.1.1.1 <$> ProbOracleComp.query ((), q.2))) :=
    hq.map_with' hmap
  have hyes : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinEnum Unit))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => do
        let r ← ProbOracleComp.sample (BitString.sampleList p.1.1)
        (fun pad => (r ++ List.zipWith xor pad
          (if bit then dropFrame p.2.1.2 else unframe p.2.1.2), ())) <$>
          (List.take p.1.1 <$> ProbOracleComp.query ((), r))) :=
    hr.bind_with hqMap
  have hno : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinEnum Unit))
      (fun _ : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => pure ([], ())) :=
    (ComputableInPolyTime.const ([], ())).isOraclePPTOn (Operation := Unit)
  exact IsOraclePPTOn.cond' hcond hyes hno

/-- `cpaToPrfDistinguisher` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_cpaToPrfDistinguisher {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (cpaToPrfDistinguisher adversary bit) := by
  let ECaller := encPair encUnary encBits
  have hhandler := isOraclePPTOn_cpaToPrfHandler bit
  have hprepare : ComputableInPolyTime
      (fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => 2 * pair.1.1 + 2)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; polytime
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBool (encFinEnum Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (cpaToPrfHandler caller.1 bit))
          (adversary caller.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open'
      (input := ECaller)
      (handler := fun caller : ℕ × List Bool => cpaToPrfHandler caller.1 bit)
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller _ => 2 * caller.1 + 2)
      hprepare hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold cpaToPrfHandler at hresult
    dsimp only at hresult
    by_cases hlenEq :
        ((unframe request.2).length == caller.1 && (dropFrame request.2).length == caller.1) = true
    · simp only [hlenEq, ↓reduceIte] at hresult
      obtain ⟨r, hr, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      change r ∈ OracleComp.support
        (ProbOracleComp.sample (BitString.sampleList caller.1)) at hr
      rw [ProbOracleComp.support_sample, BitString.eval_sampleList] at hr
      have hrLen : r.length = caller.1 := BitString.length_of_mem_support_uniformList hr
      obtain ⟨pad, hpad, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨rawPad, _, rfl⟩ := ProbOracleComp.mem_support_map hpad
      have hpadTake : (List.take caller.1 rawPad).length ≤ caller.1 := List.length_take_le _ _
      simp only [List.length_append, List.length_zipWith, hrLen]
      exact ⟨trivial, by lia, Nat.le_add_right _ _⟩
    · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte] at hresult
      have hresEq := ProbOracleComp.eq_of_mem_support_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, Nat.le_add_right _ _⟩
  unfold cpaToPrfDistinguisher
  exact (hrun.map' (ComputableInPolyTime.fst encBool (encFinEnum Unit))).isOraclePPT

/-- Running `cpaToPrfDistinguisher adversary bit` in `prfRealGame family` produces the exact same
output distribution as running `adversary` in `(prfCipher family hpoly hlen).cpaGame` at challenge
bit `bit` ([BonehShoup2023], Section 5.4.1, Theorem 5.2, Game 0, printed pp. 184–185). -/
theorem eval_prfRealGame_cpaToPrfDistinguisher (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (prfRealGame family (cpaToPrfDistinguisher adversary bit) n) =
      ProbComp.eval ((prfCipher family hpoly hlen).cpaGame adversary bit n) := by
  simp only [prfRealGame, SymmetricCipher.cpaGame, cpaToPrfDistinguisher,
    ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  rw [BitString.eval_sampleList] at hk
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  have hread := ProbOracleComp.run_interpret_readOnly
    (fun req (_ : Unit) => PMF.pure (prfOracle family n k req.2))
    ((OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (cpaToPrfHandler n bit))
      (adversary n [])).run ()) ()
  have hfst := congrArg (PMF.map Prod.fst) hread
  simp only [PMF.map_comp, Function.comp_def] at hfst
  rw [show (fun x : Bool × Unit => x) = id from rfl, PMF.map_id] at hfst
  simp only [OracleComp.interpret_map, ProbComp.eval_map, ProbOracleComp.eval_interpret,
    ProbComp.eval_pure]
  rw [← hfst, ProbOracleComp.run_interpret_run_interpret, ProbOracleComp.eval_run_interpret]
  simp only [PMF.map_comp, Function.comp_def]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q (state : Unit × Unit) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun req (s : Unit) => (PMF.pure (prfOracle family n k req.2)).map (·, s)))
        (cpaToPrfHandler n bit q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s =>
      ProbComp.eval ((prfCipher family hpoly hlen).cpaEncryptionOracle n k bit q s))
    (represent := fun _ : Unit × Unit => ())
    (step := by
      intro ⟨⟨⟩, payload⟩ ⟨⟨⟩, ⟨⟩⟩
      unfold cpaToPrfHandler SymmetricCipher.cpaEncryptionOracle
      dsimp only [prfCipher]
      by_cases hlenEq : ((unframe payload).length == n && (dropFrame payload).length == n) = true
      · simp only [hlenEq, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          ProbOracleComp.run_interpret_sample,
          _root_.PMF.monad_map_eq_map, Probability.PMF.monad_bind_eq_bind,
          ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
        dsimp only [StateT.run]
        simp only [PMF.map_bind, PMF.bind_map, Function.comp_def,
          PMF.pure_map, PMF.pure_bind, PMF.bind_bind]
        apply PMF.bind_congr_on_support
        intro r hr
        have hrLen : r.length = n := BitString.length_of_mem_support_uniformList hr
        have hpadLen : (family k r).length = n := by
          rw [hlen k r (by rw [hrLen, hkLen]), hkLen]
        simp [prfOracle, hrLen, List.take_of_length_le hpadLen.le]
      · simp [hlenEq, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure])
    (adversary n []) ((), ())
  have hsim' := congrArg (PMF.map Prod.fst) hsim
  simp only [PMF.map_comp, Function.comp_def] at hsim'
  exact hsim'

/-- Faithful lazy random-function CPA handler with a bad-collision flag ([BonehShoup2023], Section
5.4.1, Theorem 5.2, Game 2 "faithful gnome", printed p. 186): samples a random nonce `r`, raises the
bad flag if `r` was already in `cache`, looks up or samples `pad` via `memoize`, and returns
`r ++ List.zipWith xor (pad.take n) msg`. -/
private noncomputable def prfCipherFaithfulWithBadOracle (n : ℕ) (bit : Bool)
    (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool) × Bool) PMF (List Bool) :=
  fun ⟨cache, bad⟩ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then
      let msg := if bit then m1 else m0
      (BitString.uniformList n).bind fun r =>
        (memoize (fun _ => BitString.uniformList n) r cache).map fun res =>
          (r ++ List.zipWith xor (res.1.take n) msg,
            (res.2, bad || (cache.lookup r).isSome))
    else
      PMF.pure ([], (cache, bad))

/-- Forgetful CPA handler with a bad-collision flag ([BonehShoup2023], Section 5.4.1, Theorem 5.2,
Game 3 "forgetful gnome", printed p. 187): samples a random nonce `r`, raises the bad flag if `r`
was already in `cache`, samples an independent fresh `pad` regardless of `cache`, prepends
`(r, pad)` to `cache`, and returns `r ++ List.zipWith xor (pad.take n) msg`. -/
private noncomputable def prfCipherForgetfulWithBadOracle (n : ℕ) (bit : Bool)
    (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool) × Bool) PMF (List Bool) :=
  fun ⟨cache, bad⟩ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then
      let msg := if bit then m1 else m0
      (BitString.uniformList n).bind fun r =>
        (BitString.uniformList n).map fun pad =>
          (r ++ List.zipWith xor (pad.take n) msg,
            ((r, pad) :: cache, bad || (cache.lookup r).isSome))
    else
      PMF.pure ([], (cache, bad))

/-- Bit-independent one-time-pad CPA oracle: on a valid pair of `n`-bit messages, samples
independent uniform `n`-bit strings `r` and `pad` and returns `r ++ pad`. -/
private noncomputable def prfCipherOTPOracle (n : ℕ) (request : Unit × List Bool) :
    StateT Unit PMF (List Bool) :=
  fun _ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then
      (BitString.uniformList n).bind fun r =>
        (BitString.uniformList n).map fun pad =>
          (r ++ pad, ())
    else
      PMF.pure ([], ())

private theorem eval_prfIdealGame_cpaToPrfDistinguisher (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) :
    ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher adversary bit) n) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (prfCipherFaithfulWithBadOracle n bit))
        (adversary n [])).run ([], false)).map Prod.fst := by
  rw [prfIdealGame_eq_cached, ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
  dsimp only [cpaToPrfDistinguisher]
  rw [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.run_interpret_run_interpret]
  simp only [_root_.PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q (state : Unit × List (List Bool × List Bool)) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun req s => ProbComp.eval (cachedRandomFunctionOracle n req.2 s)))
        (cpaToPrfHandler n bit q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q (cache : List (List Bool × List Bool)) =>
      (prfCipherFaithfulWithBadOracle n bit q (cache, false)).map
        (fun res => (res.1, res.2.1)))
    (represent := fun s : Unit × List (List Bool × List Bool) => s.2)
    (step := by
      intro ⟨⟨⟩, payload⟩ ⟨⟨⟩, cache⟩
      unfold cpaToPrfHandler prfCipherFaithfulWithBadOracle
      by_cases hlenEq : ((unframe payload).length == n && (dropFrame payload).length == n) = true
      · simp only [hlenEq, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          ProbOracleComp.run_interpret_sample,
          _root_.PMF.monad_map_eq_map, Probability.PMF.monad_bind_eq_bind,
          BitString.eval_sampleList, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
        apply PMF.bind_congr_on_support
        intro r hr
        have hrLen : r.length = n := BitString.length_of_mem_support_uniformList hr
        simp only [cachedRandomFunctionOracle, hrLen, ↓reduceIte,
          ProbComp.eval_memoize, BitString.eval_sampleList]
        rfl
      · simp [hlenEq, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure])
    (adversary n []) ((), [])
  have hsim2 := ProbOracleComp.run_interpret_map_state
    (oracle := prfCipherFaithfulWithBadOracle n bit)
    (oracle' := fun q (cache : List (List Bool × List Bool)) =>
      (prfCipherFaithfulWithBadOracle n bit q (cache, false)).map
        (fun res => (res.1, res.2.1)))
    (represent := fun s : List (List Bool × List Bool) × Bool => s.1)
    (step := by
      intro ⟨⟨⟩, payload⟩ ⟨cache, bad⟩
      unfold prfCipherFaithfulWithBadOracle
      by_cases hlenEq : ((unframe payload).length == n && (dropFrame payload).length == n) = true
      · simp [hlenEq, PMF.map_bind, PMF.map_comp, Function.comp_def]
      · simp [hlenEq])
    (adversary n []) ([], false)
  have h1 := congrArg (PMF.map Prod.fst) hsim
  have h2 := congrArg (PMF.map Prod.fst) hsim2
  simp only [PMF.map_comp, Function.comp_def] at h1 h2
  exact h1.trans h2.symm

private theorem run_prfCipherForgetfulWithBadOracle_map_fst (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) (cache : List (List Bool × List Bool)) (bad : Bool) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (prfCipherForgetfulWithBadOracle n bit))
      (adversary n [])).run (cache, bad)).map Prod.fst =
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (prfCipherOTPOracle n))
      (adversary n [])).run ()).map Prod.fst := by
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := prfCipherForgetfulWithBadOracle n bit)
    (oracle' := prfCipherOTPOracle n)
    (represent := fun _ : List (List Bool × List Bool) × Bool => ())
    (step := by
      intro ⟨⟨⟩, payload⟩ ⟨c, b⟩
      unfold prfCipherForgetfulWithBadOracle prfCipherOTPOracle
      by_cases hlenEq : ((unframe payload).length == n && (dropFrame payload).length == n) = true
      · simp only [hlenEq, ↓reduceIte, PMF.map_bind, PMF.map_comp, Function.comp_def]
        simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
        have hmsgLen : (if bit then dropFrame payload else unframe payload).length = n := by
          cases bit <;> simp [hlenEq]
        congr 1; funext r
        have hpad :
            (BitString.uniformList n).map
              (fun pad => (r ++ List.zipWith xor (pad.take n)
                (if bit then dropFrame payload else unframe payload), ())) =
            ((BitString.uniformList n).map
              (fun pad => List.zipWith xor (pad.take n)
                (if bit then dropFrame payload else unframe payload))).map
              (fun otp => (r ++ otp, ())) := by
          simp [PMF.map_comp, Function.comp_def]
        rw [hpad, BitString.uniformList_map_take_zipWith_xor hmsgLen]
      · simp [hlenEq])
    (adversary n []) (cache, bad)
  have h := congrArg (PMF.map Prod.fst) hsim
  simp only [PMF.map_comp, Function.comp_def] at h
  exact h

private theorem identicalUntilBad_prfCipherFaithful_forgetful (n : ℕ) (bit : Bool) :
    OracleComp.IdenticalUntilBad
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (prfCipherFaithfulWithBadOracle n bit))
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (prfCipherForgetfulWithBadOracle n bit))
      (fun s => s.2 = true) where
  agree q s hs a s' hs' := by
    cases q with
    | inl m => rfl
    | inr request =>
      rcases s with ⟨cache, bad⟩
      rcases s' with ⟨cache', bad'⟩
      have hbad : bad = false := Bool.eq_false_iff.mpr hs
      have hbad' : bad' = false := Bool.eq_false_iff.mpr hs'
      subst hbad hbad'
      simp only [ProbOracleComp.handler, prfCipherFaithfulWithBadOracle,
        prfCipherForgetfulWithBadOracle, Bool.false_or]
      by_cases hlenEq :
          ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
      · simp only [hlenEq, ↓reduceIte, PMF.bind_apply]
        refine tsum_congr fun r => congrArg (_ * ·) ?_
        cases hlookup : cache.lookup r with
        | some pad₀ =>
          refine ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).trans
            ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).symm <;>
          · obtain ⟨res, -, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
            have h1 := congrArg (fun x => x.2.2) hres
            simp at h1
        | none =>
          have hmem : memoize (fun _ => BitString.uniformList n) r cache =
              (BitString.uniformList n).map (fun pad => (pad, (r, pad) :: cache)) := by
            simp [memoize_of_none, hlookup, PMF.map, Function.comp_def,
              Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
          rw [hmem]
          simp [PMF.map_comp]
      · simp [hlenEq]
  absorb_first q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      rcases s with ⟨cache, bad⟩
      simp only at hs
      subst hs
      simp only [ProbOracleComp.handler, prfCipherFaithfulWithBadOracle, Bool.true_or] at hx
      by_cases hlenEq :
          ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
      · simp only [hlenEq, ↓reduceIte] at hx
        obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        obtain ⟨res, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        rfl
      · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at hx
        subst x
        rfl
  absorb_second q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      rcases s with ⟨cache, bad⟩
      simp only at hs
      subst hs
      simp only [ProbOracleComp.handler, prfCipherForgetfulWithBadOracle, Bool.true_or] at hx
      by_cases hlenEq :
          ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
      · simp only [hlenEq, ↓reduceIte] at hx
        obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        obtain ⟨pad, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        rfl
      · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at hx
        subst x
        rfl

private theorem step_bad_prfCipherForgetfulWithBadOracle_le (n : ℕ) (bit : Bool)
    (request : Unit × List Bool) (cache : List (List Bool × List Bool)) :
    (prfCipherForgetfulWithBadOracle n bit request (cache, false)).toOuterMeasure
      {x | x.2.2 = true} ≤
      (cache.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ n) := by
  unfold prfCipherForgetfulWithBadOracle
  simp only [Bool.false_or]
  by_cases hlenEq : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
  · simp only [hlenEq, ↓reduceIte]
    rw [PMF.toOuterMeasure_bind_apply]
    calc ∑' r, (BitString.uniformList n) r *
          ((BitString.uniformList n).map fun pad =>
            (r ++ List.zipWith xor (pad.take n)
              (if bit then dropFrame request.2 else unframe request.2),
              ((r, pad) :: cache, (cache.lookup r).isSome))).toOuterMeasure
            {x | x.2.2 = true}
        ≤ ∑' r, (BitString.uniformList n) r *
            {r : List Bool | (cache.lookup r).isSome}.indicator 1 r := by
          refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
          by_cases hr : (cache.lookup r).isSome = true
          · rw [Set.indicator_of_mem (show r ∈ {r : List Bool | (cache.lookup r).isSome} from hr),
              Pi.one_apply]
            exact Probability.PMF.toOuterMeasure_le_one _ _
          · rw [Set.indicator_of_notMem
              (show r ∉ {r : List Bool | (cache.lookup r).isSome} from hr)]
            refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_)
            refine Set.disjoint_left.mpr fun x hx hbad => ?_
            obtain ⟨pad, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
            exact hr hbad
      _ = (BitString.uniformList n).toOuterMeasure {r | (cache.lookup r).isSome} := by
          rw [PMF.toOuterMeasure_apply]
          refine tsum_congr fun r => ?_
          by_cases hr : (cache.lookup r).isSome = true
          · rw [Set.indicator_of_mem (show r ∈ {r : List Bool | (cache.lookup r).isSome} from hr),
              Set.indicator_of_mem (show r ∈ {r : List Bool | (cache.lookup r).isSome} from hr),
              Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem
              (show r ∉ {r : List Bool | (cache.lookup r).isSome} from hr),
              Set.indicator_of_notMem
              (show r ∉ {r : List Bool | (cache.lookup r).isSome} from hr), mul_zero]
      _ ≤ (cache.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ n) :=
          BitString.toOuterMeasure_lookup_uniformList_le n cache
  · simp [hlenEq]

private theorem length_cache_prfCipherForgetfulWithBadOracle_le (n : ℕ) (bit : Bool)
    (request : Unit × List Bool) (cache : List (List Bool × List Bool)) (bad : Bool)
    (x : List Bool × (List (List Bool × List Bool) × Bool))
    (hx : x ∈ (prfCipherForgetfulWithBadOracle n bit request (cache, bad)).support) :
    x.2.1.length ≤ cache.length + 1 := by
  unfold prfCipherForgetfulWithBadOracle at hx
  by_cases hlenEq : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
  · simp only [hlenEq, ↓reduceIte] at hx
    obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨pad, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    simp
  · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at hx
    subst x
    exact Nat.le_succ _

private theorem bad_prfCipherForgetfulWithBadOracle_le {α : Type} (n : ℕ) (bit : Bool)
    {program : WordOracleComp Unit α} {Q : ℕ} (hq : program.IsQueryBounded Q)
    (cache : List (List Bool × List Bool)) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (prfCipherForgetfulWithBadOracle n bit))
      program).run (cache, false)).toOuterMeasure {x | x.2.2 = true} ≤
      (Q : ℝ≥0∞) * ((cache.length + Q : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ n) := by
  induction hq generalizing cache with
  | pure a Q =>
    simp [Probability.PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
  | liftBind q cont Q _ ih =>
    classical
    simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply]
    cases q with
    | inl m =>
      simp only [Sum.elim_inl, Nat.add_zero]
      set B : ℝ≥0∞ := (Q : ℝ≥0∞) * ((cache.length + Q : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ n)
      calc ∑' y, ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
              (prfCipherForgetfulWithBadOracle n bit) (Sum.inl m) (cache, false) y *
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                (prfCipherForgetfulWithBadOracle n bit))
              (cont y.1)).run y.2).toOuterMeasure {x | x.2.2 = true}
          ≤ ∑' y, ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
              (prfCipherForgetfulWithBadOracle n bit) (Sum.inl m) (cache, false) y * B := by
            refine tsum_le_tsum fun y => ?_
            by_cases hy : y ∈ (ProbOracleComp.handler
                (fun m => StateT.lift (ProbComp.unifOracle m))
                (prfCipherForgetfulWithBadOracle n bit) (Sum.inl m) (cache, false)).support
            · change y ∈ ((ProbComp.unifOracle m).map (·, (cache, false))).support at hy
              obtain ⟨val, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
              exact mul_le_mul_of_nonneg_left (ih val cache) zero_le
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hy, zero_mul, zero_mul]
        _ = B := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    | inr request =>
      simp only [Sum.elim_inr]
      set δ : ℝ≥0∞ := (1 : ℝ≥0∞) / 2 ^ n
      set M : ℝ≥0∞ := ((cache.length + (Q + 1) : ℕ) : ℝ≥0∞) * δ
      set K : ℝ≥0∞ := (Q : ℝ≥0∞) * M
      have hterm (y : List Bool × (List (List Bool × List Bool) × Bool)) :
          prfCipherForgetfulWithBadOracle n bit request (cache, false) y *
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                (prfCipherForgetfulWithBadOracle n bit))
              (cont y.1)).run y.2).toOuterMeasure {x | x.2.2 = true} ≤
          prfCipherForgetfulWithBadOracle n bit request (cache, false) y *
            ({x : List Bool × (List (List Bool × List Bool) × Bool) | x.2.2 = true}.indicator 1 y +
              K) := by
        by_cases hmem : y ∈ (prfCipherForgetfulWithBadOracle n bit request (cache, false)).support
        · refine mul_le_mul_of_nonneg_left ?_ zero_le
          by_cases hy : y.2.2 = true
          · rw [Set.indicator_of_mem
              (show y ∈ {x : List Bool × (List (List Bool × List Bool) × Bool) | x.2.2 = true}
                from hy), Pi.one_apply]
            exact (Probability.PMF.toOuterMeasure_le_one _ _).trans le_self_add
          · rw [Set.indicator_of_notMem
              (show y ∉ {x : List Bool × (List (List Bool × List Bool) × Bool) | x.2.2 = true}
                from hy), zero_add]
            have hyF : y.2.2 = false := Bool.eq_false_iff.mpr hy
            have hyState : y.2 = (y.2.1, false) := Prod.ext rfl hyF
            rw [hyState]
            refine (ih y.1 y.2.1).trans ?_
            have hgrow := length_cache_prfCipherForgetfulWithBadOracle_le n bit request cache
              false y hmem
            have hlenLe : y.2.1.length + Q ≤ cache.length + (Q + 1) := by lia
            simp only [K, M, mul_assoc]
            gcongr
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, zero_mul, zero_mul]
      calc ∑' y, prfCipherForgetfulWithBadOracle n bit request (cache, false) y *
              ((OracleComp.interpret
                (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                  (prfCipherForgetfulWithBadOracle n bit))
                (cont y.1)).run y.2).toOuterMeasure {x | x.2.2 = true}
          ≤ ∑' y, prfCipherForgetfulWithBadOracle n bit request (cache, false) y *
              ({x : List Bool × (List (List Bool × List Bool) × Bool) |
                x.2.2 = true}.indicator 1 y + K) :=
            tsum_le_tsum hterm
        _ = (prfCipherForgetfulWithBadOracle n bit request (cache, false)).toOuterMeasure
              {x | x.2.2 = true} + K := by
            simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe,
              one_mul, PMF.toOuterMeasure_apply]
            congr 1
            refine tsum_congr fun y => ?_
            by_cases hy : y.2.2 = true
            · rw [Set.indicator_of_mem
                (show y ∈ {x : List Bool × (List (List Bool × List Bool) × Bool) | x.2.2 = true}
                  from hy),
                Set.indicator_of_mem
                (show y ∈ {x : List Bool × (List (List Bool × List Bool) × Bool) | x.2.2 = true}
                  from hy),
                Pi.one_apply, mul_one]
            · rw [Set.indicator_of_notMem
                (show y ∉ {x : List Bool × (List (List Bool × List Bool) × Bool) | x.2.2 = true}
                  from hy),
                Set.indicator_of_notMem
                (show y ∉ {x : List Bool × (List (List Bool × List Bool) × Bool) | x.2.2 = true}
                  from hy), mul_zero]
        _ ≤ M + K := by
            refine add_le_add ?_ le_rfl
            refine (step_bad_prfCipherForgetfulWithBadOracle_le n bit request cache).trans ?_
            simp only [M]
            gcongr
            exact Nat.le_add_right _ _
        _ = ((Q + 1 : ℕ) : ℝ≥0∞) * ((cache.length + (Q + 1) : ℕ) : ℝ≥0∞) * δ := by
            simp only [K, M, Nat.cast_add, Nat.cast_one]
            ring

private theorem advantage_prfIdealGame_prfCipherOTPOracle_le (adversary : OracleDistinguisher)
    (bit : Bool) (n Q : ℕ) (hq : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
      (ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher adversary bit) n))
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (prfCipherOTPOracle n))
        (adversary n [])).run ()).map Prod.fst) : ℝ) ≤
      (Q : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  rw [eval_prfIdealGame_cpaToPrfDistinguisher,
    ← run_prfCipherForgetfulWithBadOracle_map_fst adversary bit n [] false]
  have hiub := identicalUntilBad_prfCipherFaithful_forgetful n bit
  have hadv := hiub.advantage_le (adversary n []) ([], false) (fun out => PMF.pure out.1)
  change (Game.advantage
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (prfCipherFaithfulWithBadOracle n bit))
        (adversary n [])).run ([], false)).map Prod.fst)
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (prfCipherForgetfulWithBadOracle n bit))
        (adversary n [])).run ([], false)).map Prod.fst) : ℝ) ≤ _ at hadv
  rw [hiub.bad_eq] at hadv
  have hbad := bad_prfCipherForgetfulWithBadOracle_le n bit hq []
  simp only [List.length_nil, zero_add] at hbad
  have htop : (Q : ℝ≥0∞) * (Q : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ n) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top Q)
      (ENNReal.natCast_ne_top Q)) ?_
    exact ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
  have hreal := ENNReal.toReal_mono htop hbad
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hreal
  refine hadv.trans (hreal.trans (le_of_eq ?_))
  ring

/-- **Quantitative IND-CPA security bound for `prfCipher`** ([BonehShoup2023], Section 5.4.1,
Theorem 5.2, equation (5.5), printed pp. 184–189): for any `OracleDistinguisher` making at most `Q`
encryption queries at security parameter `n`, the CPA distinguishing advantage against `prfCipher`
is bounded by the sum of the PRF distinguishing advantages of
`cpaToPrfDistinguisher adversary false` and `cpaToPrfDistinguisher adversary true` plus
`2 * Q^2 / 2^n` (where `2 * Q^2 / 2^n` is a factor-`2` loosening of the source's `Q^2 / N =
Q^2 / 2^n` collision term from equation (5.11) on printed p. 187, arising from the `Q * Q / 2^n`
union bound per challenge bit in `bad_prfCipherForgetfulWithBadOracle_le`). -/
theorem advantage_cpaGame_prfCipher_le (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) (n Q : ℕ) (hq : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
      (ProbComp.eval ((prfCipher family hpoly hlen).cpaGame adversary false n))
      (ProbComp.eval ((prfCipher family hpoly hlen).cpaGame adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (cpaToPrfDistinguisher adversary false) n))
        (ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher adversary false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (cpaToPrfDistinguisher adversary true) n))
        (ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher adversary true) n)) : ℝ) +
      2 * (Q : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  rw [← eval_prfRealGame_cpaToPrfDistinguisher family hpoly hlen adversary false n,
    ← eval_prfRealGame_cpaToPrfDistinguisher family hpoly hlen adversary true n]
  let pReal0 := ProbComp.eval (prfRealGame family (cpaToPrfDistinguisher adversary false) n)
  let pIdeal0 := ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher adversary false) n)
  let pReal1 := ProbComp.eval (prfRealGame family (cpaToPrfDistinguisher adversary true) n)
  let pIdeal1 := ProbComp.eval (prfIdealGame (cpaToPrfDistinguisher adversary true) n)
  let pOTP := ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
      (prfCipherOTPOracle n))
    (adversary n [])).run ()).map Prod.fst
  change (Game.advantage pReal0 pReal1 : ℝ) ≤
    (Game.advantage pReal0 pIdeal0 : ℝ) + (Game.advantage pReal1 pIdeal1 : ℝ) +
      2 * (Q : ℝ) ^ 2 / (2 : ℝ) ^ n
  have h1 : (Game.advantage pReal0 pReal1 : ℝ) ≤
      (Game.advantage pReal0 pIdeal0 : ℝ) + (Game.advantage pIdeal0 pReal1 : ℝ) := by
    exact_mod_cast Game.advantage_triangle pReal0 pIdeal0 pReal1
  have h2 : (Game.advantage pIdeal0 pReal1 : ℝ) ≤
      (Game.advantage pIdeal0 pOTP : ℝ) + (Game.advantage pOTP pReal1 : ℝ) := by
    exact_mod_cast Game.advantage_triangle pIdeal0 pOTP pReal1
  have h3 : (Game.advantage pOTP pReal1 : ℝ) ≤
      (Game.advantage pOTP pIdeal1 : ℝ) + (Game.advantage pIdeal1 pReal1 : ℝ) := by
    exact_mod_cast Game.advantage_triangle pOTP pIdeal1 pReal1
  have hcomm1 : (Game.advantage pOTP pIdeal1 : ℝ) = (Game.advantage pIdeal1 pOTP : ℝ) := by
    rw [Game.advantage_comm]
  have hcomm2 : (Game.advantage pIdeal1 pReal1 : ℝ) = (Game.advantage pReal1 pIdeal1 : ℝ) := by
    rw [Game.advantage_comm]
  have hfalse : (Game.advantage pIdeal0 pOTP : ℝ) ≤ (Q : ℝ) ^ 2 / (2 : ℝ) ^ n :=
    advantage_prfIdealGame_prfCipherOTPOracle_le adversary false n Q hq
  have htrue : (Game.advantage pIdeal1 pOTP : ℝ) ≤ (Q : ℝ) ^ 2 / (2 : ℝ) ^ n :=
    advantage_prfIdealGame_prfCipherOTPOracle_le adversary true n Q hq
  have h2Q : 2 * (Q : ℝ) ^ 2 / (2 : ℝ) ^ n =
      (Q : ℝ) ^ 2 / (2 : ℝ) ^ n + (Q : ℝ) ^ 2 / (2 : ℝ) ^ n := by ring
  linarith

/-- **Any secure `PseudorandomFunction` yields an `INDCPA`-secure symmetric cipher `prfCipher`**
([BonehShoup2023], Section 5.4.1, Example 5.2 and Theorem 5.2, printed pp. 183–189). -/
theorem PseudorandomFunction.indcpa_prfCipher
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfCipher family hprf.polyTime hprf.length_eq).INDCPA := by
  intro adversary hadversary
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
    simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hprfFalse := hprf.secure (cpaToPrfDistinguisher adversary false)
    (isOraclePPT_cpaToPrfDistinguisher hadversary false)
  have hprfTrue := hprf.secure (cpaToPrfDistinguisher adversary true)
    (isOraclePPT_cpaToPrfDistinguisher hadversary true)
  have hpolyQ : PolynomiallyBounded (fun n => 2 * (Q n) ^ 2) := by
    dsimp only [Q]; fun_prop
  have hcollNeg :=
    (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)).polynomiallyBounded_mul hpolyQ
  have hsumNeg := (hprfFalse.add hprfTrue).add hcollNeg
  refine negligible_of_le hsumNeg fun n => ?_
  rw [← NNReal.coe_le_coe]
  have hbound := advantage_cpaGame_prfCipher_le family hprf.polyTime hprf.length_eq
    adversary n (Q n) (hq n)
  simpa only [Pi.add_apply, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
    NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    one_div, one_mul, inv_pow, div_eq_mul_inv, mul_assoc] using hbound

/-! #### End-to-End Non-Vacuous PRF Encrypt-then-MAC Instance -/

/-- **Concrete PRF-based Encrypt-then-MAC cipher** combining `prfCipher` (`2 * n`-bit ciphertexts on
`n`-bit plaintexts) with
`(prfMAC family hpoly).reindex (fun n => 2 * n) ((by polytime))`
(authenticating `2 * n`-bit ciphertexts at security parameter `n`). -/
noncomputable def prfEncryptThenMAC (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    SymmetricCipher :=
  encryptThenMAC
    (prfCipher family hpoly hlen)
    ((prfMAC family hpoly).reindex (fun n => 2 * n) ((by polytime)))
    (prfCipher_ciphertext_length family hpoly hlen)

/-- **End-to-end non-vacuity of `authenticatedEncryption_encryptThenMAC`**: for any secure
`PseudorandomFunction family`, `prfEncryptThenMAC` satisfies `AuthenticatedEncryption`, with all
hypotheses (`hctLen`, `INDCPA`, and `SUFCMA`) discharged simultaneously from `hprf`. -/
theorem PseudorandomFunction.authenticatedEncryption_prfEncryptThenMAC
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).AuthenticatedEncryption :=
  authenticatedEncryption_encryptThenMAC_prfMAC
    (prfCipher family hprf.polyTime hprf.length_eq)
    hprf ((by polytime)) (strictMono_mul_left_of_pos two_pos)
    (prfCipher_ciphertext_length family hprf.polyTime hprf.length_eq)
    hprf.indcpa_prfCipher

/-- **End-to-end non-vacuity of `indcca_encryptThenMAC` and `AuthenticatedEncryption.indcca`**:
for any secure `PseudorandomFunction family`, `prfEncryptThenMAC` satisfies adaptive
chosen-ciphertext security (`INDCCA`), with all hypotheses discharged simultaneously from `hprf`. -/
theorem PseudorandomFunction.indcca_prfEncryptThenMAC
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).INDCCA :=
  hprf.authenticatedEncryption_prfEncryptThenMAC.indcca

end Cslib.Crypto
