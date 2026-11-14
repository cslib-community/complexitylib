/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
public import CslibFrontier.Crypto.Computational.GeneratorReindex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen

/-!
# MAC-then-Encrypt Composition and Chosen-Ciphertext Counterexample

This module formalizes the generic **MAC-then-Encrypt** symmetric encryption construction
(`macThenEncrypt`), proves that it preserves `INDCPA` (`indcpa_macThenEncrypt`), and gives an
explicit counterexample showing that generic MAC-then-Encrypt does not achieve chosen-ciphertext
security (`INDCCA` or `OneTimeINDCCA`) or ciphertext integrity (`CiphertextIntegrity`), even when
the underlying cipher is `INDCPA`-secure and the MAC is `SUFCMA`-secure ([KatzLindell2020],
Section 5.2; [BonehShoup2023], Section 9.4.1).

1. **Generic MAC-then-Encrypt construction (`macThenEncrypt`) and `INDCPA` preservation**: given a
   symmetric cipher `E`, a MAC scheme `M` authenticating `n`-bit messages (`M.msgLen n = n`), and
   a polynomial-time length schedule `ptLen : ℕ → ℕ` such that every encoded `(msg, tag)` pair on
   an `n`-bit message has length `ptLen n`, `macThenEncrypt E M ptLen ...` generates keys at
   `(ptLen n, n)` and encrypts/decrypts the framed `(msg, tag)` pair under `E` at security
   parameter `ptLen n`, discharging decryption completeness directly from `E.decrypt_encrypt`.
   When `ptLen` is strictly monotone and `E` is `INDCPA`, `macThenEncrypt` is `INDCPA`
   (`indcpa_macThenEncrypt`).
2. **Malleable CPA-preserving cipher extension (`extendCipher`)**: appends `false` to every
   ciphertext on encryption and ignores the last bit (`ct.take (ct.length - 1)`) during
   decryption. We prove `extendCipher` preserves `INDCPA` (`INDCPA.extendCipher`) and
   `OneTimeINDCPA` (`OneTimeINDCPA.extendCipher`).
3. **Explicit CI/CCA attack and PRF instantiation (`macThenEncrypt_extendCipher_counterexample`,
   `prfMacThenEncryptExtend_counterexample`)**: replacing the trailing `false` bit of any ciphertext
   with `true` yields a distinct ciphertext with identical decryption under
   `macThenEncrypt E.extendCipher M ptLen ...`, breaking `OneTimeINDCCA` and `INDCCA` with exact
   advantage `1` for every `n ≥ 1` and `CiphertextIntegrity` with probability `1`. Combining with
   `indcpa_macThenEncrypt` and instantiating on `(prfCipher ...).extendCipher` + `prfMAC ...` gives
   a non-vacuous counterexample from any `PseudorandomFunction`.

## Main definitions

* `Cslib.Crypto.macThenEncrypt`: MAC-then-Encrypt symmetric cipher with plaintext-tag length
  schedule `ptLen`.
* `Cslib.Crypto.mteToCPAHandler`, `Cslib.Crypto.mteToCPAAdversary`: `INDCPA` reduction from
  `macThenEncrypt` at `n` to `E` at `ptLen n`.
* `Cslib.Crypto.SymmetricCipher.extendCipher`: trailing-bit malleable symmetric cipher extension.
* `Cslib.Crypto.SymmetricCipher.extendCPAAdversary`,
  `Cslib.Crypto.SymmetricCipher.extendOneTimeCPAAdversary`: CPA reductions to `E`.
* `Cslib.Crypto.macThenEncryptExtendCCAAdversary`: two-query CCA distinguisher against
  `macThenEncrypt E.extendCipher M ptLen ...`.
* `Cslib.Crypto.macThenEncryptExtendCIAdversary`: one-query CI adversary against
  `macThenEncrypt E.extendCipher M ptLen ...`.
* `Cslib.Crypto.prfMacThenEncryptExtend`: end-to-end PRF-backed counterexample cipher at
  `ptLen n = 3 * n + 1`.

## Main results

* `Cslib.Crypto.indcpa_macThenEncrypt`: `E.INDCPA` implies `INDCPA` for `macThenEncrypt` under a
  strictly monotone polynomial-time `ptLen`.
* `Cslib.Crypto.SymmetricCipher.INDCPA.extendCipher`,
  `Cslib.Crypto.SymmetricCipher.OneTimeINDCPA.extendCipher`: `extendCipher` preserves `INDCPA` and
  `OneTimeINDCPA`.
* `Cslib.Crypto.advantage_ccaOneTimeGame_macThenEncrypt_extendCipher_eq_one`: the explicit CCA
  attacker achieves exact distinguishing advantage `1` against `macThenEncrypt E.extendCipher M`
  for all `n ≥ 1`.
* `Cslib.Crypto.not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher`,
  `Cslib.Crypto.not_ciphertextIntegrity_macThenEncrypt_extendCipher`,
  `Cslib.Crypto.not_oneTimeINDCCA_macThenEncrypt_extendCipher`,
  `Cslib.Crypto.not_indcca_macThenEncrypt_extendCipher`: `macThenEncrypt E.extendCipher M` fails
  one-time/adaptive ciphertext integrity and CCA security.
* `Cslib.Crypto.macThenEncrypt_extendCipher_counterexample`,
  `Cslib.Crypto.PseudorandomFunction.prfMacThenEncryptExtend_counterexample`: joint separation
  theorems witnessing `E'.INDCPA`, `M.SUFCMA`, composed `INDCPA`, and all four negative bounds.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 5.2 (MAC-then-Encrypt).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 9.4.1.
-/

public section

namespace Cslib.Crypto

open Cslib.Probability ProbComp OracleComp BitString Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- **MAC-then-Encrypt symmetric cipher**: signs `n`-bit messages under `km ← M.keyGen n` and
encrypts the framed pair `encPair encBits encBits (msg, tag)` under `ke ← E.keyGen (ptLen n)` at
security parameter `ptLen n`. Because `hpairLen` guarantees the framed `(msg, tag)` pair has length
`ptLen n`, decryption completeness follows directly from `E.decrypt_encrypt (ptLen n)`. -/
@[expose]
noncomputable def macThenEncrypt (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n) : SymmetricCipher where
  keyGen n := do
    let ke ← E.keyGen (ptLen n)
    let km ← M.keyGen n
    return encPair encBits encBits (ke, km)
  encrypt n k msg := do
    let tag ← M.sign (dropFrame k) msg
    E.encrypt (ptLen n) (unframe k) (encPair encBits encBits (msg, tag))
  decrypt n k ct :=
    (E.decrypt (ptLen n) (unframe k) ct).elim none fun p =>
      let msg := unframe p
      let tag := dropFrame p
      if (encPair encBits encBits (msg, tag) == p) && (msg.length == M.msgLen n) &&
          M.verify (dropFrame k) msg tag then
        some msg
      else
        none
  keyGen_ppt := by
    have hpt := hptLenPoly.tidy
    ppt
  encrypt_ppt := by
    have hpt := hptLenPoly.tidy
    ppt
  decrypt_polyTime := by
    let EDecIn := encPair encUnary (encPair encBits encBits)
    let EBIn := encPair EDecIn encBits
    have hn : ComputableTidilyInPolyTime (fun a : ℕ × List Bool × List Bool => a.1)
        EDecIn encUnary := by dsimp only [EDecIn]; fun_prop
    have hk : ComputableTidilyInPolyTime (fun a : ℕ × List Bool × List Bool => a.2.1)
        EDecIn encBits := by dsimp only [EDecIn]; fun_prop
    have hct : ComputableTidilyInPolyTime (fun a : ℕ × List Bool × List Bool => a.2.2)
        EDecIn encBits := by dsimp only [EDecIn]; fun_prop
    have hdec : ComputableTidilyInPolyTime
        (fun a : ℕ × List Bool × List Bool => E.decrypt (ptLen a.1) (unframe a.2.1) a.2.2)
        EDecIn (encOption encBits) :=
      E.decrypt_polyTime.tidy.comp
        ((hptLenPoly.tidy.comp hn).prod ((ComputableTidilyInPolyTime.unframe.comp hk).prod hct))
    have hnone : ComputableTidilyInPolyTime
        (fun _ : ℕ × List Bool × List Bool => (none : Option (List Bool)))
        EDecIn (encOption encBits) := ComputableTidilyInPolyTime.const none
    have q_n : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool => q.1.1)
        EBIn encUnary := hn.comp (ComputableTidilyInPolyTime.fst _ _)
    have q_km : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool => dropFrame q.1.2.1)
        EBIn encBits :=
      ComputableTidilyInPolyTime.dropFrame.comp (hk.comp (ComputableTidilyInPolyTime.fst _ _))
    have q_p : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool => q.2)
        EBIn encBits := ComputableTidilyInPolyTime.snd _ _
    have q_msg : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool => unframe q.2)
        EBIn encBits := ComputableTidilyInPolyTime.unframe.comp q_p
    have q_tag : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool => dropFrame q.2)
        EBIn encBits := ComputableTidilyInPolyTime.dropFrame.comp q_p
    have hframeEq : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool =>
          encPair encBits encBits (unframe q.2, dropFrame q.2) == q.2)
        EBIn encBool :=
      (q_msg.prod q_tag).encoded.beq q_p
    have hmsgLenPoly : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool =>
          (unframe q.2).length == M.msgLen q.1.1)
        EBIn encBool :=
      ((by fun_prop : ComputableTidilyInPolyTime (fun x : List Bool => x.length)
        encBits encUnary).comp q_msg).beq (M.msgLen_polyTime.tidy.comp q_n)
    have hverPoly : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool =>
          M.verify (dropFrame q.1.2.1) (unframe q.2) (dropFrame q.2))
        EBIn encBool :=
      M.verify_polyTime.tidy.comp (q_km.prod (q_msg.prod q_tag))
    have hbody : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool =>
          let msg := unframe q.2
          let tag := dropFrame q.2
          if (encPair encBits encBits (msg, tag) == q.2) && (msg.length == M.msgLen q.1.1) &&
              M.verify (dropFrame q.1.2.1) msg tag then
            some msg
          else
            none)
        EBIn (encOption encBits) :=
      ((hframeEq.bool_and' hmsgLenPoly).bool_and' hverPoly).cond
        ((ComputableTidilyInPolyTime.optionSome encBits).comp q_msg)
        (ComputableTidilyInPolyTime.const none)
    exact (hdec.optionElimWithInput hnone hbody).computableInPolyTime
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hk hct
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
    rw [unframe_encPair_encBits, dropFrame_encPair_encBits] at hct
    obtain ⟨tag, htag, hct2⟩ := hct
    have hdec : E.decrypt (ptLen n) ke ct = some (encPair encBits encBits (msg, tag)) :=
      E.decrypt_encrypt (ptLen n) ke hke (encPair encBits encBits (msg, tag))
        (hpairLen n km hkm msg hmsg tag htag) ct hct2
    have hmLen : msg.length = M.msgLen n := hmsg.trans (hmsgLen n).symm
    have hver : M.verify km msg tag = true := M.verify_sign n km hkm msg hmLen tag htag
    rw [unframe_encPair_encBits, dropFrame_encPair_encBits, hdec]
    simp only [Option.elim_some]
    rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
    simp [hmLen, hver]

/-! ### IND-CPA Preservation for MAC-then-Encrypt -/

/-- Oracle handler used by `mteToCPAAdversary` to simulate the CPA oracle of `macThenEncrypt E M
ptLen` against `E`'s CPA oracle at parameter `ptLen n`. On valid `n`-bit message pairs
`(m0, m1)`, it signs both messages under `km` and forwards the pair of framed `(msg, tag)` pairs
to `E`'s CPA oracle, truncating the reply to `ctCap` bits. -/
noncomputable def mteToCPAHandler (M : MACScheme) (n ctCap : ℕ) (km : List Bool)
    (request : Unit × List Bool) : WordOracleComp Unit (List Bool) :=
  let m0 := unframe request.2
  let m1 := dropFrame request.2
  if (m0.length == n) && (m1.length == n) then do
    let tag0 ← ProbOracleComp.sample (M.sign km m0)
    let tag1 ← ProbOracleComp.sample (M.sign km m1)
    let p0 := encPair encBits encBits (m0, tag0)
    let p1 := encPair encBits encBits (m1, tag1)
    List.take ctCap <$> ProbOracleComp.query ((), encPair encBits encBits (p0, p1))
  else
    pure []

/-- Reduction from `cpaGame` on `macThenEncrypt E M ptLen` (at security parameter `n`) to `cpaGame`
on `E` (at security parameter `m = ptLen n`): recovers `n := GeneratorReindex.parameter ptLen m`,
checks `ptLen n == m`, samples a MAC key `km ← M.keyGen n`, and interprets `adversary n []` via
`mteToCPAHandler`. -/
noncomputable def mteToCPAAdversary (M : MACScheme) (ptLen ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) : OracleDistinguisher :=
  fun m _ =>
    let n := GeneratorReindex.parameter ptLen m
    if ptLen n == m then do
      let km ← ProbOracleComp.sample (M.keyGen n)
      OracleComp.interpret
        (OracleComp.sumHandler (fun u => ProbOracleComp.sample (ProbComp.unifFin u))
          (mteToCPAHandler M n (ctBound m) km))
        (adversary n [])
    else
      pure false

/-- `mteToCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_mteToCPAAdversary (M : MACScheme) (ptLen ctBound : ℕ → ℕ)
    (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hctBoundPoly : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (mteToCPAAdversary M ptLen ctBound adversary) := by
  have hparam : ComputableInPolyTime (GeneratorReindex.parameter ptLen) encUnary encUnary :=
    GeneratorReindex.isPolyTime_parameter hptLenPoly .id'
  let ECaller := encPair encUnary encBits
  let EStateCaller := encPair ECaller encBits
  let EHandlerIn := encPair EStateCaller (encPair (encFinEnum Unit) encBits)
  have hparamT := hparam.tidy
  have hctT := hctBoundPoly.tidy
  have hcond : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (Unit × List Bool) =>
        ((unframe p.2.2).length == GeneratorReindex.parameter ptLen p.1.1.1) &&
          ((dropFrame p.2.2).length == GeneratorReindex.parameter ptLen p.1.1.1))
      EHandlerIn encBool :=
    (by dsimp only [EHandlerIn, EStateCaller, ECaller]; fun_prop :
      ComputableTidilyInPolyTime _ EHandlerIn encBool).computableInPolyTime
  have hyes : IsOraclePPTOn EHandlerIn encBits
      (fun p : ((ℕ × List Bool) × List Bool) × (Unit × List Bool) => do
        let tag0 ← ProbOracleComp.sample (M.sign p.1.2 (unframe p.2.2))
        let tag1 ← ProbOracleComp.sample (M.sign p.1.2 (dropFrame p.2.2))
        let p0 := encPair encBits encBits (unframe p.2.2, tag0)
        let p1 := encPair encBits encBits (dropFrame p.2.2, tag1)
        List.take (ctBound p.1.1.1) <$>
          ProbOracleComp.query ((), encPair encBits encBits (p0, p1))) := by
    dsimp only [EHandlerIn, EStateCaller, ECaller]
    ppt
  have hno : IsOraclePPTOn EHandlerIn encBits
      (fun _ : ((ℕ × List Bool) × List Bool) × (Unit × List Bool) =>
        (pure [] : WordOracleComp Unit (List Bool))) :=
    (ComputableInPolyTime.const ([] : List Bool)).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EHandlerIn encBits
      (fun p : ((ℕ × List Bool) × List Bool) × (Unit × List Bool) =>
        mteToCPAHandler M (GeneratorReindex.parameter ptLen p.1.1.1) (ctBound p.1.1.1)
          p.1.2 p.2) := by
    unfold mteToCPAHandler
    exact IsOraclePPTOn.cond' hcond hyes hno
  have hprepare : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        (GeneratorReindex.parameter ptLen p.1.1, ([] : List Bool)))
      EStateCaller ECaller := by
    dsimp only [EStateCaller, ECaller]
    exact ((hparam.comp ((ComputableInPolyTime.fst encUnary encBits).comp
      (ComputableInPolyTime.fst ECaller encBits))).prod
      (ComputableInPolyTime.const ([] : List Bool)))
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => ctBound pair.1.1.1)
      (encPair EStateCaller encBits) encUnary :=
    hctBoundPoly.comp
      ((ComputableInPolyTime.fst encUnary encBits).comp
        ((ComputableInPolyTime.fst ECaller encBits).comp
          (ComputableInPolyTime.fst EStateCaller encBits)))
  have hrun : IsOraclePPTOn (Operation := Unit) EStateCaller encBool
      (fun p : (ℕ × List Bool) × List Bool =>
        OracleComp.interpret
          (OracleComp.sumHandler (fun u => ProbOracleComp.sample (ProbComp.unifFin u))
            (mteToCPAHandler M (GeneratorReindex.parameter ptLen p.1.1) (ctBound p.1.1) p.2))
          (adversary (GeneratorReindex.parameter ptLen p.1.1) [])) := by
    refine hadversary.interpret_preprocess_open'
      (prepare := fun p : (ℕ × List Bool) × List Bool =>
        (GeneratorReindex.parameter ptLen p.1.1, ([] : List Bool)))
      (resources := fun p _ => ctBound p.1.1)
      hprepare hhandler hres fun p request reply hreply => ?_
    unfold mteToCPAHandler at hreply
    dsimp only at hreply
    split_ifs at hreply with hlenEq
    · obtain ⟨tag0, _, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
      obtain ⟨tag1, _, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
      obtain ⟨ct, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact List.length_take_le _ _
    · cases OracleComp.eq_of_mem_supportWith_pure hreply
      exact Nat.zero_le _
  have hkm : IsOraclePPTOn (Operation := Unit) ECaller encBits
      (fun caller : ℕ × List Bool =>
        ProbOracleComp.sample (M.keyGen (GeneratorReindex.parameter ptLen caller.1))) :=
    (M.keyGen_ppt.preprocess
      (hparam.comp (ComputableInPolyTime.fst encUnary encBits))).isOraclePPTOn
  have hbody : IsOraclePPTOn (Operation := Unit) ECaller encBool
      (fun caller : ℕ × List Bool => do
        let km ← ProbOracleComp.sample (M.keyGen (GeneratorReindex.parameter ptLen caller.1))
        OracleComp.interpret
          (OracleComp.sumHandler (fun u => ProbOracleComp.sample (ProbComp.unifFin u))
            (mteToCPAHandler M (GeneratorReindex.parameter ptLen caller.1) (ctBound caller.1) km))
          (adversary (GeneratorReindex.parameter ptLen caller.1) [])) :=
    hkm.bind_with hrun
  have houterCond : ComputableInPolyTime
      (fun caller : ℕ × List Bool => ptLen (GeneratorReindex.parameter ptLen caller.1) == caller.1)
      ECaller encBool := by
    have hptT := hptLenPoly.tidy
    dsimp only [ECaller]
    exact (by fun_prop : ComputableTidilyInPolyTime _ ECaller encBool).computableInPolyTime
  have houterNo : IsOraclePPTOn (Operation := Unit) ECaller encBool
      (fun _ : ℕ × List Bool => (pure false : WordOracleComp Unit Bool)) :=
    (ComputableInPolyTime.const false).isOraclePPTOn (Operation := Unit)
  unfold mteToCPAAdversary
  exact (IsOraclePPTOn.cond' houterCond hbody houterNo).isOraclePPT

/-- When `ptLen` is strictly monotone and `ctBound (ptLen n)` bounds all ciphertexts produced by
`E.encrypt (ptLen n)` on `ptLen n`-bit plaintexts under supported keys, `E.cpaGame` running
`mteToCPAAdversary` at security parameter `ptLen n` has the exact same output distribution as
`(macThenEncrypt E M ptLen ...).cpaGame` running `adversary` at `n`. -/
theorem eval_cpaGame_mteToCPAAdversary (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmono : StrictMono ptLen) (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (ctBound : ℕ → ℕ) (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE (ptLen n) (ctBound (ptLen n))) :
    ProbComp.eval (E.cpaGame (mteToCPAAdversary M ptLen ctBound adversary) bit (ptLen n)) =
      ProbComp.eval
        ((macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).cpaGame adversary bit n) := by
  simp only [SymmetricCipher.cpaGame, mteToCPAAdversary,
    GeneratorReindex.parameter_apply_of_strictMono hmono n, beq_self_eq_true, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure]
  have hkeyGen : ProbComp.eval
      ((macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).keyGen n) =
      (ProbComp.eval (E.keyGen (ptLen n))).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [macThenEncrypt, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hkeyGen]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
  simp only [ProbOracleComp.eval_run_interpret_eq_runWith]
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample]
  simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun km hkm => ?_
  simp only [ProbOracleComp.runWith_interpret_sumHandler]
  have horacle :
      (fun q => ProbOracleComp.runWith
          (fun q' s' => ProbComp.eval (E.cpaEncryptionOracle (ptLen n) ke bit q' s'))
          (mteToCPAHandler M n (ctBound (ptLen n)) km q)) =
        (fun q s =>
          ProbComp.eval ((macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).cpaEncryptionOracle
            n (encPair encBits encBits (ke, km)) bit q s)) := by
    funext ⟨⟨⟩, req⟩ ⟨⟩
    simp only [mteToCPAHandler, SymmetricCipher.cpaEncryptionOracle]
    by_cases hcond : ((unframe req).length == n && (dropFrame req).length == n) = true
    · simp only [hcond, ↓reduceIte, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
        ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
        PMF.bind_map, Function.comp_def]
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rcases hcond with ⟨hm0, hm1⟩
      dsimp only [macThenEncrypt]
      rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind]
      have htagstep (tag0 : List Bool)
          (htag0 : tag0 ∈ (ProbComp.eval (M.sign km (unframe req))).support)
          (tag1 : List Bool)
          (htag1 : tag1 ∈ (ProbComp.eval (M.sign km (dropFrame req))).support) :
          ((unframe (encPair encBits encBits
              (encPair encBits encBits (unframe req, tag0),
               encPair encBits encBits (dropFrame req, tag1)))).length == ptLen n &&
            (dropFrame (encPair encBits encBits
              (encPair encBits encBits (unframe req, tag0),
               encPair encBits encBits (dropFrame req, tag1)))).length == ptLen n) = true := by
        rw [unframe_encPair_encBits, dropFrame_encPair_encBits,
          hpairLen n km hkm (unframe req) hm0 tag0 htag0,
          hpairLen n km hkm (dropFrame req) hm1 tag1 htag1]
        simp
      cases bit with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine PMF.bind_congr_on_support _ _ _ fun tag0 htag0 => ?_
        trans (ProbComp.eval (M.sign km (dropFrame req))).bind fun _ =>
          (ProbComp.eval (E.encrypt (ptLen n) ke
            (encPair encBits encBits (unframe req, tag0)))).bind
            fun ct => PMF.pure (ct, ())
        · refine PMF.bind_congr_on_support _ _ _ fun tag1 htag1 => ?_
          rw [htagstep tag0 htag0 tag1 htag1]
          simp only [↓reduceIte, unframe_encPair_encBits, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.map_bind, PMF.pure_map, Prod.map_apply, id_eq]
          refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
          have htake := hctBound ke hke _ (hpairLen n km hkm _ hm0 tag0 htag0) ct hct
          rw [List.take_of_length_le htake]
        · exact PMF.bind_const _ _
      | true =>
        simp only [↓reduceIte]
        trans (ProbComp.eval (M.sign km (unframe req))).bind fun _ =>
          (ProbComp.eval (M.sign km (dropFrame req))).bind fun tag1 =>
            (ProbComp.eval (E.encrypt (ptLen n) ke
              (encPair encBits encBits (dropFrame req, tag1)))).bind fun ct =>
              PMF.pure (ct, ())
        · refine PMF.bind_congr_on_support _ _ _ fun tag0 htag0 => ?_
          refine PMF.bind_congr_on_support _ _ _ fun tag1 htag1 => ?_
          rw [htagstep tag0 htag0 tag1 htag1]
          simp only [↓reduceIte, dropFrame_encPair_encBits, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.map_bind, PMF.pure_map, Prod.map_apply, id_eq]
          refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
          have htake := hctBound ke hke _ (hpairLen n km hkm _ hm1 tag1 htag1) ct hct
          rw [List.take_of_length_le htake]
        · exact PMF.bind_const _ _
    · have hcondF : ((unframe req).length == n && (dropFrame req).length == n) = false :=
        Bool.eq_false_iff.mpr hcond
      simp only [hcondF, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure,
        ProbComp.eval_pure]
  rw [horacle]

/-- **IND-CPA security preserves under MAC-then-Encrypt**: when `ptLen` is strictly monotone and
computable in polynomial time, every encoded `(msg, tag)` pair on an `n`-bit message has length
`ptLen n`, and `E` is `INDCPA`-secure, then `macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen`
is `INDCPA`-secure. -/
theorem indcpa_macThenEncrypt (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmono : StrictMono ptLen) (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (hcpa : E.INDCPA) :
    (macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).INDCPA := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hred := hcpa (mteToCPAAdversary M ptLen ctBound adversary)
    (isOraclePPT_mteToCPAAdversary M ptLen ctBound hptLenPoly hctBoundPoly hadversary)
  have hcomp : Negligible (fun n => Game.advantage
      (ProbComp.eval (E.cpaGame (mteToCPAAdversary M ptLen ctBound adversary) false (ptLen n)))
      (ProbComp.eval (E.cpaGame (mteToCPAAdversary M ptLen ctBound adversary) true (ptLen n)))) :=
    hred.comp_polynomiallyLowerBounded (.mono_of_le .id hmono.id_le)
  refine hcomp.congr fun n => ?_
  dsimp only
  rw [eval_cpaGame_mteToCPAAdversary E M ptLen hptLenPoly hmono hmsgLen hpairLen ctBound
      adversary false n (hctBound (ptLen n)),
    eval_cpaGame_mteToCPAAdversary E M ptLen hptLenPoly hmono hmsgLen hpairLen ctBound
      adversary true n (hctBound (ptLen n))]

namespace SymmetricCipher

/-- Trailing-bit malleable extension of `E`: appends `false` to every ciphertext on encryption and
ignores the final bit (`ct.take (ct.length - 1)`) during decryption. -/
@[expose]
noncomputable def extendCipher (E : SymmetricCipher) : SymmetricCipher where
  keyGen := E.keyGen
  encrypt n k msg := do
    let c ← E.encrypt n k msg
    return c ++ [false]
  decrypt n k ct :=
    if ct.length == 0 then none else E.decrypt n k (ct.take (ct.length - 1))
  keyGen_ppt := E.keyGen_ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polytime
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hct
    obtain ⟨c, hc, rfl⟩ := hct
    have hdec : E.decrypt n k c = some msg := E.decrypt_encrypt n k hk msg hmsg c hc
    have ht : (c ++ [false]).length = c.length + 1 := by simp
    have heq : (c ++ [false]).take ((c ++ [false]).length - 1) = c := by
      rw [ht, Nat.add_sub_cancel]
      exact List.take_left
    rw [heq]
    simp [ht, hdec]

/-- Oracle handler used by `extendCPAAdversary` to answer `E.extendCipher` CPA queries using
`E`'s CPA oracle, truncating each response to `ctBound` bits and appending `false`. -/
def extendCPAHandler (n ctBound : ℕ) (request : Unit × List Bool) :
    WordOracleComp Unit (List Bool) :=
  let m0 := unframe request.2
  let m1 := dropFrame request.2
  if (m0.length == n) && (m1.length == n) then
    (· ++ [false]) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
  else
    pure []

/-- Reduction from `cpaGame` on `E.extendCipher` to `cpaGame` on `E`: appends `false` to every
valid ciphertext returned by `E`'s CPA oracle. -/
noncomputable def extendCPAAdversary (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) : OracleDistinguisher :=
  fun n _ => OracleComp.interpret
    (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m))
      (extendCPAHandler n (ctBound n)))
    (adversary n [])

/-- `extendCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_extendCPAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (extendCPAAdversary ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        ((unframe p.2.2).length == p.1.1) && ((dropFrame p.2.2).length == p.1.1))
      EIn encBool :=
    (by fun_prop : ComputableTidilyInPolyTime _ EIn encBool).computableInPolyTime
  have hquery : IsOraclePPTOn EIn encBits
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        (· ++ [false]) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.2))) := by
    have hct := hctBound.tidy
    ppt
  have hno : IsOraclePPTOn EIn encBits
      (fun _ : (ℕ × List Bool) × (Unit × List Bool) =>
        (pure [] : WordOracleComp Unit (List Bool))) :=
    (ComputableInPolyTime.const ([] : List Bool)).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn encBits
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        extendCPAHandler p.1.1 (ctBound p.1.1) p.2) := by
    unfold extendCPAHandler
    exact IsOraclePPTOn.cond' hcond hquery hno
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 1)
  exact hadversary.interpret_preprocess_open'
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (resources := fun caller _ => ctBound caller.1 + 1)
    (by fun_prop) hhandler hres fun caller request reply hreply => by
      unfold extendCPAHandler at hreply
      dsimp only at hreply
      split_ifs at hreply with hlenEq
      · obtain ⟨raw, hraw, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
        obtain ⟨ct, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hraw
        have htake : (List.take (ctBound caller.1) ct).length ≤ ctBound caller.1 :=
          List.length_take_le _ _
        simp only [List.length_append, List.length_singleton]
        lia
      · cases OracleComp.eq_of_mem_supportWith_pure hreply
        simp

/-- When `ctBound n` bounds `E` ciphertexts on `n`-bit plaintexts, `E.cpaGame` running
`extendCPAAdversary ctBound adversary` has the exact same distribution as `E.extendCipher.cpaGame`
running `adversary`. -/
theorem eval_cpaGame_extendCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaGame (extendCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.extendCipher.cpaGame adversary bit n) := by
  simp only [cpaGame, extendCPAAdversary, ProbComp.eval_bind, ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_interpret_sumHandler]
  have horacle :
      (fun q s => ProbOracleComp.runWith
          (fun q' s' => ProbComp.eval (E.cpaEncryptionOracle n k bit q' s'))
          (extendCPAHandler n (ctBound n) q) s) =
        (fun q s =>
          ProbComp.eval ((SymmetricCipher.extendCipher E).cpaEncryptionOracle n k bit q s)) := by
    funext ⟨⟨⟩, req⟩ s
    simp only [extendCPAHandler, cpaEncryptionOracle]
    by_cases hcond : ((unframe req).length == n && (dropFrame req).length == n) = true
    · simp only [hcond, ↓reduceIte, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
        extendCipher, ProbComp.eval_bind, ProbComp.eval_pure,
        Functor.map_map, PMF.map_bind, PMF.pure_map, Prod.map_apply, id_eq,
        PMF.bind_bind, PMF.pure_bind]
      apply PMF.bind_congr_on_support
      intro c hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      have hmbLen : (if bit then dropFrame req else unframe req).length = n := by
        cases bit <;> simp [hcond]
      rw [List.take_of_length_le (hctBound k hk _ hmbLen c hc)]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure,
        ProbComp.eval_pure]
  rw [horacle]

/-- Appending and ignoring a constant trailing bit preserves `INDCPA`. -/
theorem INDCPA.extendCipher {E : SymmetricCipher} (h : E.INDCPA) :
    E.extendCipher.INDCPA := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hneg := h (extendCPAAdversary ctBound adversary)
    (isOraclePPT_extendCPAAdversary hctBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  dsimp only
  rw [eval_cpaGame_extendCPAAdversary E ctBound adversary false n (hctBound n),
    eval_cpaGame_extendCPAAdversary E ctBound adversary true n (hctBound n)]

/-- Stateful oracle handler used by `extendOneTimeCPAAdversary` to answer at most one
`E.extendCipher` CPA query using `E`'s one-time CPA oracle. -/
noncomputable def extendOneTimeCPAHandler (n ctBound : ℕ) (request : Unit × List Bool) :
    StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if !alreadyQueried && (m0.length == n) && (m1.length == n) then
      (fun ct => (ct ++ [false], true)) <$>
        (List.take ctBound <$> ProbOracleComp.query ((), request.2))
    else
      pure ([], alreadyQueried)

/-- Reduction from `cpaOneTimeGame` on `E.extendCipher` to `cpaOneTimeGame` on `E`. -/
noncomputable def extendOneTimeCPAAdversary (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) : OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (extendOneTimeCPAHandler n (ctBound n)))
      (adversary n [])).run false
    return out.1

/-- `extendOneTimeCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_extendOneTimeCPAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (extendOneTimeCPAAdversary ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hstate : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.2.2)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        !p.2.2 && ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool :=
    (by fun_prop : ComputableTidilyInPolyTime _ EIn encBool).computableInPolyTime
  have hquery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        (fun ct => (ct ++ [false], true)) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.1.2))) := by
    have hct := hctBound.tidy
    ppt
  have hnoReply : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      hstate.computableInPolyTime).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        extendOneTimeCPAHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    unfold extendOneTimeCPAHandler
    exact IsOraclePPTOn.cond' hcond hquery hnoReply
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 2)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 2)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (extendOneTimeCPAHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run false) := by
    apply hadversary.run_interpret_preprocess_open'
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => false)
      (resources := fun caller _ => ctBound caller.1 + 2)
      (by fun_prop) hhandler (ComputableInPolyTime.const false)
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request alreadyQueried _ result hresult
    unfold extendOneTimeCPAHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      have htake : (List.take (ctBound caller.1) raw).length ≤ ctBound caller.1 :=
        List.length_take_le _ _
      exact ⟨trivial, by simp only [List.length_append, List.length_singleton]; lia,
        by simp [encBool_apply]⟩
    · cases OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, by simp [encBool_apply]⟩
  unfold extendOneTimeCPAAdversary
  simpa only [bind_pure_comp] using
    (hrun.map' (ComputableInPolyTime.fst encBool encBool)).isOraclePPT

/-- Equivalence between `E.cpaOneTimeGame` running `extendOneTimeCPAAdversary` and
`E.extendCipher.cpaOneTimeGame` running `adversary`. -/
theorem eval_cpaOneTimeGame_extendOneTimeCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaOneTimeGame (extendOneTimeCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.extendCipher.cpaOneTimeGame adversary bit n) := by
  simp only [cpaOneTimeGame, extendOneTimeCPAAdversary, ProbComp.eval_bind,
    ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret_eq_runWith]
  rw [ProbOracleComp.runWith_bind]
  simp only [ProbOracleComp.runWith_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.runWith_run_interpret]
  have hsim := ProbOracleComp.runWith_map_state
    (fun request alreadyQueried =>
      ProbComp.eval ((SymmetricCipher.extendCipher E).oneTimeCPAEncryptionOracle
        n k bit request alreadyQueried))
    (fun request state =>
      (ProbOracleComp.runWith
          (fun q s => ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit q s))
          ((extendOneTimeCPAHandler n (ctBound n) request).run state.1) state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun alreadyQueried : Bool => (alreadyQueried, alreadyQueried))
    (fun request alreadyQueried => by
      change (ProbComp.eval ((SymmetricCipher.extendCipher E).oneTimeCPAEncryptionOracle
          n k bit request alreadyQueried)).map (fun x => (x.1, x.2, x.2)) =
        (ProbOracleComp.runWith
            (fun q s => ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit q s))
            (extendOneTimeCPAHandler n (ctBound n) request alreadyQueried) alreadyQueried).map
          (fun result => (result.1.1, result.1.2, result.2))
      simp only [oneTimeCPAEncryptionOracle, extendOneTimeCPAHandler, extendCipher]
      by_cases hcond : (!alreadyQueried && ((unframe request.2).length == n) &&
          ((dropFrame request.2).length == n)) = true
      · simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, Functor.map_map,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
          PMF.map_bind, PMF.pure_map, Prod.map_apply, id_eq,
          PMF.bind_bind, PMF.pure_bind]
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
          cases bit <;> simp [hcond]
        apply PMF.bind_congr_on_support
        intro c hc
        rw [List.take_of_length_le (hctBound k hk _ hmbLen c hc)]
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
          ProbOracleComp.runWith_pure, PMF.pure_map])
    (adversary n []) false
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Appending and ignoring a constant trailing bit preserves `OneTimeINDCPA`. -/
theorem OneTimeINDCPA.extendCipher {E : SymmetricCipher} (h : E.OneTimeINDCPA) :
    E.extendCipher.OneTimeINDCPA := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hneg := h (extendOneTimeCPAAdversary ctBound adversary)
    (isOraclePPT_extendOneTimeCPAAdversary hctBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  dsimp only
  rw [eval_cpaOneTimeGame_extendOneTimeCPAAdversary E ctBound adversary false n (hctBound n),
    eval_cpaOneTimeGame_extendOneTimeCPAAdversary E ctBound adversary true n (hctBound n)]

end SymmetricCipher

/-! ### Explicit CI and CCA Attacks on `macThenEncrypt E.extendCipher M ptLen ...` -/

private theorem append_true_ne_append_false (c : List Bool) : c ++ [true] ≠ c ++ [false] := by
  intro h
  have hlast := congrArg List.getLast? h
  simp at hlast

private theorem decrypt_macThenEncrypt_extendCipher_append_true
    (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (n : ℕ) {ke km msg tag c : List Bool}
    (hke : ke ∈ (ProbComp.eval (E.keyGen (ptLen n))).support)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (hmsg : msg.length = n)
    (htag : tag ∈ (ProbComp.eval (M.sign km msg)).support)
    (hc : c ∈ (ProbComp.eval (E.encrypt (ptLen n) ke
      (encPair encBits encBits (msg, tag)))).support) :
    (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen).decrypt n
      (encPair encBits encBits (ke, km)) (c ++ [true]) = some msg := by
  have hdecE : E.decrypt (ptLen n) ke c = some (encPair encBits encBits (msg, tag)) :=
    E.decrypt_encrypt (ptLen n) ke hke _ (hpairLen n km hkm msg hmsg tag htag) c hc
  have ht : (c ++ [true]).length = c.length + 1 := by simp
  have heq : (c ++ [true]).take ((c ++ [true]).length - 1) = c := by
    rw [ht, Nat.add_sub_cancel]
    exact List.take_left
  have hdecExt : E.extendCipher.decrypt (ptLen n) ke (c ++ [true]) =
      some (encPair encBits encBits (msg, tag)) := by
    simp [SymmetricCipher.extendCipher, ht, hdecE]
  have hmLen : msg.length = M.msgLen n := hmsg.trans (hmsgLen n).symm
  have hver : M.verify km msg tag = true := M.verify_sign n km hkm msg hmLen tag htag
  simp only [macThenEncrypt]
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits, hdecExt]
  simp only [Option.elim_some]
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
  simp [hmLen, hver]

private theorem malleate_macThenEncrypt_extendCipher_ciphertext
    (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (n : ℕ) {ke km msg ct : List Bool}
    (hke : ke ∈ (ProbComp.eval (E.keyGen (ptLen n))).support)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
      hpairLen).encrypt n (encPair encBits encBits (ke, km)) msg)).support) :
    (ct.take (ct.length - 1) ++ [true]) ≠ ct ∧
    (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen).decrypt n
      (encPair encBits encBits (ke, km)) (ct.take (ct.length - 1) ++ [true]) = some msg := by
  simp only [macThenEncrypt, SymmetricCipher.extendCipher, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
    dropFrame_encPair_encBits, unframe_encPair_encBits] at hct
  obtain ⟨tag, htag, c, hc, rfl⟩ := hct
  have ht : (c ++ [false]).length = c.length + 1 := by simp
  have htake : (c ++ [false]).take ((c ++ [false]).length - 1) = c := by
    rw [ht, Nat.add_sub_cancel]
    exact List.take_left
  refine ⟨?_, ?_⟩
  · rw [htake]
    exact append_true_ne_append_false c
  · rw [htake]
    exact decrypt_macThenEncrypt_extendCipher_append_true E M ptLen hptLenPoly hmsgLen hpairLen n
      hke hkm hmsg htag hc

/-- One-query ciphertext-integrity adversary against `macThenEncrypt E.extendCipher M ptLen ...`:
encrypts `0^n` and flips the trailing `false` bit of the ciphertext to `true`. -/
def macThenEncryptExtendCIAdversary (ctBound : ℕ → ℕ) : CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n false)
    return ct.take (ct.length - 1) ++ [true]

/-- `macThenEncryptExtendCIAdversary` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_macThenEncryptExtendCIAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (macThenEncryptExtendCIAdversary ctBound) := by
  have hct := hctBound.tidy
  ppt [macThenEncryptExtendCIAdversary]

private theorem ci_oracle_for_macThenEncrypt_extendCipher (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
      hpairLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval ((macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).ciOneTimeGame
      (macThenEncryptExtendCIAdversary ctBound) n) = PMF.pure true := by
  let E' := macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen
  simp only [SymmetricCipher.ciOneTimeGame, macThenEncryptExtendCIAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  trans ((ProbComp.eval (E'.keyGen n)).bind fun _ => PMF.pure true)
  · apply PMF.bind_congr_on_support
    intro k hk
    have hk' := hk
    simp only [macThenEncrypt, SymmetricCipher.extendCipher, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk'
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk'
    simp only [SymmetricCipher.oneTimeCIEncryptionOracle, StateT.run, List.isEmpty_nil,
      List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    trans ((ProbComp.eval (E'.encrypt n (encPair encBits encBits (ke, km))
        (List.replicate n false))).bind fun _ => PMF.pure true)
    · apply PMF.bind_congr_on_support
      intro ct hct
      rw [List.take_of_length_le (hctBound _ hk _ List.length_replicate ct hct)]
      obtain ⟨hne, hdec⟩ := malleate_macThenEncrypt_extendCipher_ciphertext E M ptLen hptLenPoly
        hmsgLen hpairLen n hke hkm List.length_replicate hct
      rw [hdec]
      simp [hne]
    · simp
  · simp

/-- `macThenEncryptExtendCIAdversary` succeeds with probability `1` in `ciOneTimeGame` against
`macThenEncrypt E.extendCipher M ptLen ...`. -/
theorem eval_ciOneTimeGame_macThenEncrypt_extendCipher (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
      hpairLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval ((macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).ciOneTimeGame
      (macThenEncryptExtendCIAdversary ctBound) n) = PMF.pure true :=
  ci_oracle_for_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen ctBound n hctBound

/-- `macThenEncrypt E.extendCipher M ptLen ...` fails `OneTimeCiphertextIntegrity` for every
cipher `E` and MAC `M` satisfying `hmsgLen` and `hpairLen`. -/
theorem not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n) :
    ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).OneTimeCiphertextIntegrity := by
  intro hci
  let E' := macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E'.exists_ciphertext_length_bound_of_length_eq
  have hneg := hci.negligible (macThenEncryptExtendCIAdversary ctBound)
    (isOraclePPT_macThenEncryptExtendCIAdversary hctBoundPoly)
  have hcongr : (fun n => Game.succProbability (ProbComp.eval
      (E'.ciOneTimeGame (macThenEncryptExtendCIAdversary ctBound) n))) = fun _ => (1 : ℝ≥0) := by
    funext n
    rw [eval_ciOneTimeGame_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen
      ctBound n (hctBound n)]
    simp [Game.succProbability]
  rw [hcongr] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- `macThenEncrypt E.extendCipher M ptLen ...` fails `CiphertextIntegrity` for every cipher `E`
and MAC `M` satisfying `hmsgLen` and `hpairLen`. -/
theorem not_ciphertextIntegrity_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n) :
    ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).CiphertextIntegrity :=
  fun hci => not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher E M ptLen hptLenPoly
    hmsgLen hpairLen hci.oneTimeCiphertextIntegrity

/-- Two-query chosen-ciphertext distinguisher against `macThenEncrypt E.extendCipher M ptLen ...`:
queries the challenge encryption oracle on `(0^n, 1^n)`, flips the trailing `false` bit of the
returned ciphertext `ct` to `true`, queries the decryption oracle on the distinct ciphertext `ct'`,
and outputs `true` iff the plaintext equals `1^n`. -/
def macThenEncryptExtendCCAAdversary (ctBound : ℕ → ℕ) : CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (ctBound n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let ct' := ct.take (ct.length - 1) ++ [true]
    let dec ← List.take (n + 1) <$> ProbOracleComp.query (true, ct')
    return (dec == encOption encBits (some m1))

/-- `macThenEncryptExtendCCAAdversary` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_macThenEncryptExtendCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (macThenEncryptExtendCCAAdversary ctBound) := by
  have hct := hctBound.tidy
  ppt [macThenEncryptExtendCCAAdversary]

/-- In `ccaOneTimeGame` against `macThenEncrypt E.extendCipher M ptLen ...`,
`macThenEncryptExtendCCAAdversary` outputs `bit` with probability `1` whenever `bit = true` or
`1 ≤ n`. -/
theorem eval_ccaOneTimeGame_macThenEncrypt_extendCipher (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (ctBound : ℕ → ℕ) (bit : Bool) {n : ℕ} (hn : bit = true ∨ 1 ≤ n)
    (hctBound : (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
      hpairLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval ((macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).ccaOneTimeGame
      (macThenEncryptExtendCCAAdversary ctBound) bit n) = PMF.pure bit := by
  let E' := macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen
  simp only [SymmetricCipher.ccaOneTimeGame, macThenEncryptExtendCCAAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  trans ((ProbComp.eval (E'.keyGen n)).bind fun _ => PMF.pure bit)
  · apply PMF.bind_congr_on_support
    intro k hk
    have hk' := hk
    simp only [macThenEncrypt, SymmetricCipher.extendCipher, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk'
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk'
    have hmbLen : (if bit then List.replicate n true else List.replicate n false).length = n := by
      cases bit <;> simp
    simp only [SymmetricCipher.oneTimeCCAOracle, StateT.run,
      Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, unframe_encPair_encBits,
      dropFrame_encPair_encBits,
      List.length_replicate, beq_self_eq_true, Bool.and_self, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    trans ((ProbComp.eval (E'.encrypt n (encPair encBits encBits (ke, km))
        (if bit then List.replicate n true else List.replicate n false))).bind fun _ =>
      PMF.pure bit)
    · apply PMF.bind_congr_on_support
      intro ct hct
      rw [List.take_of_length_le (hctBound _ hk _ hmbLen ct hct)]
      obtain ⟨hne, hdec⟩ := malleate_macThenEncrypt_extendCipher_ciphertext E M ptLen hptLenPoly
        hmsgLen hpairLen n hke hkm hmbLen hct
      have hnc : ([ct].contains (ct.take (ct.length - 1) ++ [true])) = false := by simp [hne]
      simp only [hnc, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
      rw [hdec]
      cases bit with
      | true => simp
      | false =>
        have hn1 : 1 ≤ n := hn.resolve_left Bool.false_ne_true
        cases n with
        | zero => contradiction
        | succ m => simp
    · simp
  · simp

/-- `macThenEncryptExtendCCAAdversary` achieves exact one-time CCA advantage `1` against
`macThenEncrypt E.extendCipher M ptLen ...` for every `n ≥ 1`. -/
theorem advantage_ccaOneTimeGame_macThenEncrypt_extendCipher_eq_one (E : SymmetricCipher)
    (M : MACScheme) (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (ctBound : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hctBound : (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
      hpairLen).CiphertextLengthLE n (ctBound n)) :
    Game.advantage
      (ProbComp.eval ((macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).ccaOneTimeGame
        (macThenEncryptExtendCCAAdversary ctBound) false n))
      (ProbComp.eval ((macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).ccaOneTimeGame
        (macThenEncryptExtendCCAAdversary ctBound) true n)) = 1 := by
  rw [eval_ccaOneTimeGame_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen
      ctBound false (Or.inr hn) hctBound,
    eval_ccaOneTimeGame_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen
      ctBound true (Or.inl rfl) hctBound]
  simp [Game.advantage, Game.succProbability]

/-- `macThenEncrypt E.extendCipher M ptLen ...` fails `OneTimeINDCCA` for every cipher `E` and
MAC `M` satisfying `hmsgLen` and `hpairLen`. -/
theorem not_oneTimeINDCCA_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n) :
    ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).OneTimeINDCCA := by
  intro hcca
  let E' := macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E'.exists_ciphertext_length_bound_of_length_eq
  have hneg := hcca (macThenEncryptExtendCCAAdversary ctBound)
    (isOraclePPT_macThenEncryptExtendCCAAdversary hctBoundPoly)
  have ht0 : Filter.Tendsto (fun n => Game.advantage
      (ProbComp.eval (E'.ccaOneTimeGame (macThenEncryptExtendCCAAdversary ctBound) false n))
      (ProbComp.eval (E'.ccaOneTimeGame (macThenEncryptExtendCCAAdversary ctBound) true n)))
      Filter.atTop (nhds 0) := by
    simpa using hneg 0
  have ht : Filter.Tendsto (fun n => Game.advantage
      (ProbComp.eval (E'.ccaOneTimeGame (macThenEncryptExtendCCAAdversary ctBound) false (n + 1)))
      (ProbComp.eval (E'.ccaOneTimeGame (macThenEncryptExtendCCAAdversary ctBound) true (n + 1))))
      Filter.atTop (nhds 0) :=
    ht0.comp (Filter.tendsto_add_atTop_nat 1)
  have h1 : (fun n => Game.advantage
      (ProbComp.eval (E'.ccaOneTimeGame (macThenEncryptExtendCCAAdversary ctBound) false (n + 1)))
      (ProbComp.eval (E'.ccaOneTimeGame (macThenEncryptExtendCCAAdversary ctBound) true (n + 1)))) =
      fun _ => (1 : ℝ≥0) := by
    funext n
    exact advantage_ccaOneTimeGame_macThenEncrypt_extendCipher_eq_one E M ptLen hptLenPoly
      hmsgLen hpairLen ctBound (Nat.succ_pos n) (hctBound (n + 1))
  rw [h1] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- `macThenEncrypt E.extendCipher M ptLen ...` fails `INDCCA` for every cipher `E` and MAC `M`
satisfying `hmsgLen` and `hpairLen`. -/
theorem not_indcca_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n) :
    ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
        hpairLen).INDCCA :=
  fun hcca => not_oneTimeINDCCA_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen
    hcca.oneTimeINDCCA

/-! ### Combined Separation Theorem and PRF Instantiation -/

/-- **Generic MAC-then-Encrypt CCA/CI counterexample theorem**: given any `INDCPA`-secure cipher
`E`, any `SUFCMA`-secure MAC `M` on `n`-bit messages, and a strictly monotone polynomial-time
plaintext-tag length schedule `ptLen`, the trailing-bit malleable extension `E.extendCipher` remains
`INDCPA`, `macThenEncrypt E.extendCipher M ptLen ...` remains `INDCPA`, yet fails
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem macThenEncrypt_extendCipher_counterexample (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmono : StrictMono ptLen) (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (hcpa : E.INDCPA) (hsuf : M.SUFCMA) :
    E.extendCipher.INDCPA ∧ M.SUFCMA ∧
      (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen).INDCPA ∧
      ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
          hpairLen).OneTimeCiphertextIntegrity ∧
      ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen
          hpairLen).CiphertextIntegrity ∧
      ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen).OneTimeINDCCA ∧
      ¬ (macThenEncrypt E.extendCipher M ptLen hptLenPoly hmsgLen hpairLen).INDCCA :=
  ⟨hcpa.extendCipher, hsuf,
    indcpa_macThenEncrypt E.extendCipher M ptLen hptLenPoly hmono hmsgLen hpairLen
      hcpa.extendCipher,
    not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen
      hpairLen,
    not_ciphertextIntegrity_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen,
    not_oneTimeINDCCA_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen,
    not_indcca_macThenEncrypt_extendCipher E M ptLen hptLenPoly hmsgLen hpairLen⟩

/-- On an `n`-bit message under a supported key, every encoded `(msg, tag)` pair produced by
`prfMAC family hpoly` has exact length `3 * n + 1`. -/
theorem prfMAC_pair_length
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    ∀ n km, km ∈ (ProbComp.eval ((prfMAC family hpoly).keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval ((prfMAC family hpoly).sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = 3 * n + 1 := by
  intro n km hkm msg hmsg tag htag
  dsimp only [prfMAC] at hkm htag
  rw [BitString.eval_sampleList] at hkm
  have hkmLen : km.length = n := BitString.length_of_mem_support_uniformList hkm
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
  subst htag
  have htagLen : (prfOracle family km.length km msg).length = n := by
    simp only [prfOracle, hmsg, hkmLen, ↓reduceIte]
    rw [hlen km msg (by rw [hmsg, hkmLen]), hkmLen]
  enc_len [hmsg, htagLen]

/-- Concrete MAC-then-Encrypt counterexample cipher instantiated on
`(prfCipher family).extendCipher` and `prfMAC family` with plaintext-tag length schedule
`ptLen n := 3 * n + 1`. -/
@[expose]
noncomputable def prfMacThenEncryptExtend
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    SymmetricCipher :=
  macThenEncrypt (prfCipher family hpoly hlen).extendCipher (prfMAC family hpoly)
    (fun n => 3 * n + 1) (by fun_prop) (fun _ => rfl) (prfMAC_pair_length family hpoly hlen)

/-- **Non-vacuous end-to-end MAC-then-Encrypt counterexample from any `PseudorandomFunction`**:
for every uniform `PseudorandomFunction family`, `(prfCipher ...).extendCipher` is `INDCPA`,
`prfMAC ...` is `SUFCMA`, `prfMacThenEncryptExtend` is `INDCPA`, and `prfMacThenEncryptExtend`
fails `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem PseudorandomFunction.prfMacThenEncryptExtend_counterexample
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfCipher family hprf.polyTime hprf.length_eq).extendCipher.INDCPA ∧
      (prfMAC family hprf.polyTime).SUFCMA ∧
      (prfMacThenEncryptExtend family hprf.polyTime hprf.length_eq).INDCPA ∧
      ¬ (prfMacThenEncryptExtend family hprf.polyTime hprf.length_eq).OneTimeCiphertextIntegrity ∧
      ¬ (prfMacThenEncryptExtend family hprf.polyTime hprf.length_eq).CiphertextIntegrity ∧
      ¬ (prfMacThenEncryptExtend family hprf.polyTime hprf.length_eq).OneTimeINDCCA ∧
      ¬ (prfMacThenEncryptExtend family hprf.polyTime hprf.length_eq).INDCCA :=
  macThenEncrypt_extendCipher_counterexample
    (prfCipher family hprf.polyTime hprf.length_eq)
    (prfMAC family hprf.polyTime)
    (fun n => 3 * n + 1) (by fun_prop) (fun _ _ h => by dsimp only; omega) (fun _ => rfl)
    (prfMAC_pair_length family hprf.polyTime hprf.length_eq)
    hprf.indcpa_prfCipher hprf.sufCma_prfMAC

end Cslib.Crypto
