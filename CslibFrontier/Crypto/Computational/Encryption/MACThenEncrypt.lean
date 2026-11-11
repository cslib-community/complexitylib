/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
public import CslibFrontier.Crypto.Computational.MAC
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# MAC-then-Encrypt Composition and Chosen-Ciphertext Counterexample

This module formalizes the generic **MAC-then-Encrypt** symmetric encryption construction
(`macThenEncrypt`) together with an explicit counterexample showing that generic MAC-then-Encrypt
does not achieve chosen-ciphertext security (`INDCCA` or `OneTimeINDCCA`) or ciphertext integrity
(`CiphertextIntegrity`), even when the underlying cipher is `INDCPA`-secure and the MAC is
`SUFCMA`-secure ([KatzLindell2020], Section 5.2; [BonehShoup2023], Section 9.4.1).

1. **Generic MAC-then-Encrypt construction (`macThenEncrypt`)**: given a symmetric cipher `E` and a
   MAC scheme `M` authenticating `n`-bit messages (`M.msgLen n = n`) such that `E` correctly
   decrypts encryptions of framed plaintext-tag pairs `encPair encBits encBits (msg, tag)`,
   `macThenEncrypt` signs `msg` with `M` and encrypts the encoded pair `(msg, tag)` under `E`.
2. **Malleable CPA-preserving cipher extension (`extendCipher`)**: appends `false` to every
   ciphertext on encryption and ignores the last bit (`ct.take (ct.length - 1)`) during
   decryption. We prove `extendCipher` preserves `INDCPA` (`INDCPA.extendCipher`) and
   `OneTimeINDCPA` (`OneTimeINDCPA.extendCipher`) as well as plaintext-tag decryption completeness
   (`h_dec_extendCipher`).
3. **Explicit CCA and CI attack on `macThenEncrypt (extendCipher E) M`**: replacing the trailing
   `false` bit of any ciphertext with `true` yields a distinct ciphertext with identical decryption
   under `macThenEncrypt (extendCipher E) M`, breaking `OneTimeINDCCA` and `INDCCA` with exact
   advantage `1` for every `n ≥ 1` (`not_oneTimeINDCCA_macThenEncrypt_extendCipher`,
   `not_indcca_macThenEncrypt_extendCipher`) and `CiphertextIntegrity` with probability `1`.

## Main definitions

* `Cslib.Crypto.macThenEncrypt`: MAC-then-Encrypt symmetric cipher.
* `Cslib.Crypto.SymmetricCipher.extendCipher`: trailing-bit malleable symmetric cipher extension.
* `Cslib.Crypto.SymmetricCipher.extendCPAAdversary`,
  `Cslib.Crypto.SymmetricCipher.extendOneTimeCPAAdversary`: CPA reductions to `E`.
* `Cslib.Crypto.macThenEncryptExtendCCAAdversary`: two-query CCA distinguisher against
  `macThenEncrypt E.extendCipher M`.
* `Cslib.Crypto.macThenEncryptExtendCIAdversary`: one-query CI adversary against
  `macThenEncrypt E.extendCipher M`.

## Main results

* `Cslib.Crypto.h_dec_extendCipher`: `extendCipher` preserves plaintext-tag decryption
  completeness.
* `Cslib.Crypto.SymmetricCipher.INDCPA.extendCipher`,
  `Cslib.Crypto.SymmetricCipher.OneTimeINDCPA.extendCipher`: `extendCipher` preserves `INDCPA` and
  `OneTimeINDCPA`.
* `Cslib.Crypto.advantage_ccaOneTimeGame_macThenEncrypt_extendCipher_eq_one`: the explicit CCA
  attacker achieves exact distinguishing advantage `1` against `macThenEncrypt E.extendCipher M`
  for all `n ≥ 1`.
* `Cslib.Crypto.not_oneTimeINDCCA_macThenEncrypt_extendCipher`,
  `Cslib.Crypto.not_indcca_macThenEncrypt_extendCipher`: `macThenEncrypt E.extendCipher M` fails
  `OneTimeINDCCA` and `INDCCA`.
* `Cslib.Crypto.not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher`,
  `Cslib.Crypto.not_ciphertextIntegrity_macThenEncrypt_extendCipher`: `macThenEncrypt
  E.extendCipher M` fails ciphertext integrity.

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
encrypts the framed pair `encPair encBits encBits (msg, tag)` under `ke ← E.keyGen n`. Since
`SymmetricCipher.decrypt_encrypt` only guarantees correctness on `n`-bit inputs, decryption
completeness on framed `(msg, tag)` pairs is taken explicitly as `h_dec`. -/
@[expose]
noncomputable def macThenEncrypt (E : SymmetricCipher) (M : MACScheme)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag))) : SymmetricCipher where
  keyGen n := do
    let ke ← E.keyGen n
    let km ← M.keyGen n
    return encPair encBits encBits (ke, km)
  encrypt n k msg := do
    let tag ← M.sign (dropFrame k) msg
    E.encrypt n (unframe k) (encPair encBits encBits (msg, tag))
  decrypt n k ct :=
    (E.decrypt n (unframe k) ct).elim none fun p =>
      let msg := unframe p
      let tag := dropFrame p
      if (encPair encBits encBits (msg, tag) == p) && (msg.length == M.msgLen n) &&
          M.verify (dropFrame k) msg tag then
        some msg
      else
        none
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
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
        (fun a : ℕ × List Bool × List Bool => E.decrypt a.1 (unframe a.2.1) a.2.2)
        EDecIn (encOption encBits) :=
      E.decrypt_polyTime.tidy.comp (hn.prod ((ComputableTidilyInPolyTime.unframe.comp hk).prod hct))
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
    have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
      simp [encPair_apply, dropFrame_frame_append]
    rw [hunframe_k, hdrop_k] at hct
    obtain ⟨tag, htag, hct2⟩ := hct
    have hdec : E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)) :=
      h_dec n ke km msg tag hke hkm hmsg htag ct hct2
    have hunframe_p : unframe (encPair encBits encBits (msg, tag)) = msg := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_p : dropFrame (encPair encBits encBits (msg, tag)) = tag := by
      simp [encPair_apply, dropFrame_frame_append]
    have hmLen : msg.length = M.msgLen n := hmsg.trans (hmsgLen n).symm
    have hver : M.verify km msg tag = true := M.verify_sign n km hkm msg hmLen tag htag
    rw [hunframe_k, hdrop_k, hdec]
    simp only [Option.elim_some]
    rw [hunframe_p, hdrop_p]
    simp [hmLen, hver]

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
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
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
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
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

/-- Plaintext-tag decryption completeness `h_dec` lifts from `E` to `E.extendCipher`. -/
theorem h_dec_extendCipher (E : SymmetricCipher) (M : MACScheme)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag))) :
    ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.extendCipher.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.extendCipher.encrypt n ke
          (encPair encBits encBits (msg, tag)))).support,
        E.extendCipher.decrypt n ke ct = some (encPair encBits encBits (msg, tag)) := by
  intro n ke km msg tag hke hkm hmsg htag ct hct
  simp only [SymmetricCipher.extendCipher] at hke hct ⊢
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hct
  obtain ⟨c, hc, rfl⟩ := hct
  have hdec := h_dec n ke km msg tag hke hkm hmsg htag c hc
  have ht : (c ++ [false]).length = c.length + 1 := by simp
  have heq : (c ++ [false]).take ((c ++ [false]).length - 1) = c := by
    rw [ht, Nat.add_sub_cancel]
    exact List.take_left
  rw [heq]
  simp [ht, hdec]

/-! ### Explicit CI and CCA Attacks on `macThenEncrypt E.extendCipher M` -/

private theorem append_true_ne_append_false (c : List Bool) : c ++ [true] ≠ c ++ [false] := by
  intro h
  have hlast := congrArg List.getLast? h
  simp at hlast

private theorem decrypt_macThenEncrypt_extendCipher_append_true
    (E : SymmetricCipher) (M : MACScheme)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)))
    (n : ℕ) {ke km msg tag c : List Bool}
    (hke : ke ∈ (ProbComp.eval (E.keyGen n)).support)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (hmsg : msg.length = n)
    (htag : tag ∈ (ProbComp.eval (M.sign km msg)).support)
    (hc : c ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support) :
    (macThenEncrypt E.extendCipher M hmsgLen (h_dec_extendCipher E M h_dec)).decrypt n
      (encPair encBits encBits (ke, km)) (c ++ [true]) = some msg := by
  have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
    simp [encPair_apply, unframe_frame_append]
  have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
    simp [encPair_apply, dropFrame_frame_append]
  have hdecE : E.decrypt n ke c = some (encPair encBits encBits (msg, tag)) :=
    h_dec n ke km msg tag hke hkm hmsg htag c hc
  have ht : (c ++ [true]).length = c.length + 1 := by simp
  have heq : (c ++ [true]).take ((c ++ [true]).length - 1) = c := by
    rw [ht, Nat.add_sub_cancel]
    exact List.take_left
  have hdecExt : E.extendCipher.decrypt n ke (c ++ [true]) =
      some (encPair encBits encBits (msg, tag)) := by
    simp [SymmetricCipher.extendCipher, ht, hdecE]
  have hunframe_p : unframe (encPair encBits encBits (msg, tag)) = msg := by
    simp [encPair_apply, unframe_frame_append]
  have hdrop_p : dropFrame (encPair encBits encBits (msg, tag)) = tag := by
    simp [encPair_apply, dropFrame_frame_append]
  have hmLen : msg.length = M.msgLen n := hmsg.trans (hmsgLen n).symm
  have hver : M.verify km msg tag = true := M.verify_sign n km hkm msg hmLen tag htag
  simp only [macThenEncrypt]
  rw [hunframe_k, hdrop_k, hdecExt]
  simp only [Option.elim_some]
  rw [hunframe_p, hdrop_p]
  simp [hmLen, hver]

private theorem malleate_macThenEncrypt_extendCipher_ciphertext
    (E : SymmetricCipher) (M : MACScheme)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)))
    (n : ℕ) {ke km msg ct : List Bool}
    (hke : ke ∈ (ProbComp.eval (E.keyGen n)).support)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
      (h_dec_extendCipher E M h_dec)).encrypt n (encPair encBits encBits (ke, km)) msg)).support) :
    (ct.take (ct.length - 1) ++ [true]) ≠ ct ∧
    (macThenEncrypt E.extendCipher M hmsgLen (h_dec_extendCipher E M h_dec)).decrypt n
      (encPair encBits encBits (ke, km)) (ct.take (ct.length - 1) ++ [true]) = some msg := by
  have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
    simp [encPair_apply, dropFrame_frame_append]
  have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
    simp [encPair_apply, unframe_frame_append]
  simp only [macThenEncrypt, SymmetricCipher.extendCipher, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
    hdrop_k, hunframe_k] at hct
  obtain ⟨tag, htag, c, hc, rfl⟩ := hct
  have ht : (c ++ [false]).length = c.length + 1 := by simp
  have htake : (c ++ [false]).take ((c ++ [false]).length - 1) = c := by
    rw [ht, Nat.add_sub_cancel]
    exact List.take_left
  refine ⟨?_, ?_⟩
  · rw [htake]
    exact append_true_ne_append_false c
  · rw [htake]
    exact decrypt_macThenEncrypt_extendCipher_append_true E M hmsgLen h_dec n hke hkm
      hmsg htag hc

/-- One-query ciphertext-integrity adversary against `macThenEncrypt E.extendCipher M`: encrypts
`0^n` and flips the trailing `false` bit of the ciphertext to `true`. -/
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
    (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)))
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
          (h_dec_extendCipher E M h_dec)).encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).ciOneTimeGame
      (macThenEncryptExtendCIAdversary ctBound) n) = PMF.pure true := by
  let E' := macThenEncrypt E.extendCipher M hmsgLen (h_dec_extendCipher E M h_dec)
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
      obtain ⟨hne, hdec⟩ := malleate_macThenEncrypt_extendCipher_ciphertext E M hmsgLen h_dec n
        hke hkm List.length_replicate hct
      rw [hdec]
      simp [hne]
    · simp
  · simp

/-- `macThenEncryptExtendCIAdversary` succeeds with probability `1` in `ciOneTimeGame` against
`macThenEncrypt E.extendCipher M`. -/
theorem eval_ciOneTimeGame_macThenEncrypt_extendCipher (E : SymmetricCipher) (M : MACScheme)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)))
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
          (h_dec_extendCipher E M h_dec)).encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).ciOneTimeGame
      (macThenEncryptExtendCIAdversary ctBound) n) = PMF.pure true :=
  ci_oracle_for_macThenEncrypt_extendCipher E M hmsgLen h_dec ctBound n hctBound

/-- `macThenEncrypt E.extendCipher M` fails `OneTimeCiphertextIntegrity` for every cipher `E` and
MAC `M` satisfying `hmsgLen` and `h_dec`. -/
theorem not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag))) :
    ¬ (macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).OneTimeCiphertextIntegrity := by
  intro hci
  let E' := macThenEncrypt E.extendCipher M hmsgLen (h_dec_extendCipher E M h_dec)
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E'.exists_ciphertext_length_bound_of_length_eq
  have hneg := hci.negligible (macThenEncryptExtendCIAdversary ctBound)
    (isOraclePPT_macThenEncryptExtendCIAdversary hctBoundPoly)
  have hcongr : (fun n => Game.succProbability (ProbComp.eval
      (E'.ciOneTimeGame (macThenEncryptExtendCIAdversary ctBound) n))) = fun _ => (1 : ℝ≥0) := by
    funext n
    rw [eval_ciOneTimeGame_macThenEncrypt_extendCipher E M hmsgLen h_dec ctBound n (hctBound n)]
    simp [Game.succProbability]
  rw [hcongr] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- `macThenEncrypt E.extendCipher M` fails `CiphertextIntegrity` for every cipher `E` and MAC `M`
satisfying `hmsgLen` and `h_dec`. -/
theorem not_ciphertextIntegrity_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag))) :
    ¬ (macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).CiphertextIntegrity :=
  fun hci => not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher E M hmsgLen h_dec
    hci.oneTimeCiphertextIntegrity

/-- Two-query chosen-ciphertext distinguisher against `macThenEncrypt E.extendCipher M`: queries
the challenge encryption oracle on `(0^n, 1^n)`, flips the trailing `false` bit of the returned
ciphertext `ct` to `true`, queries the decryption oracle on the distinct ciphertext `ct'`, and
outputs `true` iff the plaintext equals `1^n`. -/
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

/-- In `ccaOneTimeGame` against `macThenEncrypt E.extendCipher M`,
`macThenEncryptExtendCCAAdversary` outputs `bit` with probability `1` whenever `bit = true` or
`1 ≤ n`. -/
theorem eval_ccaOneTimeGame_macThenEncrypt_extendCipher (E : SymmetricCipher) (M : MACScheme)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)))
    (ctBound : ℕ → ℕ) (bit : Bool) {n : ℕ} (hn : bit = true ∨ 1 ≤ n)
    (hctBound : ∀ k ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
          (h_dec_extendCipher E M h_dec)).encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).ccaOneTimeGame
      (macThenEncryptExtendCCAAdversary ctBound) bit n) = PMF.pure bit := by
  let E' := macThenEncrypt E.extendCipher M hmsgLen (h_dec_extendCipher E M h_dec)
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
    have hpair : unframe (encPair encBits encBits (List.replicate n false, List.replicate n true)) =
          List.replicate n false ∧
        dropFrame (encPair encBits encBits (List.replicate n false, List.replicate n true)) =
          List.replicate n true := by
      simp [encPair_apply, unframe_frame_append, dropFrame_frame_append]
    have hmbLen : (if bit then List.replicate n true else List.replicate n false).length = n := by
      cases bit <;> simp
    simp only [SymmetricCipher.oneTimeCCAOracle, StateT.run,
      Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, hpair.1, hpair.2,
      List.length_replicate, beq_self_eq_true, Bool.and_self, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    trans ((ProbComp.eval (E'.encrypt n (encPair encBits encBits (ke, km))
        (if bit then List.replicate n true else List.replicate n false))).bind fun _ =>
      PMF.pure bit)
    · apply PMF.bind_congr_on_support
      intro ct hct
      rw [List.take_of_length_le (hctBound _ hk _ hmbLen ct hct)]
      obtain ⟨hne, hdec⟩ := malleate_macThenEncrypt_extendCipher_ciphertext E M hmsgLen h_dec n
        hke hkm hmbLen hct
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
`macThenEncrypt E.extendCipher M` for every `n ≥ 1`. -/
theorem advantage_ccaOneTimeGame_macThenEncrypt_extendCipher_eq_one (E : SymmetricCipher)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag)))
    (ctBound : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hctBound : ∀ k ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
          (h_dec_extendCipher E M h_dec)).encrypt n k msg)).support, ct.length ≤ ctBound n) :
    Game.advantage
      (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).ccaOneTimeGame
        (macThenEncryptExtendCCAAdversary ctBound) false n))
      (ProbComp.eval ((macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).ccaOneTimeGame
        (macThenEncryptExtendCCAAdversary ctBound) true n)) = 1 := by
  rw [eval_ccaOneTimeGame_macThenEncrypt_extendCipher E M hmsgLen h_dec ctBound false
      (Or.inr hn) hctBound,
    eval_ccaOneTimeGame_macThenEncrypt_extendCipher E M hmsgLen h_dec ctBound true
      (Or.inl rfl) hctBound]
  simp [Game.advantage, Game.succProbability]

/-- `macThenEncrypt E.extendCipher M` fails `OneTimeINDCCA` for every cipher `E` and MAC `M`
satisfying `hmsgLen` and `h_dec`. -/
theorem not_oneTimeINDCCA_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag))) :
    ¬ (macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).OneTimeINDCCA := by
  intro hcca
  let E' := macThenEncrypt E.extendCipher M hmsgLen (h_dec_extendCipher E M h_dec)
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
    exact advantage_ccaOneTimeGame_macThenEncrypt_extendCipher_eq_one E M hmsgLen h_dec ctBound
      (Nat.succ_pos n) (hctBound (n + 1))
  rw [h1] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- `macThenEncrypt E.extendCipher M` fails `INDCCA` for every cipher `E` and MAC `M`
satisfying `hmsgLen` and `h_dec`. -/
theorem not_indcca_macThenEncrypt_extendCipher (E : SymmetricCipher)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (h_dec : ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (E.keyGen n)).support →
      km ∈ (ProbComp.eval (M.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (M.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        E.decrypt n ke ct = some (encPair encBits encBits (msg, tag))) :
    ¬ (macThenEncrypt E.extendCipher M hmsgLen
        (h_dec_extendCipher E M h_dec)).INDCCA :=
  fun hcca => not_oneTimeINDCCA_macThenEncrypt_extendCipher E M hmsgLen h_dec hcca.oneTimeINDCCA

end Cslib.Crypto
