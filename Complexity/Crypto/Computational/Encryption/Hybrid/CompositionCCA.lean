/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.Hybrid.DEMCCA
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Tactic.PPT

/-!
# Adaptive CCA security of hybrid encryption

The KEM key is postprocessed by a native function whose uniform-seed law is exactly the
symmetric cipher's actual key generator. The two KEM hops surround the actual-key DEM game.
Challenge messages have length exactly the security parameter, as in `SymmetricCipher`.
The conclusion is `INDCCA2On` with this admissibility rule, not unrestricted `WordINDCCA2`.

The source's uniform key space is represented by uniform `keyLen n`-bit seeds followed by `F n`.
An exact sampler identity relates this distribution to `E.keyGen n`; no uniformity of encoded
symmetric keys is assumed. Both KEM games retain their existing postchallenge decapsulation
schedule. The reduction answers the distinguished component locally before and after its own
hybrid challenge; other components use bounded external replies. The real-hop commutation is
conditional on the same original keypair and uses supported KEM correctness.

Security and perfect correctness are distinct. Correctness additionally needs postprocessed real
encapsulation keys in the DEM's support. A total saved-coins evaluator supplies this for all seeds;
a simple fixed-width key split instead needs a supported real-key length contract.

## Main definitions

* `Cslib.Crypto.Encryption.hybridKEMCCAHandler`: canonical parsing and bounded decapsulation.
* `Cslib.Crypto.Encryption.hybridKEMCCAContinuation`: both adaptive hybrid phases.
* `Cslib.Crypto.Encryption.hybridToKEMCCA`: the fixed-bit KEM reduction.
* `Cslib.Crypto.Encryption.hybridToKEMCCAHiddenBit`: the single reduction for the factor-two bound.

## Main results

* `Cslib.Crypto.Encryption.eval_kemCCARealGame_hybridToKEMCCA`,
  `Cslib.Crypto.Encryption.eval_kemCCAIdealGame_hybridToKEMCCA`: exact actual-game identities.
* `Cslib.Crypto.Encryption.exists_hybridCCA_reductions`: native reductions and the concrete
  `2 * KEM advantage + symmetric CCA advantage` bound, uniformly for every parameter.
* `Cslib.Crypto.Encryption.hybrid_indcca2On`: n-bit-message adaptive CCA security.
* `Cslib.Crypto.Encryption.isPPTOn_hybridCCAGame`: native honest-game runtime.
* `Cslib.Crypto.Encryption.hybridDecrypt_postprocessed_hybridEncrypt`: separate supported-key
  correctness.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 12.5(a), printed p. 513.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- Decrypt the distinguished component locally under the shown, postprocessed key. Other
canonical components use a bounded decapsulation reply, preserving rejection and empty keys.
This handler never queries the distinguished KEM ciphertext. -/
noncomputable def hybridKEMCCAHandler (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool) (decBound : ℕ → List Bool → ℕ)
    (n : ℕ) (key ctK : List Bool) (request : Unit × List Bool) :
    WordOracleComp Unit (List Bool) :=
  if encPair encBits encBits (unframe request.2, dropFrame request.2) == request.2 then
    if unframe request.2 == ctK then
      pure (encOption encBits (E.decrypt n key (dropFrame request.2)))
    else do
      let reply ← List.take (decBound n (unframe request.2)) <$>
        ProbOracleComp.query ((), unframe request.2)
      return encOption encBits (((Decoder.option Decoder.bits).decode reply).elim none
        (fun k => E.decrypt n (F n k) (dropFrame request.2)))
  else pure []

/-- Simulate the two public-key phases using the shown key and ciphertext. The same local
key override is present before challenge selection. After encryption, only the exact full
challenge word is rejected; a different KEM component with the same DEM component is allowed. -/
noncomputable def hybridKEMCCAContinuation (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ) (pk key ctK : List Bool) :
    WordOracleComp Unit Bool := do
  let handler := hybridKEMCCAHandler E F decBound n key ctK
  let choice ← OracleComp.interpret
    (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m)) handler)
    (adversary.choose n pk)
  if (ChoiceOut.msg₀ choice).length == n && (ChoiceOut.msg₁ choice).length == n then
    let ctD ← ProbOracleComp.sample
      (E.encrypt n key (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice))
    let ct := encPair encBits encBits (ctK, ctD)
    OracleComp.interpret
      (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m))
        (fun request => if request.2 == ct then pure [] else handler request))
      (adversary.guess n (ChoiceOut.state choice) ct)
  else pure false

/-- Fixed-bit KEM distinguisher. The input is the existing `(pk, (shownKey, ctK))` encoding;
no secret key is available to the reduction. -/
noncomputable def hybridToKEMCCA (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (bit : Bool) : OracleDistinguisher := fun n input =>
  hybridKEMCCAContinuation E F decBound adversary bit n (unframe input)
    (F n (unframe (dropFrame input))) (dropFrame (dropFrame input))

/-- An actual decapsulation reply is fully read. The source KEM challenge exclusion never
interferes, since the distinguished component is handled locally in both phases. -/
theorem run_hybridKEMCCAHandler (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (sk key ctK : List Bool)
    (hbound : ∀ ct, (encOption encBits (decaps n sk ct)).length ≤ decBound n ct)
    (request : Unit × List Bool) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encBits decaps n sk ctK))
      (hybridKEMCCAHandler E F decBound n key ctK request)).run () =
      pure (encOption encBits (hybridDecrypt
        (fun n sk ct => if ct == ctK then some key else (decaps n sk ct).map (F n))
        E.decrypt n sk request.2), ()) := by
  simp only [hybridKEMCCAHandler, hybridDecrypt]
  split_ifs with hc hk
  · rfl
  · simp only [OracleComp.interpret_bind, StateT.run_bind, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, StateT.run_map]
    dsimp only [StateT.run, cca2Phase2Oracle]
    simp only [hk, Bool.false_eq_true, ↓reduceIte, map_pure, pure_bind,
      List.take_of_length_le (hbound _),
      Decoder.decode_enc, OracleComp.interpret_pure]
    cases decaps n sk (unframe request.2) <;> rfl
  · rfl

private theorem interpret_substituted_unit {α : Type}
    (oracle : Unit × List Bool → StateT Unit ProbComp (List Bool))
    (handler : Unit × List Bool → WordOracleComp Unit (List Bool))
    (reply : Unit × List Bool → List Bool)
    (hstep : ∀ request, (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (handler request)).run () = pure (reply request, ()))
    (program : WordOracleComp Unit α) :
    OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m)) handler)
        program) =
      OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (fun request s => pure (reply request, s))) program := by
  rw [OracleComp.interpret_interpret]
  congr 1
  funext q
  cases q with
  | inl m =>
    simp only [OracleComp.sumHandler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
      OracleComp.interpret_query]
  | inr request =>
    funext s
    cases s
    exact hstep request

private theorem run_hybridKEMCCAContinuation (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary)
    (bit : Bool) (n : ℕ) (pk sk key ctK : List Bool)
    (hbound : ∀ ct, (encOption encBits (decaps n sk ct)).length ≤ decBound n ct) :
    (do
      let result ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase2Oracle encBits decaps n sk ctK))
        (hybridKEMCCAContinuation E F decBound adversary bit n pk key ctK)).run ()
      pure result.1) =
      cca2GameOn (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits
        (fun _ => pure (pk, sk))
        (fun n _ msg => (fun ct => encPair encBits encBits (ctK, ct)) <$> E.encrypt n key msg)
        (hybridDecrypt (fun n sk ct =>
          if ct == ctK then some key else (decaps n sk ct).map (F n)) E.decrypt)
        adversary bit n := by
  let decrypt := hybridDecrypt (fun n sk ct =>
    if ct == ctK then some key else (decaps n sk ct).map (F n)) E.decrypt
  have hchoose := interpret_substituted_unit
    (cca2Phase2Oracle encBits decaps n sk ctK)
    (hybridKEMCCAHandler E F decBound n key ctK)
    (fun request => encOption encBits (decrypt n sk request.2))
    (run_hybridKEMCCAHandler E F decaps decBound n sk key ctK hbound)
    (adversary.choose n pk)
  simp only [hybridKEMCCAContinuation, cca2GameOn, pure_bind, OracleComp.interpret_bind,
    StateT.run_bind]
  rw [hchoose]
  simp only [bind_assoc]
  congr 1
  funext choice
  by_cases hv : ((ChoiceOut.msg₀ choice.1).length == n &&
      (ChoiceOut.msg₁ choice.1).length == n) = true
  · simp only [hv, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift,
      ProbComp.unifFin, OracleComp.interpret_query_eq_self, bind_map_left, bind_assoc]
    congr 1
    funext ctD
    have hguess := interpret_substituted_unit
      (cca2Phase2Oracle encBits decaps n sk ctK)
      (fun request => if request.2 == encPair encBits encBits (ctK, ctD) then pure []
        else hybridKEMCCAHandler E F decBound n key ctK request)
      (fun request => if request.2 == encPair encBits encBits (ctK, ctD) then []
        else encOption encBits (decrypt n sk request.2))
      (fun request => by
        split_ifs
        · rfl
        · exact run_hybridKEMCCAHandler E F decaps decBound n sk key ctK hbound request)
      (adversary.guess n (ChoiceOut.state choice.1) (encPair encBits encBits (ctK, ctD)))
    simp only [ProbComp.unifFin] at hguess
    rw [hguess]
    cases choice.2
    congr 2
    congr 1
    funext request s
    cases request with
    | inl m => rfl
    | inr request =>
      simp only [OracleComp.sumHandler, cca2Phase2Oracle]
      split_ifs <;> rfl
  · simp [hv]

/-- The ideal KEM hop uses the actual DEM sampler, through an exact postprocessing law.
The original keypair and encapsulation retain their joint distribution. -/
theorem eval_kemCCAIdealGame_hybridToKEMCCA (E : SymmetricCipher)
    (keyLen : ℕ → ℕ) (F : ℕ → List Bool → List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary)
    (bit : Bool) (n : ℕ)
    (hlaw : (BitString.uniformList (keyLen n)).map (F n) = ProbComp.eval (E.keyGen n))
    (hbound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ ct, (encOption encBits (decaps n keys.2 ct)).length ≤ decBound n ct) :
    ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
      (hybridToKEMCCA E F decBound adversary bit) n) =
      ProbComp.eval (hybridDEMGame E keyGen
        (fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk)
        (fun n sk ct => (decaps n sk ct).map (F n)) adversary bit n) := by
  simp only [kemCCAIdealGame, kemIdealGameWith, kemRealGameWith, hybridDEMGame,
    ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro keys hkeys
  apply PMF.bind_congr_on_support
  intro kc _
  rw [← hlaw, PMF.bind_map]
  simp only [BitString.eval_sampleList]
  congr 1
  funext raw
  simp only [kemCCAContinuation, hybridToKEMCCA, encPair_apply, encBits_apply,
    unframe_frame_append, dropFrame_frame_append]
  exact congrArg ProbComp.eval
    (run_hybridKEMCCAContinuation E F decaps decBound adversary bit n keys.1 keys.2
      (F n raw) kc.2 (hbound keys hkeys))

/-- Supported encapsulation correctness removes the local override in the real world.
Encapsulation is commuted with Phase 1 only after the original keypair has been fixed. -/
theorem eval_kemCCARealGame_hybridToKEMCCA (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary)
    (bit : Bool) (n : ℕ)
    (hcorrect : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ kc ∈ (ProbComp.eval (encaps n keys.1)).support, decaps n keys.2 kc.2 = some kc.1)
    (hbound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ ct, (encOption encBits (decaps n keys.2 ct)).length ≤ decBound n ct) :
    ProbComp.eval (kemCCARealGame keyGen encaps decaps
      (hybridToKEMCCA E F decBound adversary bit) n) =
      ProbComp.eval (cca2GameOn
        (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits keyGen
        (hybridEncrypt (fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk) E.encrypt)
        (hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt)
        adversary bit n) := by
  simp only [kemCCARealGame, kemRealGameWith, ProbComp.eval_bind]
  unfold cca2GameOn
  simp only [ProbComp.eval_bind]
  apply PMF.bind_congr_on_support
  intro keys hkeys
  have hfixed : ∀ kc ∈ (ProbComp.eval (encaps n keys.1)).support,
      ProbComp.eval (kemCCAContinuation decaps
        (hybridToKEMCCA E F decBound adversary bit) n keys.2 keys.1 kc.1 kc.2) =
      ProbComp.eval (cca2GameOn
        (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits
        (fun _ => pure keys)
        (fun n _ msg => (fun ct => encPair encBits encBits (kc.2, ct)) <$>
          E.encrypt n (F n kc.1) msg)
        (hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt)
        adversary bit n) := by
    intro kc hkc
    simp only [kemCCAContinuation, hybridToKEMCCA, encPair_apply, encBits_apply,
      unframe_frame_append, dropFrame_frame_append]
    rw [run_hybridKEMCCAContinuation E F decaps decBound adversary bit n keys.1 keys.2
      (F n kc.1) kc.2 (hbound keys hkeys)]
    have hdec : ∀ ct, hybridDecrypt
        (fun m sk ct => if ct == kc.2 then some (F n kc.1)
          else (decaps m sk ct).map (F m)) E.decrypt n keys.2 ct =
        hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt n keys.2 ct := by
      intro ct
      have hk : (if unframe ct == kc.2 then some (F n kc.1)
          else (decaps n keys.2 (unframe ct)).map (F n)) =
          (decaps n keys.2 (unframe ct)).map (F n) := by
        split_ifs with hk
        · simp only [beq_iff_eq] at hk
          rw [hk, hcorrect keys hkeys kc hkc]
          rfl
        · rfl
      simp only [hybridDecrypt, hk]
    simp only [cca2GameOn, pure_bind]
    have hphase1 : cca2Phase1Oracle encBits
        (hybridDecrypt (fun m sk ct => if ct == kc.2 then some (F n kc.1)
          else (decaps m sk ct).map (F m)) E.decrypt) n keys.2 =
        cca2Phase1Oracle encBits
          (hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt) n keys.2 := by
      funext request s
      simp only [cca2Phase1Oracle, hdec]
    have hphase2 : ∀ ct, cca2Phase2Oracle encBits
        (hybridDecrypt (fun m sk ct => if ct == kc.2 then some (F n kc.1)
          else (decaps m sk ct).map (F m)) E.decrypt) n keys.2 ct =
        cca2Phase2Oracle encBits
          (hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt) n keys.2 ct := by
      intro ct
      funext request s
      simp only [cca2Phase2Oracle, hdec]
    simp only [hphase1, hphase2]
    rfl
  rw [PMF.bind_congr_on_support _ _ _ hfixed]
  simp only [cca2GameOn, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
  rw [PMF.bind_comm]
  congr 1
  funext choice
  by_cases hv : ((ChoiceOut.msg₀ choice.1).length == n &&
      (ChoiceOut.msg₁ choice.1).length == n) = true
  · simp only [hv, ↓reduceIte, hybridEncrypt, ProbComp.eval_bind, ProbComp.eval_map,
      PMF.bind_bind, PMF.bind_map, Function.comp_def, ProbComp.eval_pure, PMF.pure_bind]
  · simp [hv]

private theorem computableInPolyTime_hybridKEMReply (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => encOption encBits
        (((Decoder.option Decoder.bits).decode p.2.2).elim none
          (fun k => E.decrypt p.1 (F p.1 k) p.2.1)))
      (encPair encUnary (encPair encBits encBits)) encBits := by
  let I := encPair encUnary (encPair encBits encBits)
  have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  have ht := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  have hp := ComputableInPolyTime.fst I encBits
  have hk := ComputableInPolyTime.snd I encBits
  have hdecode := (Decoder.option Decoder.bits).computableInPolyTime.comp ht.snd'
  have hbody := E.decrypt_polyTime.comp
    ((hn.comp hp).prod ((hF.comp ((hn.comp hp).prod hk)).prod (ht.fst'.comp hp)))
  exact (hdecode.optionElimWithInput (ComputableInPolyTime.const none) hbody).encoding_comp

/-- Native implementation of bounded KEM reply reading, including the cost of key
postprocessing and decryption. The certificate holds for arbitrary external replies. -/
@[fun_prop]
theorem isOraclePPTOn_hybridKEMCCAHandler (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {key ctK request : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hkey : ComputableInPolyTime key input encBits)
    (hctK : ComputableInPolyTime ctK input encBits)
    (hrequest : ComputableInPolyTime request input encBits) :
    IsOraclePPTOn input encBits (fun a =>
      hybridKEMCCAHandler E F decBound (n a) (key a) (ctK a) ((), request a)) := by
  have hkem := ComputableInPolyTime.unframe.comp hrequest
  have hdem := ComputableInPolyTime.dropFrame.comp hrequest
  have hcanonical := ComputableInPolyTime.beq (encB := encBits)
    (hkem.prod hdem).encoding_comp hrequest
  have heq := ComputableInPolyTime.beq (encB := encBits) hkem hctK
  have hlocal := (E.decrypt_polyTime.comp (hn.prod (hkey.prod hdem))).encoding_comp
  have hp := ComputableInPolyTime.fst input encBits
  have hr := ComputableInPolyTime.snd input encBits
  have hreply := (computableInPolyTime_hybridKEMReply E hF).comp
    ((hn.comp hp).prod ((hdem.comp hp).prod hr))
  unfold hybridKEMCCAHandler
  exact IsOraclePPTOn.cond' hcanonical
    (IsOraclePPTOn.cond' heq hlocal.isOraclePPTOn
      ((IsOraclePPTOn.query_take' () hkem (hdecBound.comp (hn.prod hkem))).bind_with
        hreply.isOraclePPTOn))
    (ComputableInPolyTime.const []).isOraclePPTOn

private theorem isOraclePPTOn_hybridKEMCCAInterpret (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {n : α → ℕ} {key ctK : α → List Bool} {program : α → WordOracleComp Unit β}
    (hn : ComputableInPolyTime n input encUnary)
    (hkey : ComputableInPolyTime key input encBits)
    (hctK : ComputableInPolyTime ctK input encBits)
    (hprogram : IsOraclePPTOn input output program)
    {reject : α → List Bool → Bool}
    (hreject : ComputableInPolyTime (fun p : α × List Bool => reject p.1 p.2)
      (encPair input encBits) encBool) :
    IsOraclePPTOn input output (fun a => OracleComp.interpret
      (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m))
        (fun request => if reject a request.2 then pure [] else
          hybridKEMCCAHandler E F decBound (n a) (key a) (ctK a) request)) (program a)) := by
  have hhandler : IsOraclePPTOn (encPair input (encPair (encFinEnum Unit) encBits)) encBits
      (fun p : α × (Unit × List Bool) => if reject p.1 p.2.2 then pure [] else
        hybridKEMCCAHandler E F decBound (n p.1) (key p.1) (ctK p.1) p.2) :=
    IsOraclePPTOn.cond' (hreject.comp
      ((ComputableInPolyTime.fst input (encPair (encFinEnum Unit) encBits)).prod
        (ComputableInPolyTime.snd input (encPair (encFinEnum Unit) encBits)).snd'))
      (ComputableInPolyTime.const []).isOraclePPTOn
      (isOraclePPTOn_hybridKEMCCAHandler E hF hdecBound
        (hn.comp (by fun_prop)) (hkey.comp (by fun_prop)) (hctK.comp (by fun_prop)) (by fun_prop))
  obtain ⟨c, d, hsize⟩ :=
    (computableInPolyTime_hybridKEMReply E hF).tidy.polyBounded_length.exists_le
  let resources := fun (a : α) (ct : List Bool) =>
    (encOption encBits (E.decrypt (n a) (key a) (dropFrame ct))).length +
      c * (2 * n a + 2 * (dropFrame ct).length + decBound (n a) (unframe ct) + 5) ^ d
  have hres : ComputableInPolyTime (fun p : α × List Bool => resources p.1 p.2)
      (encPair input encBits) encUnary := by
    have hp := ComputableInPolyTime.fst input encBits
    have hq := ComputableInPolyTime.snd input encBits
    have hlocal := (E.decrypt_polyTime.comp
      ((hn.comp hp).prod ((hkey.comp hp).prod (ComputableInPolyTime.dropFrame.comp hq))))
    have hn' := hn.comp hp
    have hb := hdecBound.comp (hn'.prod (ComputableInPolyTime.unframe.comp hq))
    have hl := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.dropFrame.comp hq)
    exact ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.length_bits.comp hlocal.encoding_comp)
      (by fun_prop)
  apply IsOraclePPTOn.interpret_preprocess_open' hprogram ComputableInPolyTime.id' hhandler hres
  intro a request reply hreply
  split_ifs at hreply with hr
  · cases OracleComp.eq_of_mem_supportWith_pure hreply
    exact Nat.zero_le _
  · unfold hybridKEMCCAHandler at hreply
    split_ifs at hreply
    · cases OracleComp.eq_of_mem_supportWith_pure hreply
      exact Nat.le_add_right _ _
    · obtain ⟨raw, hraw, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
      cases OracleComp.eq_of_mem_supportWith_pure hreply
      obtain ⟨full, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hraw
      have hlen := List.length_take_le (decBound (n a) (unframe request.2)) full
      have h := hsize (n a, dropFrame request.2,
        full.take (decBound (n a) (unframe request.2)))
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at h
      exact (h.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))).trans
        (Nat.le_add_left _ _)
    · cases OracleComp.eq_of_mem_supportWith_pure hreply
      exact Nat.zero_le _

/-- Native certificate for both simulated phases. All external reads have a unary-computable
cap; subsequent key postprocessing, decryption and challenge handling are charged. -/
theorem isOraclePPTOn_hybridKEMCCAContinuation (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {pk key ctK : α → List Bool}
    {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hkey : ComputableInPolyTime key input encBits)
    (hctK : ComputableInPolyTime ctK input encBits)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsOraclePPTOn input encBool (fun a =>
      hybridKEMCCAContinuation E F decBound adversary (bit a) (n a) (pk a) (key a) (ctK a)) := by
  let C := encPair (encPair encBits encBits) encBits
  have hchoose := isOraclePPTOn_hybridKEMCCAInterpret E (reject := fun _ _ => false)
    hF hdecBound hn hkey hctK
    (hA.choose.on.preprocess' (hn.prod hpk)) (ComputableInPolyTime.const false)
  have hp := ComputableInPolyTime.fst input C
  have hc := ComputableInPolyTime.snd input C
  have hn1 := hn.comp hp
  have hkey1 := hkey.comp hp
  have hk1 := hctK.comp hp
  have hm0 := hc.fst'.fst'
  have hm1 := hc.fst'.snd'
  have henc := (E.encrypt_ppt.isOraclePPTOn (Operation := Unit)).preprocess'
    (hn1.prod (hkey1.prod (ComputableInPolyTime.ite (hbit.comp hp) hm1 hm0)))
  have hbase := ComputableInPolyTime.fst (encPair input C) encBits
  have hctD := ComputableInPolyTime.snd (encPair input C) encBits
  have hn2 := hn1.comp hbase
  have hkey2 := hkey1.comp hbase
  have hk2 := hk1.comp hbase
  have hct := (hk2.prod hctD).encoding_comp
  have hguess := isOraclePPTOn_hybridKEMCCAInterpret E
    (reject := fun a req => req == encPair encBits encBits (ctK a.1.1, a.2))
    hF hdecBound hn2 hkey2 hk2
    (hA.guess.preprocess' (hn2.prod ((hc.snd'.comp hbase).prod hct)))
    (ComputableInPolyTime.beq (encB := encBits)
      (ComputableInPolyTime.snd _ encBits)
      (hct.comp (ComputableInPolyTime.fst _ encBits)))
  have hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.2.1.length == p.1) && (p.2.2.length == p.1))
      (encPair encUnary (encPair encBits encBits)) encBool := by fun_prop
  have hcondition := hvalid.comp (hn1.prod (hm0.prod hm1))
  simp only [Bool.false_eq_true, ↓reduceIte] at hchoose
  unfold hybridKEMCCAContinuation
  exact hchoose.bind_with (IsOraclePPTOn.cond' hcondition (henc.bind_with hguess)
    (ComputableInPolyTime.const false).isOraclePPTOn)

/-- The fixed-bit KEM reduction is uniform strict oracle PPT. It does not sample ideal keys,
so its native certificate needs no efficiency assumption on the ideal key-length schedule. -/
theorem isOraclePPT_hybridToKEMCCA (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT) (bit : Bool) :
    IsOraclePPT encBool (hybridToKEMCCA E F decBound adversary bit) := by
  have hn := ComputableInPolyTime.fst encUnary encBits
  have hi := ComputableInPolyTime.snd encUnary encBits
  have hp := ComputableInPolyTime.unframe.comp hi
  have ht := ComputableInPolyTime.dropFrame.comp hi
  have hk := hF.comp (hn.prod (ComputableInPolyTime.unframe.comp ht))
  have hc := ComputableInPolyTime.dropFrame.comp ht
  exact (isOraclePPTOn_hybridKEMCCAContinuation E hF hdecBound hA hn hp hk hc
    (ComputableInPolyTime.const bit)).isOraclePPT

/-- A single KEM reduction chooses the hybrid challenge bit privately and complements the
answer in the true world. This retains the signed difference between the two KEM hops. -/
noncomputable def hybridToKEMCCAHiddenBit (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) : OracleDistinguisher := fun n input => do
  let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let guess ← hybridToKEMCCA E F decBound adversary bit n input
  return guess ^^ bit

/-- The hidden-bit reduction is uniform strict oracle PPT, including private bit selection
and answer complementation. -/
theorem isOraclePPT_hybridToKEMCCAHiddenBit (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT) :
    IsOraclePPT encBool (hybridToKEMCCAHiddenBit E F decBound adversary) := by
  let I := encPair encUnary encBits
  have hp := ComputableInPolyTime.fst I encBool
  have hb := ComputableInPolyTime.snd I encBool
  have hn := hp.fst'
  have hi := hp.snd'
  have hpk := ComputableInPolyTime.unframe.comp hi
  have ht := ComputableInPolyTime.dropFrame.comp hi
  have hk := hF.comp (hn.prod (ComputableInPolyTime.unframe.comp ht))
  have hc := ComputableInPolyTime.dropFrame.comp ht
  have hrun := isOraclePPTOn_hybridKEMCCAContinuation E hF hdecBound hA hn hpk hk hc hb
  have hprev := ComputableInPolyTime.fst (encPair I encBool) encBool
  have hout := ComputableInPolyTime.snd (encPair I encBool) encBool
  apply IsOraclePPTOn.isOraclePPT
  unfold hybridToKEMCCAHiddenBit hybridToKEMCCA
  exact (isPPTOn_uniform_bool I).isOraclePPTOn.bind_with
    (hrun.bind_with ((ComputableInPolyTime.bool_xor.comp
      (hout.prod (hb.comp hprev))).isOraclePPTOn))

private theorem eval_kemCCARealGame_hiddenBit (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary) (n : ℕ) :
    ProbComp.eval (kemCCARealGame keyGen encaps decaps
      (hybridToKEMCCAHiddenBit E F decBound adversary) n) =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        (ProbComp.eval (kemCCARealGame keyGen encaps decaps
          (hybridToKEMCCA E F decBound adversary bit) n)).map (fun guess => guess ^^ bit)) := by
  simp only [kemCCARealGame, kemRealGameWith, kemCCAContinuation, hybridToKEMCCAHiddenBit,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret,
    OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
    ProbComp.eval_uniform, PMF.bind_map, PMF.bind_bind, Function.comp_def,
    OracleComp.interpret_pure, StateT.run_pure, PMF.pure_bind, PMF.map_bind, PMF.pure_map]
  rw [PMF.bind_comm]
  congr 1
  funext keys
  rw [PMF.bind_comm]

private theorem eval_kemCCAIdealGame_hiddenBit (E : SymmetricCipher)
    (keyLen : ℕ → ℕ) (F : ℕ → List Bool → List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary) (n : ℕ) :
    ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
      (hybridToKEMCCAHiddenBit E F decBound adversary) n) =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        (ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
          (hybridToKEMCCA E F decBound adversary bit) n)).map (fun guess => guess ^^ bit)) := by
  simp only [kemCCAIdealGame, kemIdealGameWith, kemRealGameWith, kemCCAContinuation,
    hybridToKEMCCAHiddenBit, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret, OracleComp.interpret_bind, StateT.run_bind,
    ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform, PMF.bind_map, PMF.bind_bind,
    Function.comp_def, OracleComp.interpret_pure, StateT.run_pure, PMF.pure_bind,
    PMF.map_bind, PMF.pure_map]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext keys
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext kc
  rw [PMF.bind_comm]

/-- Exact signed real-world selector identity, before taking any absolute values. -/
theorem probability_kemCCARealGame_hybridToKEMCCAHiddenBit (E : SymmetricCipher)
    (F : ℕ → List Bool → List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary) (n : ℕ) :
    (Game.succProbability (ProbComp.eval (kemCCARealGame keyGen encaps decaps
      (hybridToKEMCCAHiddenBit E F decBound adversary) n)) : ℝ) =
      (1 + (Game.succProbability (ProbComp.eval (kemCCARealGame keyGen encaps decaps
        (hybridToKEMCCA E F decBound adversary false) n)) : ℝ) -
        Game.succProbability (ProbComp.eval (kemCCARealGame keyGen encaps decaps
          (hybridToKEMCCA E F decBound adversary true) n))) / 2 := by
  rw [eval_kemCCARealGame_hiddenBit]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    PMF.bind_apply_toReal, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [PMF.toReal_false_eq_one_sub]
  ring

/-- Exact signed ideal-world selector identity, with the same bit and output conventions. -/
theorem probability_kemCCAIdealGame_hybridToKEMCCAHiddenBit (E : SymmetricCipher)
    (keyLen : ℕ → ℕ) (F : ℕ → List Bool → List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary) (n : ℕ) :
    (Game.succProbability (ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
      (hybridToKEMCCAHiddenBit E F decBound adversary) n)) : ℝ) =
      (1 + (Game.succProbability (ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
        (hybridToKEMCCA E F decBound adversary false) n)) : ℝ) -
        Game.succProbability (ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
          (hybridToKEMCCA E F decBound adversary true) n))) / 2 := by
  rw [eval_kemCCAIdealGame_hiddenBit]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    PMF.bind_apply_toReal, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [PMF.toReal_false_eq_one_sub]
  ring

/-- The two KEM hops have total loss two, with one native hidden-bit KEM reduction.
The middle advantage is the existing actual-key DEM experiment, whose exact reduction to
one-time symmetric CCA is `eval_hybridDEMGame`. -/
theorem advantage_hybridCCA_le_two_mul (E : SymmetricCipher)
    (keyLen : ℕ → ℕ) (F : ℕ → List Bool → List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (adversary : WordCCA2Adversary) (n : ℕ)
    (hlaw : (BitString.uniformList (keyLen n)).map (F n) = ProbComp.eval (E.keyGen n))
    (hcorrect : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ kc ∈ (ProbComp.eval (encaps n keys.1)).support, decaps n keys.2 kc.2 = some kc.1)
    (hbound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ ct, (encOption encBits (decaps n keys.2 ct)).length ≤ decBound n ct) :
    let encaps' := fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk
    let decaps' := fun n sk ct => (decaps n sk ct).map (F n)
    Game.advantage
      (ProbComp.eval (cca2GameOn
        (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits keyGen
        (hybridEncrypt encaps' E.encrypt) (hybridDecrypt decaps' E.decrypt) adversary false n))
      (ProbComp.eval (cca2GameOn
        (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits keyGen
        (hybridEncrypt encaps' E.encrypt) (hybridDecrypt decaps' E.decrypt) adversary true n)) ≤
      2 * Game.advantage
        (ProbComp.eval (kemCCARealGame keyGen encaps decaps
          (hybridToKEMCCAHiddenBit E F decBound adversary) n))
        (ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
          (hybridToKEMCCAHiddenBit E F decBound adversary) n)) +
      Game.advantage
        (ProbComp.eval (hybridDEMGame E keyGen encaps' decaps' adversary false n))
        (ProbComp.eval (hybridDEMGame E keyGen encaps' decaps' adversary true n)) := by
  dsimp only
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Game.coe_advantage,
    probability_kemCCARealGame_hybridToKEMCCAHiddenBit,
    probability_kemCCAIdealGame_hybridToKEMCCAHiddenBit,
    eval_kemCCARealGame_hybridToKEMCCA E F keyGen encaps decaps decBound adversary _ n
      hcorrect hbound,
    eval_kemCCAIdealGame_hybridToKEMCCA E keyLen F keyGen encaps decaps decBound adversary _ n
      hlaw hbound]
  have hscale (a b c d : ℝ) :
      2 * |(1 + a - b) / 2 - (1 + c - d) / 2| = |(a - b) - (c - d)| := by
    calc
      _ = |2 * ((1 + a - b) / 2 - (1 + c - d) / 2)| := by rw [abs_mul]; norm_num
      _ = _ := by congr 1; ring
  rw [hscale]
  have h (a b c d : ℝ) : |a - b| ≤ |(a - b) - (c - d)| + |c - d| := by
    simpa only [sub_zero] using abs_sub_le (a - b) (c - d) (0 : ℝ)
  exact h _ _ _ _

private theorem isPPTOn_postprocessed_encaps
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2)) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => (fun kc => (F p.1 kc.1, kc.2)) <$> encaps p.1 p.2) := by
  apply hencaps.map_with
  have hp := ComputableInPolyTime.fst (encPair encUnary encBits) (encPair encBits encBits)
  have hk := ComputableInPolyTime.snd (encPair encUnary encBits) (encPair encBits encBits)
  exact (hF.comp (hp.fst'.prod hk.fst')).prod hk.snd'

private theorem computableInPolyTime_postprocessed_decaps
    {F : ℕ → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hdecaps : ComputableInPolyTime (fun ⟨n, sk, ct⟩ => decaps n sk ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits)) :
    ComputableInPolyTime (fun ⟨n, sk, ct⟩ => (decaps n sk ct).map (F n))
      (encPair encUnary (encPair encBits encBits)) (encOption encBits) := by
  fun_prop

/-- **Adaptive CCA security of KEM–DEM encryption**, for the source symmetric cipher's
`n`-bit message model ([BonehShoup2023], Exercise 12.5(a)). The same native postprocessor is
used on the shown KEM key and on every successful decapsulation. Its ideal-key distribution
is exactly the actual symmetric key sampler, uniformly in the security parameter.

KEM correctness is needed for the real-game hop. Correctness of hybrid decryption is a separate
supported-output contract; the security statement does not assert unrestricted word-message CCA. -/
theorem hybrid_indcca2On (E : SymmetricCipher)
    {keyLen : ℕ → ℕ} {F : ℕ → List Bool → List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkem : Game.Indistinguishable
      (fun B n => ProbComp.eval (kemCCARealGame keyGen encaps decaps B n))
      (fun B n => ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps B n))
      (IsOraclePPT encBool))
    (hdem : E.OneTimeINDCCA)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun ⟨n, sk, ct⟩ => decaps n sk ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits))
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hlaw : ∀ n, (BitString.uniformList (keyLen n)).map (F n) = ProbComp.eval (E.keyGen n))
    (hcorrect : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
      ∀ kc ∈ (ProbComp.eval (encaps n keys.1)).support, decaps n keys.2 kc.2 = some kc.1) :
    INDCCA2On (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits encBits keyGen
      (hybridEncrypt (fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk) E.encrypt)
      (hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt) := by
  intro adversary hA
  obtain ⟨decBound, hdecBoundPoly, hdecBound⟩ := exists_decryption_length_bound hkeyGen hdecaps
  have hk := hkem (hybridToKEMCCAHiddenBit E F decBound adversary)
    (isOraclePPT_hybridToKEMCCAHiddenBit E hF hdecBoundPoly hA)
  have hd := hdem.indistinguishable_hybridDEMGame
    (encaps := fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk)
    (decaps := fun n sk ct => (decaps n sk ct).map (F n)) hkeyGen
    (isPPTOn_postprocessed_encaps hF hencaps)
    (computableInPolyTime_postprocessed_decaps hF hdecaps) adversary hA
  apply negligible_of_le ((hk.add hk).add hd)
  intro n
  simpa only [two_mul, Pi.add_apply] using
    advantage_hybridCCA_le_two_mul E keyLen F keyGen encaps decaps decBound adversary n
      (hlaw n) (hcorrect n) (hdecBound n)

/-- The complete concrete reduction of Exercise 12.5(a), with both native adversaries and the
actual symmetric CCA game. The reduction code and polynomial clocks are fixed before `n`.
No security assumption is needed for this quantitative statement. -/
theorem exists_hybridCCA_reductions (E : SymmetricCipher)
    {keyLen : ℕ → ℕ} {F : ℕ → List Bool → List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun ⟨n, sk, ct⟩ => decaps n sk ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits))
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hlaw : ∀ n, (BitString.uniformList (keyLen n)).map (F n) = ProbComp.eval (E.keyGen n))
    (hcorrect : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
      ∀ kc ∈ (ProbComp.eval (encaps n keys.1)).support, decaps n keys.2 kc.2 = some kc.1)
    (adversary : WordCCA2Adversary) (hA : adversary.IsPPT) :
    let encaps' := fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk
    let decaps' := fun n sk ct => (decaps n sk ct).map (F n)
    ∃ (Bkem : OracleDistinguisher) (Bs : CCAAdversary),
      IsOraclePPT encBool Bkem ∧ IsOraclePPT encBool Bs ∧ ∀ n,
      Game.advantage
        (ProbComp.eval (cca2GameOn
          (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits keyGen
          (hybridEncrypt encaps' E.encrypt) (hybridDecrypt decaps' E.decrypt) adversary false n))
        (ProbComp.eval (cca2GameOn
          (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits keyGen
          (hybridEncrypt encaps' E.encrypt) (hybridDecrypt decaps' E.decrypt) adversary true n)) ≤
        2 * Game.advantage (ProbComp.eval (kemCCARealGame keyGen encaps decaps Bkem n))
          (ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps Bkem n)) +
        Game.advantage (ProbComp.eval (E.ccaOneTimeGame Bs false n))
          (ProbComp.eval (E.ccaOneTimeGame Bs true n)) := by
  dsimp only
  obtain ⟨decBound, hdecPoly, hdec⟩ := exists_decryption_length_bound hkeyGen hdecaps
  obtain ⟨ctBound, hctPoly, hct⟩ := E.exists_ciphertext_length_bound
  obtain ⟨symBound, hsymPoly, hsym⟩ := E.exists_decryption_length_bound
  refine ⟨hybridToKEMCCAHiddenBit E F decBound adversary,
    hybridToOneTimeCCAAdversary E keyGen
      (fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk)
      (fun n sk ct => (decaps n sk ct).map (F n)) ctBound symBound adversary,
    isOraclePPT_hybridToKEMCCAHiddenBit E hF hdecPoly hA,
    isOraclePPT_hybridToOneTimeCCAAdversary E hkeyGen
      (isPPTOn_postprocessed_encaps hF hencaps)
      (computableInPolyTime_postprocessed_decaps hF hdecaps) hctPoly hsymPoly hA, ?_⟩
  intro n
  have h := advantage_hybridCCA_le_two_mul E keyLen F keyGen encaps decaps decBound
    adversary n (hlaw n) (hcorrect n) (hdec n)
  dsimp only at h
  rw [eval_hybridDEMGame E _ _ _ ctBound symBound adversary false n (hct n) (hsym n),
    eval_hybridDEMGame E _ _ _ ctBound symBound adversary true n (hct n) (hsym n)] at h
  exact h

/-- Native runtime of the actual postprocessed hybrid game, including both decryption phases.
No security or key-distribution assumption is required for runtime. -/
theorem isPPTOn_hybridCCAGame (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun ⟨n, sk, ct⟩ => decaps n sk ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits))
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn encUnary encBool (cca2GameOn
      (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits keyGen
      (hybridEncrypt (fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk) E.encrypt)
      (hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt) adversary bit) :=
  isPPTOn_cca2GameOn (by fun_prop) hkeyGen
    (isPPTOn_hybridEncrypt (isPPTOn_postprocessed_encaps hF hencaps) E.encrypt_ppt)
    (computableInPolyTime_hybridDecrypt
      (computableInPolyTime_postprocessed_decaps hF hdecaps) E.decrypt_polyTime) hA bit

/-- Perfect decryption correctness requires postprocessed real encapsulation keys to be
supported by the DEM. An ideal-key sampler identity alone does not assert this real-key fact. -/
theorem hybridDecrypt_postprocessed_hybridEncrypt (E : SymmetricCipher)
    {F : ℕ → List Bool → List Bool}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    {n : ℕ} {pk sk ct : List Bool} {msg : List Bool}
    (hcorrect : ∀ kc ∈ (ProbComp.eval (encaps n pk)).support, decaps n sk kc.2 = some kc.1)
    (hsupport : ∀ kc ∈ (ProbComp.eval (encaps n pk)).support,
      F n kc.1 ∈ (ProbComp.eval (E.keyGen n)).support)
    (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval (hybridEncrypt
      (fun n pk => (fun kc => (F n kc.1, kc.2)) <$> encaps n pk) E.encrypt n pk msg)).support) :
    hybridDecrypt (fun n sk ct => (decaps n sk ct).map (F n)) E.decrypt n sk ct = some msg := by
  apply hybridDecrypt_hybridEncrypt (hct := hct)
  · intro k ctK hk
    rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hk
    obtain ⟨kc, hkc, hpair⟩ := hk
    cases hpair
    rw [hcorrect kc hkc]
    rfl
  · intro k ctD hk hctD
    obtain ⟨ctK, hk⟩ := hk
    rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hk
    obtain ⟨kc, hkc, hpair⟩ := hk
    cases hpair
    exact E.decrypt_encrypt n _ (hsupport kc hkc) msg hmsg ctD hctD

end Cslib.Crypto.Encryption
