/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Hybrid.CCA
public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Tactic.PPT

/-!
# The symmetric-cipher leg of hybrid CCA security

This intermediate experiment uses the symmetric cipher's actual key distribution. Its
distinguished encapsulation component is redirected to that key before and after the challenge.
This is the DEM leg of [BonehShoup2023], Exercise 12.5(a), not the full KEM–DEM composition:
the two KEM hops and compatibility of the KEM's ideal key distribution remain separate.

## Main definitions

* `Cslib.Crypto.Encryption.hybridDEMGame`: the existing two-phase CCA game with a hidden DEM key.
* `Cslib.Crypto.Encryption.hybridDEMHandler`: canonical parsing and bounded oracle forwarding.
* `Cslib.Crypto.Encryption.hybridToOneTimeCCAAdversary`: the one-time symmetric CCA reduction.

## Main results

* `Cslib.Crypto.Encryption.eval_hybridDEMGame`: exact equality with the symmetric experiment.
* `Cslib.Crypto.Encryption.isOraclePPT_hybridToOneTimeCCAAdversary`: native reduction certificate.
* `Cslib.Crypto.Encryption.isPPTOn_hybridDEMGame`: native certificate for the closed game.
* `Cslib.Crypto.SymmetricCipher.OneTimeINDCCA.indistinguishable_hybridDEMGame`:
  the loss-one DEM leg.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 12.5(a), printed p. 513.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- The DEM intermediate game. Original KEM keys and encapsulation retain their joint law;
the independently sampled DEM key is used for the distinguished component in both phases.
The source symmetric experiment admits exactly `n`-bit challenge messages. -/
noncomputable def hybridDEMGame (E : SymmetricCipher)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let encapsulated ← encaps n keys.1
  let k ← E.keyGen n
  cca2GameOn (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits
    (fun _ => pure keys)
    (fun n _ msg => (fun ct => encPair encBits encBits (encapsulated.2, ct)) <$>
      E.encrypt n k msg)
    (hybridDecrypt (fun n sk ct =>
      if ct == encapsulated.2 then some k else decaps n sk ct) E.decrypt)
    adversary bit n

/-- Forward only canonical ciphertexts with the distinguished KEM component. All other
canonical ciphertexts use local decapsulation and decryption. A bounded raw reply preserves
the distinction between rejection (`[]`) and a successful empty message (`[true]`). -/
noncomputable def hybridDEMHandler (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (sk ctK : List Bool)
    (request : Unit × List Bool) : WordOracleComp Bool (List Bool) :=
  if encPair encBits encBits (unframe request.2, dropFrame request.2) == request.2 then
    if unframe request.2 == ctK then
      List.take (decBound n (dropFrame request.2)) <$>
        ProbOracleComp.query (true, dropFrame request.2)
    else
      pure (encOption encBits (hybridDecrypt decaps E.decrypt n sk request.2))
  else pure []

/-- Both CCA phases for fixed original KEM keys and encapsulation. The hidden symmetric key
is owned by the external oracle and is never an argument to this continuation. -/
noncomputable def hybridDEMContinuation (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (n : ℕ) (pk sk ctK : List Bool) :
    WordOracleComp Bool Bool := do
  let handler := hybridDEMHandler E decaps decBound n sk ctK
  let choice ← OracleComp.interpret
    (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m)) handler)
    (adversary.choose n pk)
  if (ChoiceOut.msg₀ choice).length == n && (ChoiceOut.msg₁ choice).length == n then
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query
      (false, encPair encBits encBits (ChoiceOut.msg₀ choice, ChoiceOut.msg₁ choice))
    OracleComp.interpret
      (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m)) handler)
      (adversary.guess n (ChoiceOut.state choice)
        (encPair encBits encBits (ctK, ct)))
  else pure false

/-- Simulate both public-key CCA phases, making exactly one valid symmetric encryption query
when the selected messages have length `n`. In particular, an empty encryption reply is a
legitimate ciphertext, not a rejection marker. The original encapsulated key is not exposed. -/
noncomputable def hybridToOneTimeCCAAdversary (E : SymmetricCipher)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) : CCAAdversary := fun n _ => do
  let keys ← ProbOracleComp.sample (keyGen n)
  let encapsulated ← ProbOracleComp.sample (encaps n keys.1)
  hybridDEMContinuation E decaps ctBound decBound adversary n keys.1 keys.2 encapsulated.2

/-- Before the challenge, the distinguished component uses the hidden DEM key, including
queries made before the adversary has selected its messages. -/
theorem run_hybridDEMHandler_before (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (sk ctK k : List Bool) (bit : Bool)
    (hbound : ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct)
    (request : Unit × List Bool) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.oneTimeCCAOracle n k bit))
      (hybridDEMHandler E decaps decBound n sk ctK request)).run [] =
      pure (encOption encBits (hybridDecrypt
        (fun n sk ct => if ct == ctK then some k else decaps n sk ct)
        E.decrypt n sk request.2), []) := by
  simp only [hybridDEMHandler, hybridDecrypt]
  split_ifs with hcanonical hkem
  · simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query]
    change (pure (List.take (decBound n (dropFrame request.2))
      (encOption encBits (E.decrypt n k (dropFrame request.2))), []) :
        ProbComp (List Bool × List (List Bool))) = _
    rw [List.take_of_length_le (hbound _)]
    rfl
  · simp only [OracleComp.interpret_pure, StateT.run_pure]
  · simp only [OracleComp.interpret_pure, StateT.run_pure, encOption_none]

/-- After the challenge, symmetric challenge rejection agrees with exact hybrid-word
rejection. Canonical framing is essential: another spelling of the same projections is rejected
before it can reach the symmetric oracle. -/
theorem run_hybridDEMHandler_after (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (sk ctK k ctD : List Bool) (bit : Bool)
    (hbound : ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct)
    (request : Unit × List Bool) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.oneTimeCCAOracle n k bit))
      (hybridDEMHandler E decaps decBound n sk ctK request)).run [ctD] =
      pure (if request.2 == encPair encBits encBits (ctK, ctD) then [] else
        encOption encBits (hybridDecrypt
          (fun n sk ct => if ct == ctK then some k else decaps n sk ct)
          E.decrypt n sk request.2), [ctD]) := by
  by_cases hc : encPair encBits encBits (unframe request.2, dropFrame request.2) = request.2
  · by_cases hk : unframe request.2 = ctK
    · have heq : request.2 = encPair encBits encBits (ctK, ctD) ↔
          dropFrame request.2 = ctD := by
        rw [← hc, (encPair encBits encBits).injective.eq_iff, Prod.mk.injEq, hk]
        simp
      have hc' : encPair encBits encBits (ctK, dropFrame request.2) = request.2 := by
        simpa only [hk] using hc
      simp only [hybridDEMHandler, hybridDecrypt, beq_iff_eq, hk, hc', ↓reduceIte,
        OracleComp.interpret_map, ProbOracleComp.interpret_query, heq]
      simp only [StateT.run_map]
      dsimp only [StateT.run, SymmetricCipher.oneTimeCCAOracle]
      by_cases hd : dropFrame request.2 = ctD
      · simp [hd]
      · simp [hd, List.take_of_length_le (hbound _)]
    · have hne : request.2 ≠ encPair encBits encBits (ctK, ctD) := by
        intro h
        apply hk
        simpa only [encPair_apply, encBits_apply, unframe_frame_append] using congrArg unframe h
      simp only [hybridDEMHandler, hybridDecrypt, beq_iff_eq, hc, hk, hne, ↓reduceIte,
        OracleComp.interpret_pure, StateT.run_pure]
  · have hne : request.2 ≠ encPair encBits encBits (ctK, ctD) := by
      intro h
      apply hc
      simp [h]
    simp only [hybridDEMHandler, hybridDecrypt, beq_iff_eq, hc, hne, ↓reduceIte,
      OracleComp.interpret_pure, StateT.run_pure, encOption_none]

private theorem eval_run_substituted_phase {α : Type}
    (oracle : Bool × List Bool → StateT (List (List Bool)) ProbComp (List Bool))
    (handler : Unit × List Bool → WordOracleComp Bool (List Bool))
    (reply : Unit × List Bool → List Bool) (state : List (List Bool))
    (hstep : ∀ request, (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (handler request)).run state = pure (reply request, state))
    (program : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m)) handler)
        program)).run state) =
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (fun request (s : Unit) => pure (reply request, s))) program).run ())).map
            (fun result => (result.1, state)) := by
  let ext := OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
    (fun request s => ProbComp.eval (oracle request s))
  have hsim := ProbOracleComp.run_interpret_map_state
    (fun request (s : Unit) => PMF.pure (reply request, s))
    (fun request => OracleComp.interpret ext (handler request))
    (fun _ : Unit => state) (fun request s => by
      have h := congrArg ProbComp.eval (hstep request)
      simp only [ProbOracleComp.eval_run_interpret, ProbComp.eval_pure] at h
      simpa only [PMF.pure_map, ext, StateT.run] using h.symm) program ()
  rw [ProbOracleComp.eval_run_interpret, OracleComp.interpret_interpret]
  have hhandler : (fun q => OracleComp.interpret ext
      (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m)) handler q)) =
      OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun request => OracleComp.interpret ext (handler request)) := by
    funext q
    cases q with
    | inl m =>
      simp only [OracleComp.sumHandler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
        OracleComp.interpret_query, ext]
    | inr request => rfl
  change (OracleComp.interpret
    (fun q => OracleComp.interpret ext
      (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m)) handler q))
      program).run state = _
  rw [hhandler, ← hsim, ProbOracleComp.eval_run_interpret]
  rfl

private theorem eval_run_hybridDEMContinuation (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ) (pk sk ctK k : List Bool)
    (hct : ∀ msg, msg.length = n → ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support,
      ct.length ≤ ctBound n)
    (hdec : ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    ProbComp.eval (do
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (E.oneTimeCCAOracle n k bit))
        (hybridDEMContinuation E decaps ctBound decBound adversary n pk sk ctK)).run []
      return out.1) =
    ProbComp.eval (cca2GameOn (fun n _ m0 m1 => (m0.length == n) && (m1.length == n))
      encBits (fun _ => pure (pk, sk))
      (fun n _ msg => (fun ct => encPair encBits encBits (ctK, ct)) <$> E.encrypt n k msg)
      (hybridDecrypt (fun n sk ct => if ct == ctK then some k else decaps n sk ct) E.decrypt)
      adversary bit n) := by
  let decrypt := hybridDecrypt
    (fun n sk ct => if ct == ctK then some k else decaps n sk ct) E.decrypt
  have hchoose := eval_run_substituted_phase (E.oneTimeCCAOracle n k bit)
    (hybridDEMHandler E decaps decBound n sk ctK)
    (fun request => encOption encBits (decrypt n sk request.2)) []
    (run_hybridDEMHandler_before E decaps decBound n sk ctK k bit hdec)
    (adversary.choose n pk)
  simp only [hybridDEMContinuation, cca2GameOn, OracleComp.interpret_bind, StateT.run_bind,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
  rw [hchoose]
  simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind]
  apply PMF.bind_congr_on_support
  intro choice hchoice
  by_cases hvalid : ((ChoiceOut.msg₀ choice.1).length == n &&
      (ChoiceOut.msg₁ choice.1).length == n) = true
  · simp only [hvalid, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
      OracleComp.interpret_map, ProbOracleComp.interpret_query, StateT.run_map,
      ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    have henc : (E.oneTimeCCAOracle n k bit
        (false, encPair encBits encBits
          (ChoiceOut.msg₀ choice.1, ChoiceOut.msg₁ choice.1))).run [] =
        (do let ct ← E.encrypt n k
              (if bit then ChoiceOut.msg₁ choice.1 else ChoiceOut.msg₀ choice.1)
            return (ct, [ct])) := by
      simp [StateT.run, SymmetricCipher.oneTimeCCAOracle, encPair_apply, encBits_apply,
        unframe_frame_append, dropFrame_frame_append, hvalid]
    rw [henc]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    apply PMF.bind_congr_on_support
    intro ct hmem
    have hlen : (if bit then ChoiceOut.msg₁ choice.1 else ChoiceOut.msg₀ choice.1).length = n := by
      have h := hvalid
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      split_ifs <;> first | exact h.1 | exact h.2
    rw [List.take_of_length_le (hct _ hlen ct hmem)]
    have hguess := eval_run_substituted_phase (E.oneTimeCCAOracle n k bit)
      (hybridDEMHandler E decaps decBound n sk ctK)
      (fun request => if request.2 == encPair encBits encBits (ctK, ct) then [] else
        encOption encBits (decrypt n sk request.2)) [ct]
      (run_hybridDEMHandler_after E decaps decBound n sk ctK k ct bit hdec)
      (adversary.guess n (ChoiceOut.state choice.1) (encPair encBits encBits (ctK, ct)))
    rw [hguess]
    simp only [PMF.bind_map, Function.comp_def]
    have hp : (fun request (s : Unit) =>
        (pure (if request.2 == encPair encBits encBits (ctK, ct) then [] else
          encOption encBits (decrypt n sk request.2), s) : ProbComp (List Bool × Unit))) =
        cca2Phase2Oracle encBits decrypt n sk (encPair encBits encBits (ctK, ct)) := by
      funext request s
      unfold cca2Phase2Oracle
      split_ifs <;> rfl
    rw [hp]
  · simp only [hvalid]
    change (PMF.pure (false, ([] : List (List Bool)))).bind (fun a => PMF.pure a.1) = _
    exact PMF.pure_bind _ _

/-- Exact, loss-one DEM game identity. Bounds apply only to keys in the actual symmetric key
sampler's support and to valid `n`-bit encryption inputs. Neither uniform encoded keys nor KEM
correctness is assumed for this intermediate-game identity. -/
theorem eval_hybridDEMGame (E : SymmetricCipher)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ)
    (hct : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n → ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support,
        ct.length ≤ ctBound n)
    (hdec : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    ProbComp.eval (hybridDEMGame E keyGen encaps decaps adversary bit n) =
      ProbComp.eval (E.ccaOneTimeGame
        (hybridToOneTimeCCAAdversary E keyGen encaps decaps ctBound decBound adversary) bit n) := by
  symm
  simp only [hybridDEMGame, SymmetricCipher.ccaOneTimeGame, hybridToOneTimeCCAAdversary,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret,
    OracleComp.interpret_bind, StateT.run_bind,
    ProbOracleComp.run_interpret_sample, PMF.bind_map, Function.comp_def, PMF.bind_bind]
  rw [PMF.bind_comm]
  apply PMF.bind_congr_on_support
  intro keys _
  rw [PMF.bind_comm]
  apply PMF.bind_congr_on_support
  intro encapsulated _
  apply PMF.bind_congr_on_support
  intro k hk
  simpa only [ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret] using
    eval_run_hybridDEMContinuation E decaps ctBound decBound adversary bit n keys.1 keys.2
      encapsulated.2 k (hct k hk) (hdec k hk)

/-- Native bounded-read implementation of the canonical forwarding handler. -/
@[fun_prop]
theorem isOraclePPTOn_hybridDEMHandler (E : SymmetricCipher)
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {sk ctK request : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hsk : ComputableInPolyTime sk input encBits)
    (hctK : ComputableInPolyTime ctK input encBits)
    (hrequest : ComputableInPolyTime request input encBits) :
    IsOraclePPTOn input encBits (fun a =>
      hybridDEMHandler E decaps decBound (n a) (sk a) (ctK a) ((), request a)) := by
  have hkem := ComputableInPolyTime.unframe.comp hrequest
  have hdem := ComputableInPolyTime.dropFrame.comp hrequest
  have hcanonical := ComputableInPolyTime.beq (encB := encBits)
    (hkem.prod hdem).encoding_comp hrequest
  have hkey := ComputableInPolyTime.beq (encB := encBits) hkem hctK
  have hlocal := (computableInPolyTime_hybridDecrypt hdecaps E.decrypt_polyTime).comp
    (hn.prod (hsk.prod hrequest))
  unfold hybridDEMHandler
  exact IsOraclePPTOn.cond' hcanonical
    (IsOraclePPTOn.cond' hkey
      (IsOraclePPTOn.query_take' true hdem (hdecBound.comp (hn.prod hdem)))
      hlocal.encoding_comp.isOraclePPTOn)
    (ComputableInPolyTime.const []).isOraclePPTOn

private theorem isOraclePPTOn_hybridDEMInterpret (E : SymmetricCipher)
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {n : α → ℕ} {sk ctK : α → List Bool} {program : α → WordOracleComp Unit β}
    (hn : ComputableInPolyTime n input encUnary)
    (hsk : ComputableInPolyTime sk input encBits)
    (hctK : ComputableInPolyTime ctK input encBits)
    (hprogram : IsOraclePPTOn input output program) :
    IsOraclePPTOn input output (fun a => OracleComp.interpret
      (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m))
        (hybridDEMHandler E decaps decBound (n a) (sk a) (ctK a))) (program a)) := by
  have hhandler : IsOraclePPTOn (encPair input (encPair (encFinEnum Unit) encBits)) encBits
      (fun p : α × (Unit × List Bool) =>
        hybridDEMHandler E decaps decBound (n p.1) (sk p.1) (ctK p.1) p.2) :=
    isOraclePPTOn_hybridDEMHandler E hdecaps hdecBound
      (hn.comp (by fun_prop)) (hsk.comp (by fun_prop)) (hctK.comp (by fun_prop)) (by fun_prop)
  let resources := fun (a : α) (ct : List Bool) => decBound (n a) (dropFrame ct) +
    (encOption encBits (hybridDecrypt decaps E.decrypt (n a) (sk a) ct)).length
  have hres : ComputableInPolyTime (fun p : α × List Bool => resources p.1 p.2)
      (encPair input encBits) encUnary := by
    have hp := ComputableInPolyTime.fst input encBits
    have hq := ComputableInPolyTime.snd input encBits
    have hlocal := (computableInPolyTime_hybridDecrypt hdecaps E.decrypt_polyTime).comp
      ((hn.comp hp).prod ((hsk.comp hp).prod hq))
    exact ComputableInPolyTime.unary_add'
      (hdecBound.comp ((hn.comp hp).prod (ComputableInPolyTime.dropFrame.comp hq)))
      (ComputableInPolyTime.length_bits.comp hlocal.encoding_comp)
  apply hprogram.interpret_preprocess_open' ComputableInPolyTime.id' hhandler hres
  intro a request reply hreply
  unfold hybridDEMHandler at hreply
  split_ifs at hreply
  · obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    exact (List.length_take_le _ _).trans (Nat.le_add_right _ _)
  · cases OracleComp.eq_of_mem_supportWith_pure hreply
    exact Nat.le_add_left _ _
  · cases OracleComp.eq_of_mem_supportWith_pure hreply
    exact Nat.zero_le _

/-- Native implementation of both phases with a captured KEM environment. External replies
are read only up to the supplied unary-computable limits. -/
theorem isOraclePPTOn_hybridDEMContinuation (E : SymmetricCipher)
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {ctBound : ℕ → ℕ} (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {pk sk ctK : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hsk : ComputableInPolyTime sk input encBits)
    (hctK : ComputableInPolyTime ctK input encBits) :
    IsOraclePPTOn input encBool (fun a =>
      hybridDEMContinuation E decaps ctBound decBound adversary (n a) (pk a) (sk a) (ctK a)) := by
  let C := encPair (encPair encBits encBits) encBits
  have hchoose := isOraclePPTOn_hybridDEMInterpret E hdecaps hdecBound hn hsk hctK
    (hA.choose.on.preprocess' (hn.prod hpk))
  have hp := ComputableInPolyTime.fst input C
  have hc := ComputableInPolyTime.snd input C
  have hn1 := hn.comp hp
  have hsk1 := hsk.comp hp
  have hk1 := hctK.comp hp
  have hm0 := hc.fst'.fst'
  have hm1 := hc.fst'.snd'
  have hquery := IsOraclePPTOn.query_take' false (hm0.prod hm1).encoding_comp
    (hctBound.comp hn1)
  have hbase := ComputableInPolyTime.fst (encPair input C) encBits
  have hct := ComputableInPolyTime.snd (encPair input C) encBits
  have hn2 := hn1.comp hbase
  have hsk2 := hsk1.comp hbase
  have hk2 := hk1.comp hbase
  have hguess := isOraclePPTOn_hybridDEMInterpret E hdecaps hdecBound hn2 hsk2 hk2
    (hA.guess.preprocess' (hn2.prod
      ((hc.snd'.comp hbase).prod (hk2.prod hct).encoding_comp)))
  have hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.2.1.length == p.1) && (p.2.2.length == p.1))
      (encPair encUnary (encPair encBits encBits)) encBool := by fun_prop
  have hcondition := hvalid.comp (hn1.prod (hm0.prod hm1))
  unfold hybridDEMContinuation
  exact hchoose.bind_with (IsOraclePPTOn.cond' hcondition (hquery.bind_with hguess)
    (ComputableInPolyTime.const false).isOraclePPTOn)

/-- The complete reduction is uniform strict oracle PPT. Key generation, encapsulation,
local decapsulation/decryption, both adaptive phases, and bounded external reads are charged. -/
theorem isOraclePPT_hybridToOneTimeCCAAdversary (E : SymmetricCipher)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {ctBound : ℕ → ℕ} (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT) :
    IsOraclePPT encBool
      (hybridToOneTimeCCAAdversary E keyGen encaps decaps ctBound decBound adversary) := by
  let I := encPair encUnary encBits
  let K := encPair encBits encBits
  have hn := ComputableInPolyTime.fst encUnary encBits
  have hp := ComputableInPolyTime.fst I K
  have hk := ComputableInPolyTime.snd I K
  have hq := ComputableInPolyTime.fst (encPair I K) K
  have he := ComputableInPolyTime.snd (encPair I K) K
  have hfirst := (hkeyGen.isOraclePPTOn (Operation := Bool)).preprocess' hn
  have hsecond := (hencaps.isOraclePPTOn (Operation := Bool)).preprocess'
    ((hn.comp hp).prod hk.fst')
  have hlast := isOraclePPTOn_hybridDEMContinuation E hdecaps hctBound hdecBound hA
    (hn.comp (hp.comp hq)) (hk.fst'.comp hq) (hk.snd'.comp hq) he.snd'
  apply IsOraclePPTOn.isOraclePPT
  unfold hybridToOneTimeCCAAdversary
  exact hfirst.bind_with (hsecond.bind_with hlast)

/-- The intermediate game itself has a uniform strict-PPT realization, including the hidden
symmetric key sampler and every adaptive decryption reply. -/
@[program_certificate]
theorem isPPTOn_hybridDEMGame (E : SymmetricCipher)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn encUnary encBool (hybridDEMGame E keyGen encaps decaps adversary bit) := by
  obtain ⟨ctBound, hctPoly, hct⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨decBound, hdecPoly, hdec⟩ := E.exists_decryption_length_bound
  have hrun := E.isPPTOn_ccaOneTimeGame
    (isOraclePPT_hybridToOneTimeCCAAdversary E hkeyGen hencaps hdecaps hctPoly hdecPoly hA) bit
  exact hrun.congr fun n =>
    (eval_hybridDEMGame E keyGen encaps decaps ctBound decBound adversary bit n
      (hct n) (hdec n)).symm

/-- The DEM leg of [BonehShoup2023], Exercise 12.5(a): one-time symmetric CCA security
indistinguishes the two intermediate games with loss one. The two KEM hops and their
ideal-key sampler compatibility remain separate obligations for full composition. -/
theorem _root_.Cslib.Crypto.SymmetricCipher.OneTimeINDCCA.indistinguishable_hybridDEMGame
    {E : SymmetricCipher} (hsecure : E.OneTimeINDCCA)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits)) :
    Game.Indistinguishable
      (fun A n => ProbComp.eval (hybridDEMGame E keyGen encaps decaps A false n))
      (fun A n => ProbComp.eval (hybridDEMGame E keyGen encaps decaps A true n))
      WordCCA2Adversary.IsPPT := by
  intro adversary hA
  obtain ⟨ctBound, hctPoly, hct⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨decBound, hdecPoly, hdec⟩ := E.exists_decryption_length_bound
  have h := hsecure (hybridToOneTimeCCAAdversary E keyGen encaps decaps ctBound decBound adversary)
    (isOraclePPT_hybridToOneTimeCCAAdversary E hkeyGen hencaps hdecaps hctPoly hdecPoly hA)
  refine h.congr fun n => ?_
  dsimp only
  rw [eval_hybridDEMGame E keyGen encaps decaps ctBound decBound adversary false n (hct n) (hdec n),
    eval_hybridDEMGame E keyGen encaps decaps ctBound decBound adversary true n (hct n) (hdec n)]

end Cslib.Crypto.Encryption
