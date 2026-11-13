/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TCRSignature
public import CslibFrontier.Crypto.Computational.WordSignature
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT

/-!
# Many-time fresh-key TCR hash-and-sign on arbitrary-length bit words

`TCRSignature.scheme` instantiates construction `(13.2)` of [BonehShoup2023], Section 13.2.1 over a
**one-time** signature scheme `S` to build a capacity-`1` `IndexedSignatureScheme`. This module
formalizes [BonehShoup2023], Section 13.2.1 (construction `(13.2)` on p. 533 and Theorem 13.2 on
p. 534) in its full **many-time** form: given any stateless many-time `EUFCMA`-secure
`SignatureScheme` `S` on fixed-length bit strings and any unrestricted target collision-resistant
`KeyedHashFamily` `H` on `List Bool`, `TCRSignature.wordScheme S H` is a stateless many-time
`WordSignatureScheme` satisfying `WordSignatureScheme.EUFCMA` on **arbitrary-length `List Bool`
messages**:

1. **Construction (`TCRSignature.wordScheme`)**: reuses `TCRSignature.keyGen S H`, signs any
   `msg : List Bool` via `TCRSignature.sign S H sk 0 msg` (sampling a fresh `H.keyLen n`-bit hash
   key `k` per signature and signing `otsMsg H n k (H.eval n k msg)` under `S`), and verifies via
   `TCRSignature.verify S H pk 0 msg sig`.
2. **Many-query security reduction (`exists_reduction_wordScheme_eufCmaGame_le`,
   `SignatureScheme.EUFCMA.eufCMA_wordScheme`)**: following the proof of [BonehShoup2023], Theorem
   13.2 (p. 534), every valid forgery `(m*, (k*, ots*))` against `wordScheme S H` after arbitrarily
   many adaptive signing queries `(m_1, k_1), …, (m_Q, k_Q)` satisfies one of two cases:
   * **Type I (`manyTimeForger`)**: `M* = otsMsg H n k* (H.eval n k* m*)` differs from every word
     `otsMsg H n k_r (H.eval n k_r m_r)` signed during the run, winning `S.eufCmaGame` with factor
     `1`.
   * **Type II (`tcrMultiAdversary`)**: `M* = otsMsg H n k_r (H.eval n k_r m_r)` for some signing
     query step, so `otsMsg_inj` forces `k* = k_r` and `H.eval n k_r m_r = H.eval n k_r m*` while
     freshness `m* ∉ queried` forces `m_r ≠ m*`. Guessing the challenge machine step via
     `sampleDyadicIndex (fuelUpper ... n)` commits `m_r` before `k_r` is sampled, implants the
     external challenge hash key at that step, and finishes the remaining steps locally under `S`,
     winning `targetCollisionGame` with polynomial loss `dyadicSize (fuelUpper ... n)`.
3. **Cryptographic consequences (`WordSignatureScheme.EUFCMA.exists_oneWay`,
   `OneWay.exists_wordEUFCMA_of_targetCollisionResistant`, `OneWayPermutation.exists_wordEUFCMA`)**:
   combining `OneWay.exists_eufCMA_of_targetCollisionResistant` with `eufCMA_wordScheme` yields
   stateless many-time `WordSignatureScheme`s on unrestricted `List Bool` messages from any one-way
   function plus a target collision-resistant `KeyedHashFamily` (and unconditionally from any
   `OneWayPermutation` via `naorYungHash`).

## Main definitions

* `Cslib.Crypto.TCRSignature.wordScheme`: stateless many-time `WordSignatureScheme` on arbitrary
  `List Bool` messages via per-signature fresh-key TCR hash-and-sign.
* `Cslib.Crypto.TCRSignature.manyTimeHandler`, `Cslib.Crypto.TCRSignature.manyTimeForger`: open
  oracle reduction to `SignatureScheme.eufCmaGame`.
* `Cslib.Crypto.TCRSignature.TraceStep`, `Cslib.Crypto.TCRSignature.TcrSavedState`,
  `Cslib.Crypto.TCRSignature.replayStep`, `Cslib.Crypto.TCRSignature.replayCfg`,
  `Cslib.Crypto.TCRSignature.queryOf`, `Cslib.Crypto.TCRSignature.appendTraceStep`,
  `Cslib.Crypto.TCRSignature.sampleStep`, `Cslib.Crypto.TCRSignature.tcrMultiAdversary`:
  clocked step-guessing two-stage target-collision reduction across polynomially many signing
  queries.

## Main results

* `Cslib.Crypto.TCRSignature.isOraclePPT_manyTimeForger`,
  `Cslib.Crypto.TCRSignature.isPPT_tcrMultiAdversary`: uniform strict PPT certificates for both
  many-query reductions, proved with zero tidy-calculus bridge steps.
* `Cslib.Crypto.TCRSignature.succProbability_wordScheme_eufCmaGame_le_of_machine`,
  `Cslib.Crypto.TCRSignature.exists_reduction_wordScheme_eufCmaGame_le`: concrete Theorem 13.2
  security bound with polynomial query-slot loss `dyadicSize (fuelUpper ... n)`.
* `Cslib.Crypto.SignatureScheme.EUFCMA.eufCMA_wordScheme`: `TCRSignature.wordScheme S H` satisfies
  `WordSignatureScheme.EUFCMA` whenever `S` satisfies `SignatureScheme.EUFCMA` and `H` is target
  collision-resistant.
* `Cslib.Crypto.WordSignatureScheme.EUFCMA.exists_oneWay`,
  `Cslib.Crypto.OneWay.exists_wordEUFCMA_of_targetCollisionResistant`,
  `Cslib.Crypto.OneWayPermutation.exists_wordEUFCMA`: necessity and sufficiency bridges for
  unrestricted-message signatures.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 13.2.1 (construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534).
* [M. Naor, M. Yung, *Universal One-Way Hash Functions and their Cryptographic
  Applications*][NaorYung1989], Section 4.
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990].
-/

public section

namespace Cslib.Crypto

open Probability ProbComp _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace TCRSignature

/-! ### Stateless many-time `WordSignatureScheme` via fresh-key TCR hash-and-sign -/

/-- **Fresh-key TCR hash-and-sign stateless `WordSignatureScheme`** ([BonehShoup2023], Section
13.2.1, construction `(13.2)`, p. 533): signs arbitrary-length `List Bool` messages by sampling a
fresh `H.keyLen n`-bit hash key `k` inside every signature and signing `otsMsg H n k (H.eval n k m)`
under the fixed-length signature scheme `S` at security parameter `otsParam H n`. -/
@[expose]
noncomputable def wordScheme (S : SignatureScheme) (H : KeyedHashFamily) :
    WordSignatureScheme where
  keyGen := keyGen S H
  sign sk msg := sign S H sk 0 msg
  verify pk msg sig := verify S H pk 0 msg sig
  keyGen_ppt := (scheme S H).keyGen_ppt
  sign_ppt := by
    have hprep : ComputableInPolyTime
        (fun p : List Bool × List Bool => (p.1, 0, p.2))
        (encPair encBits encBits)
        (encPair encBits (encPair encUnary encBits)) :=
      (ComputableInPolyTime.fst _ _).prod
        ((ComputableInPolyTime.const 0).prod (ComputableInPolyTime.snd _ _))
    exact (scheme S H).sign_ppt.preprocess hprep
  verify_polyTime := by
    have hprep : ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool => (p.1, 0, p.2.1, p.2.2))
        (encPair encBits (encPair encBits encBits))
        (encPair encBits (encPair encUnary (encPair encBits encBits))) :=
      (ComputableInPolyTime.fst _ _).prod
        ((ComputableInPolyTime.const 0).prod (ComputableInPolyTime.snd _ _))
    exact hprep.trans (scheme S H).verify_polyTime
  verify_sign n pk sk hkeys msg sig hsig :=
    (scheme S H).verify_sign n (pk, sk) hkeys 0 Nat.zero_lt_one msg sig hsig

@[simp] theorem wordScheme_keyGen (S : SignatureScheme) (H : KeyedHashFamily) :
    (wordScheme S H).keyGen = keyGen S H := rfl

@[simp] theorem wordScheme_sign (S : SignatureScheme) (H : KeyedHashFamily)
    (sk msg : List Bool) :
    (wordScheme S H).sign sk msg = sign S H sk 0 msg := rfl

@[simp] theorem wordScheme_verify (S : SignatureScheme) (H : KeyedHashFamily)
    (pk msg sig : List Bool) :
    (wordScheme S H).verify pk msg sig = verify S H pk 0 msg sig := rfl

/-! ### Type-I reduction: open stateless signing-oracle simulation (`manyTimeForger`) -/

/-- Open stateless handler answering each signing query `msg` at parameter `n` by sampling a fresh
`H.keyLen n`-bit hash key `k`, querying the external `S`-signing oracle on
`otsMsg H n k (H.eval n k msg)` (truncated to `sigBound n`), and returning `(k, ots)`. -/
noncomputable def manyTimeHandler (H : KeyedHashFamily) (sigBound : ℕ → ℕ) (n : ℕ)
    (request : Unit × List Bool) (_ : Unit) : WordOracleComp Unit (List Bool × Unit) := do
  let k ← ProbOracleComp.sample (BitString.sampleList (H.keyLen n))
  let ots ← List.take (sigBound n) <$>
    ProbOracleComp.query ((), otsMsg H n k (H.eval n k request.2))
  return (encPair encBits encBits (k, ots), ())

/-- Many-time signature forger against `S` at parameter `M = otsParam H n`: recovers
`n := otsParamInv H M`, runs `adversary n (encPair encUnary encBits (n, otvk))` against
`manyTimeHandler H sigBound n`, and translates any output `(m*, (k*, ots*))` into the fixed-length
`S`-forgery `(otsMsg H n k* (H.eval n k* m*), ots*)`. -/
noncomputable def manyTimeForger (H : KeyedHashFamily) (sigBound : ℕ → ℕ)
    (adversary : Forger) : Forger :=
  fun M otvk =>
    let n := otsParamInv H M
    if otsParam H n = M then do
      let pk := simPkOf n otvk
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (manyTimeHandler H sigBound n))
        (adversary n pk)).run ()
      return otsForgeryOf H n out.1.1 out.1.2
    else
      pure ([], [])

private theorem isOraclePPTOn_manyTimeHandler (H : KeyedHashFamily) {sigBound : ℕ → ℕ}
    (hsigBound : ComputableInPolyTime sigBound encUnary encUnary) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun ⟨caller, request, state⟩ => manyTimeHandler H sigBound caller.1 request state) := by
  let Caller := ℕ × List Bool
  let encCaller : Caller ↪ List Bool := encPair encUnary encBits
  let HIn := Caller × ((Unit × List Bool) × Unit)
  let encHIn : HIn ↪ List Bool :=
    encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hhandlerProj : IsOraclePPTOn (Operation := Unit) encHIn
      (encPair encBits (encFinEnum Unit))
      (fun pair : HIn => manyTimeHandler H sigBound pair.1.1 pair.2.1 pair.2.2) := by
    have hn : ComputableInPolyTime (fun pair : HIn => pair.1.1) encHIn encUnary :=
      (ComputableInPolyTime.fst _ _).fst'
    have hreq : ComputableInPolyTime (fun pair : HIn => pair.2.1.2) encHIn encBits :=
      (ComputableInPolyTime.snd _ _).fst'.snd'
    have hsampleK : IsOraclePPTOn (Operation := Unit) encHIn encBits
        (fun pair : HIn =>
          ProbOracleComp.sample (BitString.sampleList (H.keyLen pair.1.1))) :=
      ((H.keyLen_polyTime.comp hn).sampleList).isOraclePPTOn
    let Mid := HIn × List Bool
    let encMid : Mid ↪ List Bool := encPair encHIn encBits
    have hmIn : ComputableInPolyTime (fun q : Mid => q.1) encMid encHIn :=
      ComputableInPolyTime.fst _ _
    have hmK : ComputableInPolyTime (fun q : Mid => q.2) encMid encBits :=
      ComputableInPolyTime.snd _ _
    have hmN := hmIn.trans hn
    have hmReq := hmIn.trans hreq
    have hmOtsReq := computableInPolyTime_otsMsg_eval_comp H hmN hmK hmReq
    have hquery : IsOraclePPTOn (Operation := Unit) encMid encBits
        (fun q : Mid => List.take (sigBound q.1.1.1) <$>
          ProbOracleComp.query ((), otsMsg H q.1.1.1 q.2 (H.eval q.1.1.1 q.2 q.1.2.1.2))) :=
      IsOraclePPTOn.query_take' () (hmOtsReq.of_enc_eq fun _ => rfl)
        ((hmN.trans hsigBound).of_enc_eq fun _ => rfl)
    have hpack : ComputableInPolyTime
        (fun r : Mid × List Bool => (encPair encBits encBits (r.1.2, r.2), ()))
        (encPair encMid encBits) (encPair encBits (encFinEnum Unit)) := by
      have henc : ComputableInPolyTime (encPair encBits encBits)
          (encPair encBits encBits) encBits := .of_eq fun _ => rfl
      have hpair := (((ComputableInPolyTime.fst encMid encBits).trans hmK).prod
        (ComputableInPolyTime.snd encMid encBits)).trans henc
      exact hpair.prod (.const ())
    exact hsampleK.bind_pair (hquery.map_pair' hpack)
  refine hhandlerProj.congr fun ⟨caller, request, state⟩ _ _ _ => ?_
  dsimp only

private theorem isOraclePPTOn_run_manyTimeHandler (H : KeyedHashFamily) {sigBound : ℕ → ℕ}
    (hsigBound : ComputableInPolyTime sigBound encUnary encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encFinEnum Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (manyTimeHandler H sigBound caller.1))
          (adversary caller.1 (encPair encUnary encBits (caller.1, caller.2)))).run ()) := by
  let Caller := ℕ × List Bool
  let encCaller : Caller ↪ List Bool := encPair encUnary encBits
  have hprepare : ComputableInPolyTime
      (fun caller : Caller => (caller.1, encPair encUnary encBits (caller.1, caller.2)))
      encCaller (encPair encUnary encBits) := by
    have henc : ComputableInPolyTime (encPair encUnary encBits)
        (encPair encUnary encBits) encBits := .of_eq fun _ => rfl
    exact (ComputableInPolyTime.fst _ _).prod henc
  have hresources : ComputableInPolyTime
      (fun pair : Caller × List Bool =>
        2 * H.keyLen pair.1.1 + sigBound pair.1.1 + 2)
      (encPair encCaller encBits) encUnary := by
    have hn : ComputableInPolyTime (fun pair : Caller × List Bool => pair.1.1)
        (encPair encCaller encBits) encUnary :=
      (ComputableInPolyTime.fst _ _).fst'
    have htwoK := (ComputableInPolyTime.const 2).unary_mul' (hn.trans H.keyLen_polyTime)
    exact (htwoK.unary_add' (hn.trans hsigBound)).unary_add' (.const 2)
  apply hadversary.run_interpret_preprocess_open'
    (handler := fun (caller : Caller) request state =>
      manyTimeHandler H sigBound caller.1 request state)
    (prepare := fun caller : Caller =>
      (caller.1, encPair encUnary encBits (caller.1, caller.2)))
    (initial := fun _ : Caller => ())
    (resources := fun (caller : Caller) _ => 2 * H.keyLen caller.1 + sigBound caller.1 + 2)
    hprepare (isOraclePPTOn_manyTimeHandler H hsigBound) (.const ())
    (fun _ _ => True) (fun _ => trivial) hresources
  intro caller request state _ result hresult
  cases state
  simp only [manyTimeHandler, bind_map_left] at hresult
  obtain ⟨k, hk, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
  obtain ⟨raw, _, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
  obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
  have hkSupp : k ∈ (BitString.uniformList (H.keyLen caller.1)).support := by
    have h := (ProbOracleComp.support_sample (BitString.sampleList (H.keyLen caller.1))).subset hk
    rwa [BitString.eval_sampleList] at h
  have hkLen : k.length = H.keyLen caller.1 :=
    BitString.length_of_mem_support_uniformList hkSupp
  have htake : (raw.take (sigBound caller.1)).length ≤ sigBound caller.1 :=
    List.length_take_le _ _
  refine ⟨trivial, ?_, Nat.le_add_right _ _⟩
  dsimp only
  rw [length_encPair]
  simp only [encBits_apply, hkLen]
  omega

private theorem computableInPolyTime_manyTimePost (H : KeyedHashFamily) :
    ComputableInPolyTime
      (fun q : (ℕ × List Bool) × ((List Bool × List Bool) × Unit) =>
        otsForgeryOf H (otsParamInv H q.1.1) q.2.1.1 q.2.1.2)
      (encPair (encPair encUnary encBits) (encPair (encPair encBits encBits) (encFinEnum Unit)))
      (encPair encBits encBits) := by
  let Q := (ℕ × List Bool) × ((List Bool × List Bool) × Unit)
  let encQ : Q ↪ List Bool :=
    encPair (encPair encUnary encBits) (encPair (encPair encBits encBits) (encFinEnum Unit))
  have hqN : ComputableInPolyTime (fun q : Q => otsParamInv H q.1.1) encQ encUnary :=
    (computableInPolyTime_otsParamInv H).comp ((ComputableInPolyTime.fst _ _).fst')
  have hqM : ComputableInPolyTime (fun q : Q => q.2.1.1) encQ encBits :=
    (ComputableInPolyTime.snd _ _).fst'.fst'
  have hqSig : ComputableInPolyTime (fun q : Q => q.2.1.2) encQ encBits :=
    (ComputableInPolyTime.snd _ _).fst'.snd'
  exact computableInPolyTime_otsForgeryOf_comp H hqN hqM hqSig

/-- `manyTimeForger` is uniformly strict oracle PPT whenever `sigBound` is computable in plain
polynomial time on unary `n`. -/
theorem isOraclePPT_manyTimeForger (H : KeyedHashFamily) {sigBound : ℕ → ℕ}
    (hsigBound : ComputableInPolyTime sigBound encUnary encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (manyTimeForger H sigBound adversary) := by
  apply IsOraclePPTOn.isOraclePPT
  let In := ℕ × List Bool
  let encIn : In ↪ List Bool := encPair encUnary encBits
  have hM : ComputableInPolyTime (fun p : In => p.1) encIn encUnary :=
    ComputableInPolyTime.fst _ _
  have hotvk : ComputableInPolyTime (fun p : In => p.2) encIn encBits :=
    ComputableInPolyTime.snd _ _
  have hnIn : ComputableInPolyTime (fun p : In => otsParamInv H p.1) encIn encUnary :=
    (computableInPolyTime_otsParamInv H).comp hM
  have hcond : ComputableInPolyTime
      (fun p : In => decide (otsParam H (otsParamInv H p.1) = p.1)) encIn encBool :=
    ComputableInPolyTime.unary_eq' ((computableInPolyTime_otsParam H).comp hnIn) hM
  have hrunIn := (isOraclePPTOn_run_manyTimeHandler H hsigBound hadversary).preprocess'
    (hnIn.prod hotvk)
  have hactive := hrunIn.map_pair' (computableInPolyTime_manyTimePost H)
  have hempty : IsOraclePPTOn (Operation := Unit) encIn (encPair encBits encBits)
      (fun _ : In => pure ([], [])) :=
    (ComputableInPolyTime.const (encIn := encIn) (encOut := encPair encBits encBits)
      ([], [])).isOraclePPTOn
  exact IsOraclePPTOn.ite' hcond hactive hempty

/-! ### Deterministic step replay and bounded-growth trace sampling (`tcrMultiAdversary`) -/

section MultiSimulator

/-- One recorded machine step of the many-query trace sampler. -/
@[ext]
structure TraceStep where
  /-- Fair coin bit supplied to the machine transition at this step. -/
  coin : Bool
  /-- Fresh hash key chosen when this step queries the signing oracle. -/
  hashKey : List Bool
  /-- Signature from the underlying signature scheme (or `[]` when no query occurs). -/
  ots : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- Standard encoding of a `TraceStep`. -/
enc_structure encTraceStep : TraceStep where
  coin : encBool, hashKey : encBits, ots : encBits

attribute [fun_prop] encTraceStep_coin_polyTime encTraceStep_hashKey_polyTime
  encTraceStep_ots_polyTime encTraceStep_mk_polyTime

/-- Total decoder for raw `Forger` outputs `(msg, sig)`. -/
@[expose]
def msgSigDecoder : Decoder (encPair encBits encBits) :=
  sigDecoder

/-- Total decoder for `TraceStep`. -/
@[expose]
def traceStepDecoder : Decoder encTraceStep :=
  (Decoder.bool.pair (Decoder.bits.pair Decoder.bits)).map
    (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun s => (s.coin, s.hashKey, s.ots))
    (fun _ => rfl)
    (fun _ => rfl)

/-- Deterministically advance `cfg` by one `TraceStep`, truncating any query reply
`encPair encBits encBits (step.hashKey, step.ots)` to `limit` bits. -/
def replayStep {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (limit : ℕ) (cfg : FiniteConfig k Bool Control Unit)
    (step : TraceStep) : FiniteConfig k Bool Control Unit :=
  match cfg.tapes.state with
  | none => cfg
  | some state =>
    match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols step.coin with
    | .step action symbol move => cfg.step action symbol move
    | .query () next =>
      cfg.receive () next ((encPair encBits encBits (step.hashKey, step.ots)).take limit)

/-- Replay a full `List TraceStep` from `FiniteConfig.init machine.initial word`. -/
def replayCfg {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (limit : ℕ) (word : List Bool) (trace : List TraceStep) :
    FiniteConfig k Bool Control Unit :=
  trace.foldl (replayStep machine limit) (FiniteConfig.init machine.initial word)

/-- Inspect whether `machine` issues an external query from `cfg` on fair coin `coin`, returning
`some (cfg.channels ()).1` when it does and `none` otherwise. -/
def queryOf {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (cfg : FiniteConfig k Bool Control Unit) (coin : Bool) : Option (List Bool) :=
  match cfg.tapes.state with
  | none => none
  | some state =>
    match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols coin with
    | .step _ _ _ => none
    | .query () _ => some (cfg.channels ()).1

private theorem computableInPolyTime_replayStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Unit) :
    ComputableInPolyTime
      (fun q : (ℕ × FiniteConfig k Bool Control Unit) × TraceStep =>
        replayStep machine q.1.1 q.1.2 q.2)
      (encPair (encPair encUnary encFiniteConfig) encTraceStep)
      encFiniteConfig := by
  let Q := (ℕ × FiniteConfig k Bool Control Unit) × TraceStep
  let encQ : Q ↪ List Bool := encPair (encPair encUnary encFiniteConfig) encTraceStep
  have hlimit : ComputableInPolyTime (fun q : Q => q.1.1) encQ encUnary :=
    (ComputableInPolyTime.fst _ _).fst'
  have hcfg : ComputableInPolyTime (fun q : Q => q.1.2) encQ encFiniteConfig :=
    (ComputableInPolyTime.fst _ _).snd'
  have hstep : ComputableInPolyTime (fun q : Q => q.2) encQ encTraceStep :=
    ComputableInPolyTime.snd _ _
  have hcoin : ComputableInPolyTime (fun q : Q => q.2.coin) encQ encBool := by
    unfold encQ; fun_prop
  have hhash : ComputableInPolyTime (fun q : Q => q.2.hashKey) encQ encBits := by
    unfold encQ; fun_prop
  have hots : ComputableInPolyTime (fun q : Q => q.2.ots) encQ encBits := by
    unfold encQ; fun_prop
  have henc : ComputableInPolyTime (encPair encBits encBits)
      (encPair encBits encBits) encBits := .of_eq fun _ => rfl
  have hreply : ComputableInPolyTime
      (fun q : Q => (encPair encBits encBits (q.2.hashKey, q.2.ots)).take q.1.1) encQ encBits :=
    ComputableInPolyTime.bitsTakeWithInput ((hhash.prod hots).trans henc) hlimit
  exact (computableInPolyTime_finiteConfig_cases machine hcfg hcoin hcfg
    (fun action symbol move =>
      (ComputableInPolyTime.finiteConfig_step action symbol move).comp hcfg)
    (fun next =>
      ComputableInPolyTime.finiteConfig_receive hcfg hreply () next)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_replayCfg_raw {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Unit) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List TraceStep => replayCfg machine p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits (encList encTraceStep)))
      encFiniteConfig := by
  let P := ℕ × List Bool × List TraceStep
  let encP : P ↪ List Bool := encPair encUnary (encPair encBits (encList encTraceStep))
  have hlimit : ComputableInPolyTime (fun p : P => p.1) encP encUnary :=
    ComputableInPolyTime.fst _ _
  have hword : ComputableInPolyTime (fun p : P => p.2.1) encP encBits :=
    (ComputableInPolyTime.snd _ _).fst'
  have htrace : ComputableInPolyTime (fun p : P => p.2.2) encP (encList encTraceStep) :=
    (ComputableInPolyTime.snd _ _).snd'
  have hinit :=
    ComputableInPolyTime.finiteConfig_init (k := k) (Oracle := Unit) hword machine.initial
  obtain ⟨cCfg, hcCfg⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let inv (p : P) (consumed : List TraceStep)
      (cfg : FiniteConfig k Bool Control Unit) : Prop :=
    FiniteConfig.SpaceBound p.2.1.length consumed.length p.1 cfg
  let size (p : P) : ℕ :=
    cCfg * (p.2.1.length + (encList encTraceStep p.2.2).length + p.1 + 1)
  have hsize : PolyBounded (fun p : P => (encP p).length) size := by
    apply PolyBounded.of_forall_le (cCfg + 1) 1
    rintro ⟨lim, w, tr⟩
    dsimp only [P, encP, size]
    rw [length_encPair, length_encPair]
    simp only [encUnary_apply, List.length_replicate, encBits_apply, pow_one]
    calc cCfg * (w.length + (encList encTraceStep tr).length + lim + 1)
        ≤ (cCfg + 1) * (w.length + (encList encTraceStep tr).length + lim + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ ≤ (cCfg + 1) * (2 * lim + 1 + (2 * w.length + 1 + (encList encTraceStep tr).length) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
  exact (ComputableInPolyTime.foldlWith_spec
    (encA := encTraceStep) (encL := encList encTraceStep) (encB := encFiniteConfig)
    (par := fun p : P => p.1) (list := fun p : P => p.2.2)
    (init := fun p : P => FiniteConfig.init machine.initial p.2.1)
    (step := replayStep machine)
    hlimit htrace hinit (computableInPolyTime_replayStep machine)
    inv
    (fun p => FiniteConfig.spaceBound_init machine.initial p.2.1 p.1)
    (fun p consumed cfg item _ hinv => by
      dsimp only [inv, replayStep] at hinv ⊢
      simp only [List.length_append, List.length_singleton]
      cases cfg.tapes.state with
      | none => exact hinv.mono le_rfl (Nat.le_succ _) le_rfl
      | some state =>
        dsimp only
        cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols item.coin with
        | step action symbol move => exact hinv.step action symbol move
        | query ch next =>
          cases ch
          exact hinv.receive () next _ (List.length_take_le _ _))
    hsize
    (fun p consumed cfg hpre hinv => by
      rcases p with ⟨lim, w, tr⟩
      dsimp only [inv, size] at hinv ⊢
      have hlenPre : consumed.length ≤ (encList encTraceStep tr).length :=
        hpre.length_le.trans (length_le_length_encList encTraceStep tr)
      exact (hcCfg w.length consumed.length lim cfg hinv).trans
        (Nat.mul_le_mul_left cCfg (by omega)))).1

/-- `replayCfg` is computable in plain polynomial time for every finite-control `MultiTapePTM`. -/
theorem computableInPolyTime_replayCfg_comp {k : ℕ} {Control α : Type} [Finite Control]
    {input : α ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {limit : α → ℕ} {word : α → List Bool} {trace : α → List TraceStep}
    (hlimit : ComputableInPolyTime limit input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (htrace : ComputableInPolyTime trace input (encList encTraceStep)) :
    ComputableInPolyTime (fun a => replayCfg machine (limit a) (word a) (trace a))
      input encFiniteConfig :=
  ((hlimit.prod (hword.prod htrace)).trans
    (computableInPolyTime_replayCfg_raw machine)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_queryOf_comp {k : ℕ} {Control α : Type} [Finite Control]
    {input : α ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {cfg : α → FiniteConfig k Bool Control Unit} {coin : α → Bool}
    (hcfg : ComputableInPolyTime cfg input encFiniteConfig)
    (hcoin : ComputableInPolyTime coin input encBool) :
    ComputableInPolyTime (fun a => queryOf machine (cfg a) (coin a))
      input (encOption encBits) :=
  (computableInPolyTime_finiteConfig_cases machine hcfg hcoin (.const none)
    (fun _ _ _ => .const none)
    (fun _ =>
      (ComputableInPolyTime.optionSome encBits).comp
        (computableInPolyTime_finiteConfig_reqWord hcfg))).of_enc_eq fun _ => rfl

/-- Advance `trace` by one step under coin `b` and key `hashKey`, appending
`⟨b, hashKey, []⟩` when step `trace.length` does not query and signing
`(hashKey, H.eval n hashKey msg)` to append `⟨b, hashKey, ots⟩` when it queries `msg`. -/
noncomputable def appendTraceStep {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (otsk : List Bool) (limit : ℕ) (word : List Bool)
    (trace : List TraceStep) (b : Bool) (hashKey : List Bool) :
    ProbComp (List TraceStep) :=
  match queryOf machine (replayCfg machine limit word trace) b with
  | none => pure (trace ++ [⟨b, hashKey, []⟩])
  | some msg => do
    let ots ← S.sign otsk (otsMsg H n hashKey (H.eval n hashKey msg))
    return trace ++ [⟨b, hashKey, ots⟩]

/-- Sample one local simulation step on `trace`, appending `⟨b, k, []⟩` when step `trace.length`
does not query and `⟨b, k, ots⟩` (with `ots ← S.sign otsk (otsMsg H n k (H.eval n k msg))`) when
it queries `msg`. -/
noncomputable def sampleStep {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (otsk : List Bool) (limit : ℕ) (word : List Bool)
    (trace : List TraceStep) : ProbComp (List TraceStep) := do
  let b ← ProbComp.uniform Bool
  let hashKey ← BitString.sampleList (H.keyLen n)
  appendTraceStep S H machine n otsk limit word trace b hashKey

private theorem isPPTOn_appendTraceStep {k : ℕ} {Control α : Type} [Finite Control]
    {input : α ↪ List Bool}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    {n : α → ℕ} {otsk : α → List Bool} {limit : α → ℕ} {word : α → List Bool}
    {trace : α → List TraceStep} {b : α → Bool} {hashKey : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hotsk : ComputableInPolyTime otsk input encBits)
    (hlimit : ComputableInPolyTime limit input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (htrace : ComputableInPolyTime trace input (encList encTraceStep))
    (hb : ComputableInPolyTime b input encBool)
    (hhashKey : ComputableInPolyTime hashKey input encBits) :
    IsPPTOn input (encList encTraceStep)
      (fun a => appendTraceStep S H machine (n a) (otsk a) (limit a) (word a)
        (trace a) (b a) (hashKey a)) := by
  have hcfg := computableInPolyTime_replayCfg_comp machine hlimit hword htrace
  have hqOpt := computableInPolyTime_queryOf_comp machine hcfg hb
  have hnone : IsPPTOn input (encList encTraceStep)
      (fun a => pure (trace a ++ [⟨b a, hashKey a, []⟩])) := by
    have hitem : ComputableInPolyTime (fun a => (⟨b a, hashKey a, []⟩ : TraceStep))
        input encTraceStep := by
      fun_prop
    exact (htrace.listAppend' (hitem.cons' (.const []))).isPPTOn
  have hmsg := hqOpt.optionGetDWithInput (.const [])
  have hM := computableInPolyTime_otsMsg_eval_comp H hn hhashKey hmsg
  have hsign := S.isPPTOn_sign_comp (hotsk.of_enc_eq fun _ => rfl)
    (hM.of_enc_eq fun _ => rfl)
  have hpostSome : ComputableInPolyTime
      (fun u : α × List Bool => trace u.1 ++ [⟨b u.1, hashKey u.1, u.2⟩])
      (encPair input encBits) (encList encTraceStep) := by
    have huA := ComputableInPolyTime.fst input encBits
    have huOts := ComputableInPolyTime.snd input encBits
    have hitem : ComputableInPolyTime
        (fun u : α × List Bool => (⟨b u.1, hashKey u.1, u.2⟩ : TraceStep))
        (encPair input encBits) encTraceStep := by
      fun_prop
    exact (huA.trans htrace).listAppend' (hitem.cons' (.const []))
  have hsome := hsign.map_pair hpostSome
  have hcond : ComputableInPolyTime
      (fun a => decide ((queryOf machine
        (replayCfg machine (limit a) (word a) (trace a)) (b a)).isSome = true))
      input encBool :=
    hqOpt.optionIsSome.of_enc_eq fun _ => rfl
  refine (IsPPTOn.ite' hcond hsome hnone).congr fun a => ?_
  dsimp only [appendTraceStep]
  cases queryOf machine (replayCfg machine (limit a) (word a) (trace a)) (b a) with
  | none => rfl
  | some msg => simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]

private theorem exists_ots_of_mem_support_appendTraceStep {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (otsk : List Bool) (limit : ℕ) (word : List Bool)
    (trace : List TraceStep) (b : Bool) (hashKey : List Bool) {next : List TraceStep}
    (hnext : next ∈ (ProbComp.eval
      (appendTraceStep S H machine n otsk limit word trace b hashKey)).support) :
    ∃ ots, next = trace ++ [⟨b, hashKey, ots⟩] ∧
      (ots = [] ∨ ∃ msg, ots ∈ (ProbComp.eval
        (S.sign otsk (otsMsg H n hashKey (H.eval n hashKey msg)))).support) := by
  unfold appendTraceStep at hnext
  cases hq : queryOf machine (replayCfg machine limit word trace) b with
  | none =>
    rw [hq] at hnext
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
    exact ⟨[], hnext, Or.inl rfl⟩
  | some msg =>
    rw [hq] at hnext
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hnext
    obtain ⟨ots, hots, rfl⟩ := hnext
    exact ⟨ots, rfl, Or.inr ⟨msg, hots⟩⟩

private theorem isPPTOn_iterateWith_of_bounded_growth' {α State : Type}
    {input : α ↪ List Bool} {stateEncoding : State ↪ List Bool}
    {initial : α → State} {count : α → ℕ} {step : α → State → ProbComp State}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    {growth : α → ℕ} (hpoly : PolyBounded (fun a => (input a).length) growth)
    (hgrowth : ∀ a state next, next ∈ (ProbComp.eval (step a state)).support →
      (stateEncoding next).length ≤ (stateEncoding state).length + growth a) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) (step a) (initial a)) := by
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth' hcount hinitial
    (hstep.isOraclePPTOn (Operation := Empty)) hpoly fun a state next hnext =>
      hgrowth a state next ((ProbOracleComp.support_sample _).subset hnext)
  apply IsOraclePPTOn.isPPTOn
  simpa only [ProbOracleComp.sample, OracleComp.interpret_iterate] using hloop

private theorem isPPTOn_iterate_sampleStep {k : ℕ} {Control α : Type} [Finite Control]
    {input : α ↪ List Bool}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    {count : α → ℕ} {n : α → ℕ} {otsk : α → List Bool}
    {limit : α → ℕ} {word : α → List Bool} {initTrace : α → List TraceStep}
    (hcount : ComputableInPolyTime count input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hotsk : ComputableInPolyTime otsk input encBits)
    (hlimit : ComputableInPolyTime limit input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (hinit : ComputableInPolyTime initTrace input (encList encTraceStep)) :
    IsPPTOn input (encList encTraceStep)
      (fun a => OracleComp.iterate (count a)
        (sampleStep S H machine (n a) (otsk a) (limit a) (word a)) (initTrace a)) := by
  let SIn := α × List TraceStep
  let encSIn : SIn ↪ List Bool := encPair input (encList encTraceStep)
  have hsA : ComputableInPolyTime (fun p : SIn => p.1) encSIn input :=
    ComputableInPolyTime.fst _ _
  have hsTr : ComputableInPolyTime (fun p : SIn => p.2) encSIn (encList encTraceStep) :=
    ComputableInPolyTime.snd _ _
  have hb : IsPPTOn encSIn encBool (fun _ : SIn => ProbComp.uniform Bool) :=
    isPPTOn_uniform_bool encSIn
  have hk : IsPPTOn (encPair encSIn encBool) encBits
      (fun q : SIn × Bool => BitString.sampleList (H.keyLen (n q.1.1))) :=
    ((((ComputableInPolyTime.fst encSIn encBool).trans hsA).trans hn).trans
      H.keyLen_polyTime).sampleList
  let Mid := (SIn × Bool) × List Bool
  let encMid : Mid ↪ List Bool := encPair (encPair encSIn encBool) encBits
  have hmA : ComputableInPolyTime (fun r : Mid => r.1.1.1) encMid input :=
    ((ComputableInPolyTime.fst _ _).fst').trans hsA
  have hmTr : ComputableInPolyTime (fun r : Mid => r.1.1.2) encMid (encList encTraceStep) :=
    ((ComputableInPolyTime.fst _ _).fst').trans hsTr
  have hmB : ComputableInPolyTime (fun r : Mid => r.1.2) encMid encBool :=
    (ComputableInPolyTime.fst _ _).snd'
  have hmK : ComputableInPolyTime (fun r : Mid => r.2) encMid encBits :=
    ComputableInPolyTime.snd _ _
  have hmatch := isPPTOn_appendTraceStep S H machine
    (hmA.trans hn) (hmA.trans hotsk) (hmA.trans hlimit) (hmA.trans hword) hmTr hmB hmK
  have hstep : IsPPTOn encSIn (encList encTraceStep)
      (fun p : SIn =>
        sampleStep S H machine (n p.1) (otsk p.1) (limit p.1) (word p.1) p.2) :=
    (hb.bind_pair (hk.bind_pair hmatch)).congr fun _ => rfl
  obtain ⟨csg, dsg, hsgLen⟩ := S.sign_ppt.length_le
  let sigGrowth (a : α) : ℕ :=
    csg * (2 * (otsk a).length + otsParam H (n a) + 2) ^ dsg
  let growth (a : α) : ℕ :=
    4 * H.keyLen (n a) + 2 * sigGrowth a + 10
  have hpolySig : PolyBounded (fun a => (input a).length) sigGrowth := by
    have h1 := hotsk.polyBounded_length
    have h2 := ((computableInPolyTime_otsParam H).comp hn).polyBounded
    have hinner := (((PolyBounded.const 2).mul h1).add h2).add (.const 2)
    exact (PolyBounded.const csg).mul (hinner.pow dsg)
  have hpolyGrowth : PolyBounded (fun a => (input a).length) growth :=
    (((PolyBounded.const 4).mul (H.keyLen_polyTime.comp hn).polyBounded).add
      ((PolyBounded.const 2).mul hpolySig)).add (.const 10)
  refine isPPTOn_iterateWith_of_bounded_growth' hcount hinit hstep hpolyGrowth ?_
  intro a tr next hnext
  simp only [sampleStep, ProbComp.eval_bind, ProbComp.eval_uniform, BitString.eval_sampleList,
    PMF.mem_support_bind_iff] at hnext
  obtain ⟨b, _, k, hk, hrest⟩ := hnext
  have hkLen : k.length = H.keyLen (n a) := BitString.length_of_mem_support_uniformList hk
  obtain ⟨ots, rfl, hotsCases⟩ := exists_ots_of_mem_support_appendTraceStep S H machine
    (n a) (otsk a) (limit a) (word a) tr b k hrest
  have hotsLen : ots.length ≤ sigGrowth a := by
    rcases hotsCases with rfl | ⟨msg, hots⟩
    · exact Nat.zero_le _
    · have hs := hsgLen (otsk a, otsMsg H (n a) k (H.eval (n a) k msg)) ots hots
      simp only [length_encPair, encBits_apply, length_otsMsg] at hs
      have hle : 2 * (otsk a).length + 1 + otsParam H (n a) + 1 ≤
          2 * (otsk a).length + otsParam H (n a) + 2 := by omega
      exact hs.trans (Nat.mul_le_mul_left csg (Nat.pow_le_pow_left hle dsg))
  rw [encList_append]
  simp only [List.length_append, encList_cons, encList_nil, List.append_nil, length_frame,
    encTraceStep_apply, length_encPair, encBool_apply, encBits_apply, List.length_singleton,
    hkLen, growth]
  omega

/-- Uniform polynomial upper bound on the machine clock `c * ((wordOf n otvk).length + 1) ^ d`
across all `otvk` of length at most `ckg * (otsParam H n + 1) ^ dkg`. -/
@[expose]
def fuelUpper (H : KeyedHashFamily) (ckg dkg c d n : ℕ) : ℕ :=
  c * (4 * n + ckg * (otsParam H n + 1) ^ dkg + 3) ^ d

theorem computableInPolyTime_fuelUpper (H : KeyedHashFamily) (ckg dkg c d : ℕ) :
    ComputableInPolyTime (fuelUpper H ckg dkg c d) encUnary encUnary := by
  have hM := computableInPolyTime_otsParam H
  unfold fuelUpper
  fun_prop

/-- Saved state passed from `tcrMultiAdversary.choose` to `tcrMultiAdversary.find`. -/
@[ext]
structure TcrSavedState where
  /-- Whether `choose` sampled a step slot strictly before the machine fuel limit. -/
  active : Bool
  /-- Verification and signing key pair `(pk, sk)` sampled once for this execution. -/
  keys : List Bool × List Bool
  /-- Fair coin bit pre-committed for the target query step. -/
  coinAtSlot : Bool
  /-- Remaining simulation steps after the implanted challenge hash key. -/
  remSteps : ℕ
  /-- Prefix trace simulated locally before the implanted query step. -/
  preTrace : List TraceStep
  deriving DecidableEq, Repr, Inhabited

/-- Standard encoding of `TcrSavedState`. -/
enc_structure encTcrSavedState : TcrSavedState where
  active : encBool,
  keys : (encPair encBits encBits),
  coinAtSlot : encBool,
  remSteps : encUnary,
  preTrace : (encList encTraceStep)

attribute [fun_prop] encTcrSavedState_active_polyTime encTcrSavedState_keys_polyTime
  encTcrSavedState_coinAtSlot_polyTime encTcrSavedState_remSteps_polyTime
  encTcrSavedState_preTrace_polyTime encTcrSavedState_mk_polyTime

/-- Total decoder for `TcrSavedState`. -/
@[expose]
def tcrStateDecoder : Decoder encTcrSavedState :=
  (Decoder.bool.pair
    ((Decoder.bits.pair Decoder.bits).pair
      (Decoder.bool.pair (Decoder.unary.pair (Decoder.list traceStepDecoder))))).map
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩)
    (fun s => (s.active, s.keys, s.coinAtSlot, s.remSteps, s.preTrace))
    (fun _ => rfl)
    (fun _ => rfl)

/-- Many-query two-stage target-collision adversary against `H` ([BonehShoup2023], proof of
Theorem 13.2, p. 534): `choose n` samples `keys ← S.keyGen (otsParam H n)` and a uniform dyadic
step index `slot ← sampleDyadicIndex (fuelUpper H ckg dkg c d n)`; when `slot < B`, it locally
simulates `slot` machine steps via `sampleStep`, draws the next step coin `b`, commits the queried
message `(queryOf machine cfg b).getD []` before `hashKey` is sampled, and saves the state; `find`
implants the external `hashKey` at step `slot`, finishes the remaining `B - 1 - slot` steps via
`sampleStep`, and outputs the forged message `m*`. -/
noncomputable def tcrMultiAdversary {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (ckg dkg c d : ℕ) :
    TargetCollisionFinder where
  choose n := do
    let keys ← S.keyGen (otsParam H n)
    let slot ← sampleDyadicIndex (fuelUpper H ckg dkg c d n)
    let word := simWordOf n keys.1
    let fuel := simFuelOf c d n keys.1
    if slot < fuel then do
      let preTrace ← OracleComp.iterate slot (sampleStep S H machine n keys.2 fuel word) []
      let b ← ProbComp.uniform Bool
      let cfg := replayCfg machine fuel word preTrace
      pure ((queryOf machine cfg b).getD [],
        encTcrSavedState ⟨true, keys, b, fuel - 1 - slot, preTrace⟩)
    else
      pure ([], encTcrSavedState ⟨false, keys, false, 0, []⟩)
  find n stateWord hashKey := do
    let saved := tcrStateDecoder.decode stateWord
    if saved.active then do
      let keys := saved.keys
      let b := saved.coinAtSlot
      let remSteps := saved.remSteps
      let preTrace := saved.preTrace
      let word := simWordOf n keys.1
      let fuel := simFuelOf c d n keys.1
      let midTrace ← appendTraceStep S H machine n keys.2 fuel word preTrace b hashKey
      let fullTrace ← OracleComp.iterate remSteps
        (sampleStep S H machine n keys.2 fuel word) midTrace
      let finalCfg := replayCfg machine fuel word fullTrace
      pure (msgSigDecoder.decode finalCfg.tapes.output).1
    else
      pure []

private theorem isPPTOn_tcrMultiAdversary_choose {k : ℕ} {Control : Type} [Finite Control]
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (ckg dkg c d : ℕ) :
    IsPPTOn encUnary (encPair encBits encBits)
      (tcrMultiAdversary S H machine ckg dkg c d).choose := by
  have hkg : IsPPTOn encUnary (encPair encBits encBits)
      (fun n => S.keyGen (otsParam H n)) :=
    S.isPPTOn_keyGen_comp (computableInPolyTime_otsParam H)
  let KIn := ℕ × (List Bool × List Bool)
  let encKIn : KIn ↪ List Bool := encPair encUnary (encPair encBits encBits)
  have hkN : ComputableInPolyTime (fun p : KIn => p.1) encKIn encUnary :=
    ComputableInPolyTime.fst _ _
  have hslot : IsPPTOn encKIn encUnary
      (fun p : KIn => sampleDyadicIndex (fuelUpper H ckg dkg c d p.1)) :=
    isPPTOn_sampleDyadicIndex ((computableInPolyTime_fuelUpper H ckg dkg c d).comp hkN)
  let SIn := KIn × ℕ
  let encSIn : SIn ↪ List Bool := encPair encKIn encUnary
  have hsN : ComputableInPolyTime (fun q : SIn => q.1.1) encSIn encUnary :=
    (ComputableInPolyTime.fst _ _).fst'
  have hsKeys : ComputableInPolyTime (fun q : SIn => q.1.2) encSIn (encPair encBits encBits) :=
    (ComputableInPolyTime.fst _ _).snd'
  have hsSlot : ComputableInPolyTime (fun q : SIn => q.2) encSIn encUnary :=
    ComputableInPolyTime.snd _ _
  have hsWord := computableInPolyTime_wordOf hsN hsKeys.fst'
  have hsFuel := computableInPolyTime_fuelOf c d hsN hsKeys.fst'
  have hsCond : ComputableInPolyTime (fun q : SIn => decide (q.2 < simFuelOf c d q.1.1 q.1.2.1))
      encSIn encBool :=
    ComputableInPolyTime.unary_lt.comp (hsSlot.prod hsFuel)
  have hpreLoop := isPPTOn_iterate_sampleStep S H machine hsSlot hsN hsKeys.snd'
    hsFuel hsWord (.const [])
  let LIn := SIn × List TraceStep
  let encLIn : LIn ↪ List Bool := encPair encSIn (encList encTraceStep)
  have hlCoin : IsPPTOn encLIn encBool (fun _ : LIn => ProbComp.uniform Bool) :=
    isPPTOn_uniform_bool encLIn
  have hencState : ComputableInPolyTime encTcrSavedState encTcrSavedState encBits :=
    .of_eq fun _ => rfl
  have hpostActive : ComputableInPolyTime
      (fun u : LIn × Bool =>
        let n := u.1.1.1.1
        let keys := u.1.1.1.2
        let slot := u.1.1.2
        let preTrace := u.1.2
        let b := u.2
        let word := simWordOf n keys.1
        let fuel := simFuelOf c d n keys.1
        let cfg := replayCfg machine fuel word preTrace
        ((queryOf machine cfg b).getD [],
          encTcrSavedState ⟨true, keys, b, fuel - 1 - slot, preTrace⟩))
      (encPair encLIn encBool) (encPair encBits encBits) := by
    let U := LIn × Bool
    let encU : U ↪ List Bool := encPair encLIn encBool
    have huSIn : ComputableInPolyTime (fun u : U => u.1.1) encU encSIn :=
      (ComputableInPolyTime.fst _ _).fst'
    have huTr : ComputableInPolyTime (fun u : U => u.1.2) encU (encList encTraceStep) :=
      (ComputableInPolyTime.fst _ _).snd'
    have huB : ComputableInPolyTime (fun u : U => u.2) encU encBool :=
      ComputableInPolyTime.snd _ _
    have huKeys := huSIn.trans hsKeys
    have huSlot := huSIn.trans hsSlot
    have huWord := huSIn.trans hsWord
    have huFuel := huSIn.trans hsFuel
    have huCfg := computableInPolyTime_replayCfg_comp machine huFuel huWord huTr
    have huQOpt := computableInPolyTime_queryOf_comp machine huCfg huB
    have huTarget := huQOpt.optionGetDWithInput (.const [])
    have huRem : ComputableInPolyTime
        (fun u : U => simFuelOf c d u.1.1.1.1 u.1.1.1.2.1 - 1 - u.1.1.2) encU encUnary :=
      ComputableInPolyTime.unary_sub.comp
        ((ComputableInPolyTime.unary_sub.comp (huFuel.prod (.const 1))).prod huSlot)
    have huSaved : ComputableInPolyTime
        (fun u : U =>
          (⟨true, u.1.1.1.2, u.2, simFuelOf c d u.1.1.1.1 u.1.1.1.2.1 - 1 - u.1.1.2,
            u.1.2⟩ : TcrSavedState))
        encU encTcrSavedState :=
      encTcrSavedState_mk_polyTime (.const true) huKeys huB huRem huTr
    exact (huTarget.prod (huSaved.trans hencState)).of_enc_eq fun _ => rfl
  have hyes := hpreLoop.bind_pair (hlCoin.map_pair hpostActive)
  have hno : IsPPTOn encSIn (encPair encBits encBits)
      (fun q : SIn => pure ([], encTcrSavedState ⟨false, q.1.2, false, 0, []⟩)) := by
    have hsavedFalse : ComputableInPolyTime
        (fun q : SIn => (⟨false, q.1.2, false, 0, []⟩ : TcrSavedState))
        encSIn encTcrSavedState :=
      encTcrSavedState_mk_polyTime (.const false) hsKeys (.const false) (.const 0) (.const [])
    exact ((ComputableInPolyTime.const []).prod (hsavedFalse.trans hencState)).isPPTOn
  have hite := IsPPTOn.ite' hsCond hyes hno
  exact (hkg.bind_pair (hslot.bind_pair hite)).congr fun _ => rfl

private theorem isPPTOn_tcrMultiAdversary_find {k : ℕ} {Control : Type} [Finite Control]
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (ckg dkg c d : ℕ) :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ⟨n, stateWord, hashKey⟩ =>
        (tcrMultiAdversary S H machine ckg dkg c d).find n stateWord hashKey) := by
  let FIn := ℕ × List Bool × List Bool
  let encFIn : FIn ↪ List Bool := encPair encUnary (encPair encBits encBits)
  have hn : ComputableInPolyTime (fun p : FIn => p.1) encFIn encUnary :=
    ComputableInPolyTime.fst _ _
  have hstateWord : ComputableInPolyTime (fun p : FIn => p.2.1) encFIn encBits :=
    (ComputableInPolyTime.snd _ _).fst'
  have hhashKey : ComputableInPolyTime (fun p : FIn => p.2.2) encFIn encBits :=
    (ComputableInPolyTime.snd _ _).snd'
  have hsaved : ComputableInPolyTime
      (fun p : FIn => tcrStateDecoder.decode p.2.1) encFIn encTcrSavedState :=
    hstateWord.trans tcrStateDecoder.computableInPolyTime
  have hactiveRaw : ComputableInPolyTime
      (fun p : FIn => (tcrStateDecoder.decode p.2.1).active) encFIn encBool := by
    fun_prop
  have hactive : ComputableInPolyTime
      (fun p : FIn => decide ((tcrStateDecoder.decode p.2.1).active = true)) encFIn encBool :=
    hactiveRaw.of_enc_eq fun _ => rfl
  have hkeys : ComputableInPolyTime
      (fun p : FIn => (tcrStateDecoder.decode p.2.1).keys) encFIn (encPair encBits encBits) := by
    fun_prop
  have hb : ComputableInPolyTime
      (fun p : FIn => (tcrStateDecoder.decode p.2.1).coinAtSlot) encFIn encBool := by
    fun_prop
  have hrem : ComputableInPolyTime
      (fun p : FIn => (tcrStateDecoder.decode p.2.1).remSteps) encFIn encUnary := by
    fun_prop
  have hpre : ComputableInPolyTime
      (fun p : FIn => (tcrStateDecoder.decode p.2.1).preTrace) encFIn (encList encTraceStep) := by
    fun_prop
  have hword := computableInPolyTime_wordOf hn hkeys.fst'
  have hfuel := computableInPolyTime_fuelOf c d hn hkeys.fst'
  have hmid := isPPTOn_appendTraceStep S H machine hn hkeys.snd' hfuel hword hpre hb hhashKey
  let MIn := FIn × List TraceStep
  let encMIn : MIn ↪ List Bool := encPair encFIn (encList encTraceStep)
  have hmFIn := ComputableInPolyTime.fst encFIn (encList encTraceStep)
  have hmMid := ComputableInPolyTime.snd encFIn (encList encTraceStep)
  have hpostLoop := isPPTOn_iterate_sampleStep S H machine
    (hmFIn.trans hrem) (hmFIn.trans hn) (hmFIn.trans hkeys.snd')
    (hmFIn.trans hfuel) (hmFIn.trans hword) hmMid
  have hpostOut : ComputableInPolyTime
      (fun r : MIn × List TraceStep =>
        let s := tcrStateDecoder.decode r.1.1.2.1
        let word := simWordOf r.1.1.1 s.keys.1
        let fuel := simFuelOf c d r.1.1.1 s.keys.1
        let finalCfg := replayCfg machine fuel word r.2
        (msgSigDecoder.decode finalCfg.tapes.output).1)
      (encPair encMIn (encList encTraceStep)) encBits := by
    have hrMIn := ComputableInPolyTime.fst encMIn (encList encTraceStep)
    have hrFull := ComputableInPolyTime.snd encMIn (encList encTraceStep)
    have hrCfg := computableInPolyTime_replayCfg_comp machine
      ((hrMIn.trans hmFIn).trans hfuel) ((hrMIn.trans hmFIn).trans hword) hrFull
    have hrTapes := ComputableInPolyTime.finiteConfig_tapes.comp hrCfg
    have hrOut := ComputableInPolyTime.finiteCfg_output.comp hrTapes
    exact ((hrOut.trans msgSigDecoder.computableInPolyTime).fst').of_enc_eq fun _ => rfl
  have hyes := hmid.bind_pair (hpostLoop.map_pair hpostOut)
  have hno : IsPPTOn encFIn encBits (fun _ : FIn => pure []) :=
    (ComputableInPolyTime.const []).isPPTOn
  exact (IsPPTOn.ite' hactive hyes hno).congr fun _ => rfl

/-- Both stages of `tcrMultiAdversary` are uniformly strict PPT. -/
theorem isPPT_tcrMultiAdversary {k : ℕ} {Control : Type} [Finite Control]
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (ckg dkg c d : ℕ) :
    (tcrMultiAdversary S H machine ckg dkg c d).IsPPT where
  choose := isPPTOn_tcrMultiAdversary_choose S H machine ckg dkg c d
  find := isPPTOn_tcrMultiAdversary_find S H machine ckg dkg c d

/-! ### Exact trace coupling and Boneh–Shoup Theorem 13.2 security proof -/

/-- Enriched signing oracle recording every `(queriedMsg, freshHashKey)` pair in reverse
chronological order. -/
private noncomputable def pairSigningOracle (S : SignatureScheme) (H : KeyedHashFamily)
    (n : ℕ) (otsk : List Bool) (request : Unit × List Bool)
    (pairs : List (List Bool × List Bool)) :
    PMF (List Bool × List (List Bool × List Bool)) := do
  let k ← BitString.uniformList (H.keyLen n)
  (ProbComp.eval (S.sign otsk (otsMsg H n k (H.eval n k request.2)))).map fun ots =>
    (encPair encBits encBits (k, ots), (request.2, k) :: pairs)

/-- Deterministic step accumulating both `FiniteConfig` and `(msg, hashKey)` query pairs. -/
private def replayPairStep {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (limit : ℕ)
    (acc : FiniteConfig k Bool Control Unit × List (List Bool × List Bool))
    (step : TraceStep) :
    FiniteConfig k Bool Control Unit × List (List Bool × List Bool) :=
  match acc.1.tapes.state with
  | none => acc
  | some state =>
    match machine.tr state acc.1.tapes.inputSymbol acc.1.tapes.workTapeSymbols
        acc.1.answerSymbols step.coin with
    | .step action symbol move => (acc.1.step action symbol move, acc.2)
    | .query () next =>
      let msg := (acc.1.channels ()).1
      (acc.1.receive () next ((encPair encBits encBits (step.hashKey, step.ots)).take limit),
        (msg, step.hashKey) :: acc.2)

private theorem replayPairStep_fst {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (limit : ℕ)
    (cfg : FiniteConfig k Bool Control Unit)
    (pairs : List (List Bool × List Bool)) (trace : List TraceStep) :
    (trace.foldl (replayPairStep machine limit) (cfg, pairs)).1 =
      trace.foldl (replayStep machine limit) cfg := by
  induction trace generalizing cfg pairs with
  | nil => rfl
  | cons step rest ih =>
    simp only [List.foldl_cons]
    have hfst : (replayPairStep machine limit (cfg, pairs) step).1 =
        replayStep machine limit cfg step := by
      unfold replayPairStep replayStep
      cases cfg.tapes.state with
      | none => rfl
      | some state =>
        dsimp only
        cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols step.coin with
        | step _ _ _ => rfl
        | query ch _ => cases ch; rfl
    rcases h : replayPairStep machine limit (cfg, pairs) step with ⟨cfg', pairs'⟩
    rw [h] at hfst
    dsimp only at hfst
    subst hfst
    exact ih _ pairs'

private theorem iterate_finiteStep_pairSigningOracle {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (otsk : List Bool) (limit : ℕ) (word : List Bool) (steps : ℕ) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (pairSigningOracle S H n otsk))
      (OracleComp.iterate steps
        (machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op req => List.take limit <$> ProbOracleComp.query (op, req)))
        (FiniteConfig.init machine.initial word))).run [] =
    (ProbComp.eval (OracleComp.iterate steps
      (sampleStep S H machine n otsk limit word) [])).map fun trace =>
        trace.foldl (replayPairStep machine limit)
          (FiniteConfig.init machine.initial word, []) := by
  induction steps with
  | zero =>
    simp only [OracleComp.iterate_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map, List.foldl_nil]
  | succ steps ih =>
    rw [OracleComp.iterate_succ, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, ih,
      OracleComp.iterate_succ, ProbComp.eval_bind, PMF.map_bind, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun trace _ => ?_
    dsimp only [Function.comp_def]
    let acc := trace.foldl (replayPairStep machine limit)
      (FiniteConfig.init machine.initial word, [])
    have haccEq : trace.foldl (replayPairStep machine limit)
        (FiniteConfig.init machine.initial word, []) = acc := rfl
    have hcfg : acc.1 = replayCfg machine limit word trace :=
      replayPairStep_fst machine limit _ [] trace
    change (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (pairSigningOracle S H n otsk))
      (machine.finiteStep _ _ acc.1)).run acc.2 =
      (ProbComp.eval (sampleStep S H machine n otsk limit word trace)).map
        (fun trace' => trace'.foldl (replayPairStep machine limit)
          (FiniteConfig.init machine.initial word, []))
    simp only [sampleStep, appendTraceStep, ← hcfg]
    cases hs : acc.1.tapes.state with
    | none =>
      simp only [finiteStep, queryOf, hs, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, ProbComp.eval_bind, ProbComp.eval_pure,
        ProbComp.eval_uniform, BitString.eval_sampleList, PMF.map_bind, PMF.pure_map,
        List.foldl_append, List.foldl_cons, List.foldl_nil, haccEq]
      simp only [replayPairStep, hs, PMF.bind_const]
    | some state =>
      simp only [finiteStep, queryOf, hs, bind_map_left, OracleComp.interpret_bind,
        StateT.run_bind, ProbOracleComp.run_interpret_sample, ProbComp.eval_bind,
        ProbComp.eval_uniform, BitString.eval_sampleList, Probability.PMF.monad_bind_eq_bind,
        PMF.bind_map, PMF.map_bind, Function.comp_def]
      congr 1
      funext bit
      cases htr : machine.tr state acc.1.tapes.inputSymbol acc.1.tapes.workTapeSymbols
          acc.1.answerSymbols bit with
      | step action symbol move =>
        simp only [OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map,
          List.foldl_append, List.foldl_cons, List.foldl_nil, haccEq]
        simp only [replayPairStep, hs, htr, PMF.bind_const]
      | query ch next =>
        cases ch
        simp only [OracleComp.interpret_bind, OracleComp.interpret_pure, StateT.run_bind,
          StateT.run_pure, ProbOracleComp.interpret_query, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_bind, ProbComp.eval_pure,
          PMF.map_bind, PMF.pure_map, List.foldl_append, List.foldl_cons, List.foldl_nil, haccEq]
        simp only [StateT.run, pairSigningOracle, replayPairStep, hs, htr,
          PMF.monad_bind_eq_bind, _root_.PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]

private theorem iterate_add_prob {State : Type} (a b : ℕ) (step : State → ProbComp State)
    (initial : State) :
    OracleComp.iterate (a + b) step initial =
      OracleComp.iterate a step initial >>= OracleComp.iterate b step := by
  induction b with
  | zero => simp [OracleComp.iterate]
  | succ b ih =>
    rw [Nat.add_succ, OracleComp.iterate_succ, ih, bind_assoc]
    rfl

private theorem mem_support_iterate_sampleStep_props {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (otsk : List Bool) (limit : ℕ) (word : List Bool)
    (count : ℕ) (init : List TraceStep) {trace : List TraceStep}
    (h : trace ∈ (ProbComp.eval
      (OracleComp.iterate count (sampleStep S H machine n otsk limit word) init)).support) :
    init <+: trace ∧ trace.length = init.length + count ∧
      ((∀ item ∈ init, item.hashKey.length = H.keyLen n) →
        ∀ item ∈ trace, item.hashKey.length = H.keyLen n) := by
  refine ProbComp.iterate_invariant count
    (sampleStep S H machine n otsk limit word) init
    (fun i tr => init <+: tr ∧ tr.length = init.length + i ∧
      ((∀ item ∈ init, item.hashKey.length = H.keyLen n) →
        ∀ item ∈ tr, item.hashKey.length = H.keyLen n))
    ⟨List.prefix_refl init, Nat.add_zero _, fun h0 => h0⟩
    (fun i _ tr ⟨hpre, hlen, hkeys⟩ next hnext => ?_) trace h
  simp only [sampleStep, ProbComp.eval_bind, ProbComp.eval_uniform, BitString.eval_sampleList,
    PMF.mem_support_bind_iff] at hnext
  obtain ⟨b, _, hashKey, hk, hrest⟩ := hnext
  have hkLen : hashKey.length = H.keyLen n := BitString.length_of_mem_support_uniformList hk
  obtain ⟨ots, rfl, _⟩ := exists_ots_of_mem_support_appendTraceStep S H machine
    n otsk limit word tr b hashKey hrest
  refine ⟨hpre.trans (List.prefix_append tr _), ?_, fun h0 item hitem => ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen]
    omega
  · rcases List.mem_append.mp hitem with htr | hsing
    · exact hkeys h0 item htr
    · simp only [List.mem_singleton] at hsing
      rw [hsing]
      exact hkLen

private theorem exists_slot_of_mem_replayPairs {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (limit : ℕ) (word : List Bool)
    (trace : List TraceStep) {mJ kJ : List Bool}
    (hmem : (mJ, kJ) ∈
      (trace.foldl (replayPairStep machine limit)
        (FiniteConfig.init machine.initial word, [])).2) :
    ∃ j < trace.length,
      let stepJ := trace.getD j ⟨false, [], []⟩
      queryOf machine (replayCfg machine limit word (trace.take j)) stepJ.coin = some mJ ∧
        stepJ.hashKey = kJ := by
  induction trace using List.reverseRecOn with
  | nil => simp at hmem
  | append_singleton pre item ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hmem
    let acc := pre.foldl (replayPairStep machine limit)
      (FiniteConfig.init machine.initial word, [])
    have hcfg : acc.1 = replayCfg machine limit word pre :=
      replayPairStep_fst machine limit _ [] pre
    have hOld : (mJ, kJ) ∈ acc.2 →
        ∃ j < (pre ++ [item]).length,
          let stepJ := (pre ++ [item]).getD j ⟨false, [], []⟩
          queryOf machine (replayCfg machine limit word ((pre ++ [item]).take j))
            stepJ.coin = some mJ ∧ stepJ.hashKey = kJ := by
      intro hold
      obtain ⟨j, hj, hq, hk⟩ := ih hold
      refine ⟨j, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · have htake : (pre ++ [item]).take j = pre.take j :=
          List.take_append_of_le_length hj.le
        have hget : (pre ++ [item]).getD j ⟨false, [], []⟩ = pre.getD j ⟨false, [], []⟩ := by
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
            List.getElem_append_left hj]
        simpa only [htake, hget] using ⟨hq, hk⟩
    change (mJ, kJ) ∈ (replayPairStep machine limit acc item).2 at hmem
    unfold replayPairStep at hmem
    cases hs : acc.1.tapes.state with
    | none =>
      rw [hs] at hmem
      exact hOld hmem
    | some state =>
      rw [hs] at hmem
      dsimp only at hmem
      cases htr : machine.tr state acc.1.tapes.inputSymbol acc.1.tapes.workTapeSymbols
          acc.1.answerSymbols item.coin with
      | step _ _ _ =>
        rw [htr] at hmem
        exact hOld hmem
      | query ch _ =>
        cases ch
        rw [htr] at hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htail
        · rcases Prod.mk.inj hhead with ⟨rfl, rfl⟩
          refine ⟨pre.length, by simp, ?_⟩
          have htake : (pre ++ [item]).take pre.length = pre := by simp
          have hget : (pre ++ [item]).getD pre.length ⟨false, [], []⟩ = item := by
            rw [List.getD_eq_getElem _ _ (by simp)]
            simp
          simp only [htake, hget, ← hcfg, queryOf, hs, htr, and_self]
        · exact hOld htail

private theorem succProbability_map_le_add_sum {α ι : Type*} [Fintype ι] (μ : PMF α)
    (f g : α → Bool) (h : ι → α → Bool)
    (hfg : ∀ x ∈ μ.support, f x = true → g x = true ∨ ∃ i, h i x = true) :
    Game.succProbability (μ.map f) ≤
      Game.succProbability (μ.map g) + ∑ i, ((μ.map (h i)) true).toNNReal := by
  have hsum_ennreal : (μ.map f) true ≤ (μ.map g) true + ∑ i, (μ.map (h i)) true := by
    simp only [PMF.map_apply]
    rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable,
      ← Summable.tsum_add CompleteLattice.summable CompleteLattice.summable]
    refine tsum_le_tsum fun sample => ?_
    by_cases hs : sample ∈ μ.support
    · by_cases hw : f sample = true
      · rcases hfg sample hs hw with h1 | ⟨i₀, hi₀⟩
        · simp only [hw, h1, ↓reduceIte]
          exact le_self_add
        · simp only [hw, ↓reduceIte]
          refine le_trans ?_ le_add_self
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i₀))
          simp [hi₀]
      · simp [Bool.eq_false_iff.mpr hw]
    · simp [(PMF.apply_eq_zero_iff μ sample).mpr hs]
  have hsumNeTop : (μ.map g) true + ∑ i, (μ.map (h i)) true ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨PMF.apply_ne_top _ _, ENNReal.sum_ne_top.mpr fun _ _ => PMF.apply_ne_top _ _⟩
  have hmono := ENNReal.toNNReal_mono hsumNeTop hsum_ennreal
  rwa [ENNReal.toNNReal_add (PMF.apply_ne_top _ _)
    (ENNReal.sum_ne_top.mpr fun _ _ => PMF.apply_ne_top _ _),
    ENNReal.toNNReal_sum fun _ _ => PMF.apply_ne_top _ _] at hmono

private noncomputable def traceSamplePMF {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (c d n : ℕ) :
    PMF ((List Bool × List Bool) × List TraceStep) := do
  let keys ← ProbComp.eval (S.keyGen (otsParam H n))
  (ProbComp.eval (OracleComp.iterate (simFuelOf c d n keys.1)
    (sampleStep S H machine n keys.2 (simFuelOf c d n keys.1) (simWordOf n keys.1)) [])).map
    fun trace => (keys, trace)

private def winTcrAt {k : ℕ} {Control : Type}
    (H : KeyedHashFamily) (machine : MultiTapePTM k Bool Control Unit)
    (c d n slot : ℕ) (sample : (List Bool × List Bool) × List TraceStep) : Bool :=
  let keys := sample.1
  let trace := sample.2
  let B := simFuelOf c d n keys.1
  decide (slot < B) &&
    let stepJ := trace.getD slot ⟨false, [], []⟩
    let cfgJ := replayCfg machine B (simWordOf n keys.1) (trace.take slot)
    match queryOf machine cfgJ stepJ.coin with
    | none => false
    | some mJ =>
      let finalCfg := replayCfg machine B (simWordOf n keys.1) trace
      let mOut := (msgSigDecoder.decode finalCfg.tapes.output).1
      isCollision (H.eval n) (fun _ _ => true) n stepJ.hashKey mJ mOut

private noncomputable def tcrSlotTrial {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (c d n slot : ℕ) : Game := do
  let keys ← ProbComp.eval (S.keyGen (otsParam H n))
  let B := simFuelOf c d n keys.1
  let word := simWordOf n keys.1
  if slot < B then
    let preTrace ← ProbComp.eval (OracleComp.iterate slot
      (sampleStep S H machine n keys.2 B word) [])
    let b ← PMF.uniformOfFintype Bool
    let cfg := replayCfg machine B word preTrace
    let mTarget := (queryOf machine cfg b).getD []
    let kStar ← BitString.uniformList (H.keyLen n)
    let midTrace ← ProbComp.eval (appendTraceStep S H machine n keys.2 B word preTrace b kStar)
    (ProbComp.eval (OracleComp.iterate (B - 1 - slot)
      (sampleStep S H machine n keys.2 B word) midTrace)).map fun fullTrace =>
        let finalCfg := replayCfg machine B word fullTrace
        let mOut := (msgSigDecoder.decode finalCfg.tapes.output).1
        isCollision (H.eval n) (fun _ _ => true) n kStar mTarget mOut
  else
    (BitString.uniformList (H.keyLen n)).map fun kStar =>
      isCollision (H.eval n) (fun _ _ => true) n kStar [] []

private theorem eval_targetCollisionGame_tcrMultiAdversary {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (ckg dkg c d n : ℕ) :
    have : NeZero (dyadicSize (fuelUpper H ckg dkg c d n)) := ⟨(dyadicSize_pos _).ne'⟩
    ProbComp.eval
      (targetCollisionGame H.keyLen H.eval (fun _ _ => true)
        (tcrMultiAdversary S H machine ckg dkg c d) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (fuelUpper H ckg dkg c d n)))).bind fun i =>
        tcrSlotTrial S H machine c d n i.val := by
  intro _
  simp only [targetCollisionGame, tcrMultiAdversary, tcrSlotTrial, eval_sampleDyadicIndex,
    BitString.eval_sampleList, pmf_norm]
  peel_binds keys i
  by_cases hlt : i.val < simFuelOf c d n keys.1
  · dsimp only [simFuelOf, simWordOf, simPkOf] at hlt ⊢
    simp only [hlt, ↓reduceIte, ProbComp.eval_uniform, tcrStateDecoder.decode_enc,
      _root_.PMF.map, pmf_norm]
  · dsimp only [simFuelOf, simWordOf, simPkOf] at hlt ⊢
    simp only [hlt, ↓reduceIte, tcrStateDecoder.decode_enc, Bool.false_eq_true,
      _root_.PMF.map, pmf_norm]

private theorem succProbability_winTcrAt_le_trial {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (c d n slot : ℕ) :
    (((traceSamplePMF S H machine c d n).map (winTcrAt H machine c d n slot)) true).toNNReal ≤
      Game.succProbability (tcrSlotTrial S H machine c d n slot) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [traceSamplePMF, tcrSlotTrial, PMF.monad_bind_eq_bind, PMF.map_bind]
  refine PMF.bind_apply_mono_on_support _ true fun keys _ => ?_
  let B := simFuelOf c d n keys.1
  let word := simWordOf n keys.1
  let stepFn := sampleStep S H machine n keys.2 B word
  by_cases hlt : slot < B
  · simp only [B] at hlt
    simp only [hlt, ↓reduceIte, PMF.map_comp]
    have hsplit : B = slot + 1 + (B - 1 - slot) := by omega
    have hiter :
        ProbComp.eval (OracleComp.iterate B stepFn []) =
          (ProbComp.eval (OracleComp.iterate slot stepFn [])).bind fun preTrace =>
            (PMF.uniformOfFintype Bool).bind fun b =>
              (BitString.uniformList (H.keyLen n)).bind fun kStar =>
                (ProbComp.eval
                  (appendTraceStep S H machine n keys.2 B word preTrace b kStar)).bind
                  fun midTrace =>
                    ProbComp.eval (OracleComp.iterate (B - 1 - slot) stepFn midTrace) := by
      conv_lhs => rw [hsplit, iterate_add_prob, OracleComp.iterate_succ]
      simp only [ProbComp.eval_bind, PMF.bind_bind]
      congr 1; funext preTrace
      simp only [stepFn, sampleStep, ProbComp.eval_bind, ProbComp.eval_uniform,
        BitString.eval_sampleList, PMF.bind_bind]
    change ((ProbComp.eval (OracleComp.iterate B stepFn [])).map
        (fun trace => winTcrAt H machine c d n slot (keys, trace))) true ≤ _
    rw [hiter]
    simp only [PMF.map_bind]
    refine PMF.bind_apply_mono_on_support _ true fun preTrace hpreSupp => ?_
    have hpreLen : preTrace.length = slot := by
      simpa using (mem_support_iterate_sampleStep_props S H machine n keys.2 B word
        slot [] hpreSupp).2.1
    refine PMF.bind_apply_mono_on_support _ true fun b _ => ?_
    refine PMF.bind_apply_mono_on_support _ true fun kStar _ => ?_
    refine PMF.bind_apply_mono_on_support _ true fun midTrace hmidSupp => ?_
    refine PMF.map_true_mono _ fun fullTrace hfullSupp hwin => ?_
    obtain ⟨postTrace, rfl⟩ :=
      (mem_support_iterate_sampleStep_props S H machine n keys.2 B word
        (B - 1 - slot) midTrace hfullSupp).1
    obtain ⟨ots, rfl, _⟩ := exists_ots_of_mem_support_appendTraceStep S H machine
      n keys.2 B word preTrace b kStar hmidSupp
    have hassoc : (preTrace ++ [(⟨b, kStar, ots⟩ : TraceStep)]) ++ postTrace =
        preTrace ++ ((⟨b, kStar, ots⟩ : TraceStep) :: postTrace) := by simp
    have htake :
        ((preTrace ++ [(⟨b, kStar, ots⟩ : TraceStep)]) ++ postTrace).take slot = preTrace := by
      rw [hassoc, List.take_append_of_le_length (by rw [hpreLen]), ← hpreLen, List.take_length]
    have hget :
        ((preTrace ++ [(⟨b, kStar, ots⟩ : TraceStep)]) ++ postTrace).getD slot
            (⟨false, [], []⟩ : TraceStep) =
          (⟨b, kStar, ots⟩ : TraceStep) := by
      have hltFull :
          slot < (preTrace ++ ((⟨b, kStar, ots⟩ : TraceStep) :: postTrace)).length := by
        simp [hpreLen]
      rw [hassoc, List.getD_eq_getElem _ _ hltFull,
        List.getElem_append_right (by rw [hpreLen])]
      simp only [hpreLen, Nat.sub_self, List.getElem_cons_zero]
    dsimp only [winTcrAt, B, word] at hwin ⊢
    simp only [decide_eq_true hlt, Bool.true_and, htake, hget] at hwin
    cases hq : queryOf machine
        (replayCfg machine (simFuelOf c d n keys.1) (simWordOf n keys.1) preTrace) b with
    | none => simp [hq] at hwin
    | some mJ => simpa [hq] using hwin
  · simp [B, hlt, PMF.map_comp, PMF.map_apply, winTcrAt]

end MultiSimulator

/-! ### Concrete and asymptotic security theorems ([BonehShoup2023], Theorem 13.2) -/

/-- **Concrete security bound for `TCRSignature.wordScheme` with an explicit realizing machine**
([BonehShoup2023], Section 13.2.1, Theorem 13.2, p. 534): at every security parameter `n`, the
adaptive EUF-CMA forging probability against `wordScheme S H` on unrestricted `List Bool` messages
is at most the `SignatureScheme.eufCmaGame` forging probability of `manyTimeForger` against `S` at
`otsParam H n` plus `dyadicSize (fuelUpper H ckg dkg c d n)` times the target-collision probability
of `tcrMultiAdversary` against `H` at `n`. -/
theorem succProbability_wordScheme_eufCmaGame_le_of_machine {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (ckg dkg : ℕ)
    (hpkBound : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support →
      pk.length ≤ ckg * (otsParam H n + 1) ^ dkg)
    (sigBound : ℕ → ℕ)
    (hsigBound : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support →
      ∀ msg, msg.length = otsParam H n →
      ∀ ots ∈ (ProbComp.eval (S.sign sk msg)).support, ots.length ≤ sigBound n)
    (adversary : Forger)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ)
    (hmachine : ∀ (input : ℕ × List Bool) (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
          ((encPair encBits encBits) <$> adversary input.1 input.2)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
          (machine.runOracle
            (c * ((encPair encUnary encBits input).length + 1) ^ d)
            (encPair encUnary encBits input))).run s)
    (n : ℕ) :
    Game.succProbability (ProbComp.eval ((wordScheme S H).eufCmaGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (S.eufCmaGame (manyTimeForger H sigBound adversary) (otsParam H n))) +
      (dyadicSize (fuelUpper H ckg dkg c d n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (targetCollisionGame H.keyLen H.eval (fun _ _ => true)
              (tcrMultiAdversary S H machine ckg dkg c d) n)) := by
  let pkOf := simPkOf n
  let wordOf := simWordOf n
  let fuelOf := simFuelOf c d n
  let D : ℕ := dyadicSize (fuelUpper H ckg dkg c d n)
  have hDpos : 0 < D := dyadicSize_pos _
  have : NeZero D := ⟨hDpos.ne'⟩
  let μ := traceSamplePMF S H machine c d n
  have hrunPair : ∀ keys : List Bool × List Bool,
      ProbOracleComp.runWith (pairSigningOracle S H n keys.2) (adversary n (pkOf keys.1)) [] =
      (ProbComp.eval (OracleComp.iterate (fuelOf keys.1)
        (sampleStep S H machine n keys.2 (fuelOf keys.1) (wordOf keys.1)) [])).map fun trace =>
          let res := trace.foldl (replayPairStep machine (fuelOf keys.1))
            (FiniteConfig.init machine.initial (wordOf keys.1), [])
          (msgSigDecoder.decode res.1.tapes.output, res.2) := by
    intro keys
    rw [← ProbOracleComp.run_interpret_eq_runWith]
    have hdecode : adversary n (pkOf keys.1) =
        msgSigDecoder.decode <$> ((encPair encBits encBits) <$> adversary n (pkOf keys.1)) := by
      simp only [Functor.map_map, msgSigDecoder.decode_enc]
      exact (id_map _).symm
    rw [hdecode, OracleComp.interpret_map, StateT.run_map, _root_.PMF.monad_map_eq_map,
      hmachine (n, pkOf keys.1) _ _ []]
    erw [← machine.finiteRunFrom_take_runOracle (fuelOf keys.1) (wordOf keys.1)]
    simp only [finiteRunFrom, OracleComp.interpret_map, StateT.run_map,
      _root_.PMF.monad_map_eq_map, PMF.map_comp]
    rw [iterate_finiteStep_pairSigningOracle S H machine n keys.2 (fuelOf keys.1) (wordOf keys.1)
      (fuelOf keys.1), PMF.map_comp]
    rfl
  let winGame (sample : (List Bool × List Bool) × List TraceStep) : Bool :=
    let keys := sample.1
    let trace := sample.2
    let res := trace.foldl (replayPairStep machine (fuelOf keys.1))
      (FiniteConfig.init machine.initial (wordOf keys.1), [])
    let msig := msgSigDecoder.decode res.1.tapes.output
    let queried := res.2.map Prod.fst
    !queried.contains msig.1 && verify S H (pkOf keys.1) 0 msig.1 msig.2
  let winSig (sample : (List Bool × List Bool) × List TraceStep) : Bool :=
    let keys := sample.1
    let trace := sample.2
    let res := trace.foldl (replayPairStep machine (fuelOf keys.1))
      (FiniteConfig.init machine.initial (wordOf keys.1), [])
    let msig := msgSigDecoder.decode res.1.tapes.output
    let parsedSig := sigDecoder.decode msig.2
    let MStar := otsMsg H n parsedSig.1 (H.eval n parsedSig.1 msig.1)
    let queriedS := res.2.map fun p => otsMsg H n p.2 (H.eval n p.2 p.1)
    (MStar.length == otsParam H n) && !queriedS.contains MStar &&
      S.verify keys.1 MStar parsedSig.2
  have hwordEq :
      ProbComp.eval ((wordScheme S H).eufCmaGame adversary n) = μ.map winGame := by
    simp only [WordSignatureScheme.eufCmaGame, wordScheme_keyGen, wordScheme_verify, keyGen,
      μ, traceSamplePMF, runWith_norm, pmf_norm]
    peel_binds keys
    have hsim := ProbOracleComp.runWith_map_state
      (oracle := pairSigningOracle S H n keys.2)
      (oracle' := fun q s =>
        ProbComp.eval ((wordScheme S H).signingOracle (pkOf keys.2) q s))
      (represent := List.map Prod.fst)
      (step := by
        intro ⟨⟨⟩, msg⟩ pairs
        simp only [pairSigningOracle, WordSignatureScheme.signingOracle, wordScheme_sign, sign,
          pkOf, simPkOf, keyDecoder.decode_enc, ↓reduceIte, BitString.eval_sampleList,
          List.map_cons, _root_.PMF.map, pmf_norm])
      (adversary n (pkOf keys.1)) []
    have hrun := hrunPair keys
    simp only [List.map_nil, pkOf, simPkOf] at hsim hrun
    rw [← hsim, hrun]
    simp only [_root_.PMF.map, winGame, pkOf, wordOf, fuelOf, simPkOf, simWordOf, simFuelOf,
      pmf_norm]
  have hsigEq :
      ProbComp.eval (S.eufCmaGame (manyTimeForger H sigBound adversary) (otsParam H n)) =
        μ.map winSig := by
    simp only [SignatureScheme.eufCmaGame, manyTimeForger, simPkOf, otsParamInv_otsParam,
      ↓reduceIte, μ, traceSamplePMF, runWith_norm, pmf_norm]
    peel_binds keys
    have hsim := ProbOracleComp.runWith_map_state
      (oracle := pairSigningOracle S H n keys.2)
      (oracle' := fun q (state : Unit × List (List Bool)) =>
        (ProbOracleComp.runWith (fun req s => ProbComp.eval (S.signingOracle keys.2 req s))
          (StateT.run (manyTimeHandler H sigBound n q) state.1) state.2).map
            (fun p => (p.1.1, p.1.2, p.2)))
      (represent := fun pairs : List (List Bool × List Bool) =>
        ((), pairs.map fun p => otsMsg H n p.2 (H.eval n p.2 p.1)))
      (step := by
        intro ⟨⟨⟩, msg⟩ pairs
        change _ = (ProbOracleComp.runWith
          (fun req s => ProbComp.eval (S.signingOracle keys.2 req s))
          (manyTimeHandler H sigBound n ((), msg) ())
          (pairs.map fun p => otsMsg H n p.2 (H.eval n p.2 p.1))).map
            (fun p => (p.1.1, p.1.2, p.2))
        simp only [manyTimeHandler, SignatureScheme.signingOracle, pairSigningOracle,
          BitString.eval_sampleList, List.map_cons, _root_.PMF.map, runWith_norm, pmf_norm]
        peel_binds hashKey ots
        have htake : ots.take (sigBound n) = ots :=
          List.take_of_length_le
            (hsigBound n keys.1 keys.2 keys_mem (otsMsg H n hashKey (H.eval n hashKey msg))
              (length_otsMsg H n hashKey _) ots ots_mem)
        simp only [htake])
      (adversary n (pkOf keys.1)) []
    have hrun := hrunPair keys
    simp only [List.map_nil, pkOf, simPkOf] at hsim hrun
    rw [← hsim, hrun]
    simp only [_root_.PMF.map, winSig, otsForgeryOf, wordOf, fuelOf, simWordOf, simFuelOf,
      pmf_norm]
  have hpointwise : ∀ sample ∈ μ.support,
      winGame sample = true →
        winSig sample = true ∨ ∃ i : Fin D, winTcrAt H machine c d n i.val sample = true := by
    rintro ⟨keys, trace⟩ hsupp hwin
    simp only [μ, traceSamplePMF, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hsupp
    obtain ⟨keys', hkeys, trace', htrace, heqPair⟩ := hsupp
    rcases Prod.mk.inj heqPair.symm with ⟨rfl, rfl⟩
    have hpkLen : keys.1.length ≤ ckg * (otsParam H n + 1) ^ dkg :=
      hpkBound n keys.1 keys.2 hkeys
    have hfuelLe : fuelOf keys.1 ≤ fuelUpper H ckg dkg c d n := by
      have hwLen : (wordOf keys.1).length + 1 ≤
          4 * n + ckg * (otsParam H n + 1) ^ dkg + 3 := by
        dsimp only [wordOf, pkOf, simWordOf, simPkOf]
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
        omega
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hwLen d)
    have hfuelLtD : fuelOf keys.1 < D :=
      Nat.lt_of_le_of_lt hfuelLe (lt_dyadicSize _)
    have htraceProps := mem_support_iterate_sampleStep_props S H machine n keys.2
      (fuelOf keys.1) (wordOf keys.1) (fuelOf keys.1) [] htrace
    have htraceLen : trace.length = fuelOf keys.1 := by simpa using htraceProps.2.1
    have htraceKeys : ∀ item ∈ trace, item.hashKey.length = H.keyLen n :=
      htraceProps.2.2 (by intro _ h; cases h)
    let res := trace.foldl (replayPairStep machine (fuelOf keys.1))
      (FiniteConfig.init machine.initial (wordOf keys.1), [])
    have hresFst : res.1 = replayCfg machine (fuelOf keys.1) (wordOf keys.1) trace :=
      replayPairStep_fst machine (fuelOf keys.1) _ [] trace
    let msig := msgSigDecoder.decode res.1.tapes.output
    let parsedSig := sigDecoder.decode msig.2
    let MStar := otsMsg H n parsedSig.1 (H.eval n parsedSig.1 msig.1)
    change (!(res.2.map Prod.fst).contains msig.1 &&
        verify S H (pkOf keys.1) 0 msig.1 msig.2) = true at hwin
    dsimp only [pkOf, simPkOf] at hwin
    simp only [Bool.and_eq_true, Bool.not_eq_true', verify, keyDecoder.decode_enc,
      beq_self_eq_true, Bool.true_and, beq_iff_eq] at hwin
    change (res.2.map Prod.fst).contains msig.1 = false ∧
      parsedSig.1.length = H.keyLen n ∧
      S.verify keys.1 MStar parsedSig.2 = true at hwin
    obtain ⟨hnotQueried, hkStarLen, hverifyS⟩ := hwin
    let queriedS := res.2.map fun p => otsMsg H n p.2 (H.eval n p.2 p.1)
    by_cases hMemS : MStar ∈ queriedS
    · right
      obtain ⟨⟨mJ, kJ⟩, hpMem, hMEq⟩ := List.mem_map.mp hMemS
      obtain ⟨j, hjLt, hqJ, hkJEq⟩ := exists_slot_of_mem_replayPairs machine
        (fuelOf keys.1) (wordOf keys.1) trace hpMem
      have hjFuel : j < fuelOf keys.1 := hjLt.trans_eq htraceLen
      have hjD : j < D := hjFuel.trans hfuelLtD
      have hkJLen : kJ.length = H.keyLen n := by
        rw [← hkJEq, List.getD_eq_getElem _ _ hjLt]
        exact htraceKeys _ (List.getElem_mem hjLt)
      have hdJLen : (H.eval n kJ mJ).length = H.digestLen n :=
        H.length_eq n kJ mJ hkJLen
      have hdStarLen : (H.eval n parsedSig.1 msig.1).length = H.digestLen n :=
        H.length_eq n parsedSig.1 msig.1 hkStarLen
      obtain ⟨hkEq, hdEq⟩ := otsMsg_inj H hkJLen hdJLen hkStarLen hdStarLen hMEq
      rw [← hkEq] at hdEq
      have hmNe : mJ ≠ msig.1 := by
        intro hEq
        have hmemFst : msig.1 ∈ res.2.map Prod.fst := by
          rw [← hEq]
          exact List.mem_map.mpr ⟨(mJ, kJ), hpMem, rfl⟩
        have hcontTrue : (res.2.map Prod.fst).contains msig.1 = true :=
          List.contains_iff_mem.mpr hmemFst
        exact Bool.false_ne_true (hnotQueried.symm.trans hcontTrue)
      refine ⟨⟨j, hjD⟩, ?_⟩
      dsimp only [winTcrAt, fuelOf, wordOf] at hjFuel hqJ hresFst ⊢
      simp only [decide_eq_true hjFuel, Bool.true_and, hqJ, hkJEq]
      rw [← hresFst]
      dsimp only [msig] at hdEq hmNe
      simp only [isCollision, hdEq, beq_self_eq_true, Bool.and_true, Bool.true_and, bne_iff_ne]
      exact hmNe
    · left
      have hcontFalse : queriedS.contains MStar = false :=
        Bool.eq_false_iff.mpr (mt List.contains_iff_mem.mp hMemS)
      change ((MStar.length == otsParam H n) && !queriedS.contains MStar &&
        S.verify keys.1 MStar parsedSig.2) = true
      simp only [MStar, length_otsMsg, beq_self_eq_true, hcontFalse, Bool.not_false,
        hverifyS, Bool.and_self]
  rw [hwordEq, hsigEq, eval_targetCollisionGame_tcrMultiAdversary S H machine ckg dkg c d n]
  have hDposNN : (0 : ℝ≥0) < D := by exact_mod_cast hDpos
  have havg : (D : ℝ≥0) *
      Game.succProbability ((PMF.uniformOfFintype (Fin D)).bind fun i =>
        tcrSlotTrial S H machine c d n i.val) =
      ∑ i : Fin D, Game.succProbability (tcrSlotTrial S H machine c d n i.val) := by
    rw [Game.succProbability_uniform, Fintype.card_fin, mul_div_cancel₀ _ hDposNN.ne']
  calc
    Game.succProbability (μ.map winGame)
      ≤ Game.succProbability (μ.map winSig) +
          ∑ i : Fin D, ((μ.map (winTcrAt H machine c d n i.val)) true).toNNReal :=
        succProbability_map_le_add_sum μ winGame winSig
          (fun i : Fin D => winTcrAt H machine c d n i.val) hpointwise
    _ ≤ Game.succProbability (μ.map winSig) +
          ∑ i : Fin D, Game.succProbability (tcrSlotTrial S H machine c d n i.val) :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
          succProbability_winTcrAt_le_trial S H machine c d n i.val)
    _ = Game.succProbability (μ.map winSig) +
          (D : ℝ≥0) *
            Game.succProbability ((PMF.uniformOfFintype (Fin D)).bind fun i =>
              tcrSlotTrial S H machine c d n i.val) := by
        rw [havg]

/-- **Existential many-query reduction for `TCRSignature.wordScheme`** ([BonehShoup2023], Section
13.2.1, Theorem 13.2, p. 534): every strict oracle-PPT forger `adversary` against
`wordScheme S H` induces a strict oracle-PPT forger `sigForger` against `S`, a strict PPT
two-stage `TargetCollisionFinder` `tcrAdv` against `H`, and a `PolynomiallyBounded` loss schedule
`loss` bounding `adversary`'s forging probability at every security parameter `n`. -/
theorem exists_reduction_wordScheme_eufCmaGame_le (S : SignatureScheme) (H : KeyedHashFamily)
    {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    ∃ (sigForger : Forger) (tcrAdv : TargetCollisionFinder) (loss : ℕ → ℕ),
      IsOraclePPT (encPair encBits encBits) sigForger ∧
      tcrAdv.IsPPT ∧
      PolynomiallyBounded loss ∧
      ∀ n, Game.succProbability (ProbComp.eval ((wordScheme S H).eufCmaGame adversary n)) ≤
        Game.succProbability (ProbComp.eval (S.eufCmaGame sigForger (otsParam H n))) +
          (loss n : ℝ≥0) *
            Game.succProbability
              (ProbComp.eval
                (targetCollisionGame H.keyLen H.eval (fun _ _ => true) tcrAdv n)) := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, hmachine⟩ := hadversary.on
  obtain ⟨ckg, dkg, sigBound, hsigBoundPoly, hpkBoundLe, hsigBoundLe⟩ := exists_ots_bounds S H
  have hlossPoly : PolynomiallyBounded (fun n => dyadicSize (fuelUpper H ckg dkg c d n)) :=
    (ComputableInPolyTime.unary_dyadicSize.comp
      (computableInPolyTime_fuelUpper H ckg dkg c d)).polynomiallyBounded
  exact ⟨manyTimeForger H sigBound adversary,
    tcrMultiAdversary S H machine ckg dkg c d,
    fun n => dyadicSize (fuelUpper H ckg dkg c d n),
    isOraclePPT_manyTimeForger H hsigBoundPoly hadversary,
    isPPT_tcrMultiAdversary S H machine ckg dkg c d,
    hlossPoly,
    succProbability_wordScheme_eufCmaGame_le_of_machine S H ckg dkg
      (fun n pk sk h => hpkBoundLe n (pk, sk) h) sigBound
      (fun n pk sk h => hsigBoundLe n (pk, sk) h) adversary machine c d hmachine⟩

end TCRSignature

/-- **Boneh–Shoup Theorem 13.2** ([BonehShoup2023], Section 13.2.1, p. 534): if `S` is a stateless
many-time `EUFCMA`-secure `SignatureScheme` on fixed-length bit strings and `H` is an unrestricted
target collision-resistant `KeyedHashFamily` on `List Bool`, then `TCRSignature.wordScheme S H` is
an `EUFCMA`-secure stateless `WordSignatureScheme` on arbitrary-length `List Bool` messages. -/
theorem SignatureScheme.EUFCMA.eufCMA_wordScheme
    {S : SignatureScheme} (hS : S.EUFCMA)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    (TCRSignature.wordScheme S H).EUFCMA := by
  refine WordSignatureScheme.EUFCMA.of_negligible fun adversary hadversary => ?_
  obtain ⟨sigForger, tcrAdv, loss, hsigPPT, htcrPPT, hlossPoly, hbound⟩ :=
    TCRSignature.exists_reduction_wordScheme_eufCmaGame_le S H hadversary
  have := TCRSignature.negligible_comp_otsParam (hS.negligible sigForger hsigPPT) H
  have := hH.negligible tcrAdv htcrPPT
  negligible using hbound

/-- Any `EUFCMA`-secure `WordSignatureScheme` implies the existence of a uniform `OneWay`
function. -/
theorem WordSignatureScheme.EUFCMA.exists_oneWay {S : WordSignatureScheme} (hS : S.EUFCMA) :
    ∃ f, OneWay f :=
  hS.toSignatureScheme.exists_oneWay

/-- **Stateless unrestricted-message `EUFCMA` signatures from one-way functions and target
collision-resistant hash families** ([NaorYung1989], Section 4; [BonehShoup2023], Sections 13.2.1
and 14.6): any uniform `OneWay` function and any unrestricted target collision-resistant
`KeyedHashFamily` yield a stateless many-time `WordSignatureScheme` satisfying `EUFCMA` on all
`List Bool` messages. -/
theorem OneWay.exists_wordEUFCMA_of_targetCollisionResistant
    {f : List Bool → List Bool} (hf : OneWay f)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    ∃ W : WordSignatureScheme, W.EUFCMA := by
  obtain ⟨S, hS⟩ := hf.exists_eufCMA_of_targetCollisionResistant hH
  exact ⟨TCRSignature.wordScheme S H, hS.eufCMA_wordScheme hH⟩

/-- **Unrestricted-message Naor–Yung signature theorem** ([NaorYung1989], Theorem 2 / Section 4;
[BonehShoup2023], Section 13.2.1, Theorem 13.2): every one-way permutation implies the existence of
a stateless many-time `EUFCMA`-secure `WordSignatureScheme` on arbitrary-length `List Bool`
messages. -/
theorem OneWayPermutation.exists_wordEUFCMA
    {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    ∃ W : WordSignatureScheme, W.EUFCMA := by
  obtain ⟨H, hH⟩ := hf.exists_targetCollisionResistant_keyedHashFamily
  exact hf.oneWay.exists_wordEUFCMA_of_targetCollisionResistant hH

end Cslib.Crypto
