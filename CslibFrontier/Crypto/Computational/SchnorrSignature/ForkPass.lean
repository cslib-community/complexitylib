/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrSignature.EncodedROM
public import CslibFrontier.Crypto.Computational.Signature.WordRandomOracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
import CslibFrontier.Computability.Probabilistic.OracleSimulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# One native pass of the Schnorr forking reduction

The security proof of Schnorr signatures in the random-oracle model
(`succProbability_eufCmaGame_schnorrWordROMScheme_le`) runs the forger twice through the existing
`FiatShamir.forkingProgram`: signing calls are answered from presampled simulated transcripts
`(t, c, z)`, which also program the oracle at `(msg, t)`, and hash calls are answered from a table
or from a list of presampled answers. That program is a typed distribution-level object with no
runtime bound. This module gives one native pass of it, for a native forger given as a guarded
saved-coin replay (`savedWordReplay`), and proves that the pass is strict PPT and computes exactly
what the typed program computes.

The native state (`SchnorrForkState`) holds the oracle table, the signed messages, the number of
own hash queries and the number of handled calls; challenges and transcripts are words. One call
(`schnorrForkStep`) mirrors `ForkingReduction.handler`: every call consumes a transcript, and a new
hash point consumes the next answer. When the answers run out, a new point gets the empty reply
and changes nothing. This keeps each table tag at most the number of answers, so the state grows
by an amount bounded by the input and the request (`IsOraclePPTOn.run_interpret_preprocess`). The
final check (`schnorrForkFinish`) decodes the forgery with the existing total pair decoder, verifies
it with `schnorrSigVerifyBits`, and returns the code of the named index (`forkIndexCode`, mirroring
`validIndex`), the challenge and the response.

`eval_schnorrForkPass` shows that on a canonical public key, at least `B` transcripts and `B + 1`
answers, where `B = savedCoinBudget …` bounds the forger's calls, the pass returns exactly the
index, challenge and response that `forkingAlgorithm` reads from `FiatShamir.forkingProgram` for
`schnorrWordROMScheme` and the decoded saved-coin forger. Exhaustion of the banks is ruled out by
the call budget, not assumed, so the typed program's default answer is never used.

Sampling the banks, the second pass with spliced answers, extraction, and the discrete-logarithm
theorem are separate steps (#2568).

## Main definitions

* `SchnorrForkEntry`, `SchnorrForkState`, `SchnorrForkBanks`, `SchnorrForkPassInput`: the table
  entries, state, banks and input of a native pass, with `enc_structure` encodings.
* `schnorrForkStep`: one call of a native pass.
* `schnorrForkRun`: the guarded replay run against `schnorrForkStep`.
* `schnorrForkFinish`: the final check.
* `schnorrForkPass`: one native pass.
* `forkIndexCode`, `forkRunWords`, `transcriptWords`: the native code of a named fork index, the
  words a pass returns for one typed run, and the native view of a typed transcript.

## Main results

* `computableInPolyTime_schnorrForkStep`, `computableInPolyTime_schnorrForkFinish`: the step and
  the final check run in polynomial time.
* `isPPTOn_schnorrForkRun`, `isPPTOn_schnorrForkPass`: the run and the pass are strict PPT in
  their full inputs, for every replay machine.
* `eval_schnorrForkPass`: the pass agrees exactly with the typed forking program.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.6.1. The native realization is original.
-/
public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Protocols.ROMSignature
open scoped ENNReal NNReal

/-- An entry of the oracle table of a native forking pass. -/
structure SchnorrForkEntry where
  /-- The hash point. -/
  point : List Bool
  /-- The challenge word at the point. -/
  challenge : List Bool
  /-- `0` for a point programmed by a signing call, `i + 1` for the pass's own query number `i`. -/
  tag : ℕ

/-- The encoding of a table entry: the point and challenge words, then the tag in unary. -/
enc_structure encSchnorrForkEntry : SchnorrForkEntry where
  point : encBits, challenge : encBits, tag : encUnary

/-- The state of a native forking pass. -/
structure SchnorrForkState where
  /-- The oracle table, newest entry first. -/
  table : List SchnorrForkEntry
  /-- The signed messages, newest first. -/
  log : List (List Bool)
  /-- The number of the pass's own hash queries. -/
  count : ℕ
  /-- The number of handled calls, which is also the number of consumed transcripts. -/
  used : ℕ

/-- The encoding of a pass state, with both counters in unary. -/
enc_structure encSchnorrForkState : SchnorrForkState where
  table : (encList encSchnorrForkEntry), log : (encList encBits), count : encUnary,
  used : encUnary

/-- The presampled values of one pass. -/
structure SchnorrForkBanks where
  /-- Simulated transcripts `(t, c, z)`, one consumed per call. -/
  transcripts : List (List Bool × List Bool × List Bool)
  /-- Challenge answers, one consumed per own hash query. -/
  answers : List (List Bool)

/-- The encoding of the banks: the transcripts as a list of `encBits`-framed word triples
`(t, c, z)`, then the answers as a list of `encBits`-framed words. -/
enc_structure encSchnorrForkBanks : SchnorrForkBanks where
  transcripts : (encList (encPair encBits (encPair encBits encBits))), answers : (encList encBits)

/-- One call of the native forking pass. A signing call on `msg` takes the next transcript
`(t, c, z)`, returns `(t, z)`, programs the point `(msg, t)` with `c` and logs `msg`. A hash call
returns the table's challenge for its point, or else the next unused answer, which it records as
the pass's own query. Every call consumes one transcript, as in `ForkingReduction.handler`. Once
the answers run out, a new point gets the empty reply and changes nothing, which keeps every tag
at most the number of answers. -/
@[expose] def schnorrForkStep (banks : SchnorrForkBanks) (request : Bool × List Bool)
    (state : SchnorrForkState) : List Bool × SchnorrForkState :=
  let (hash, word) := request
  if hash then
    match state.table.find? (fun entry => entry.point == word) with
    | some entry => (entry.challenge, { state with used := state.used + 1 })
    | none =>
      match banks.answers[state.count]? with
      | some challenge =>
        (challenge, ⟨⟨word, challenge, state.count + 1⟩ :: state.table, state.log,
          state.count + 1, state.used + 1⟩)
      | none => ([], { state with used := state.used + 1 })
  else
    let (t, challenge, z) := banks.transcripts.getD state.used ([], [], [])
    (encPair encBits encBits (t, z),
      ⟨⟨encPair encBits encBits (word, t), challenge, 0⟩ :: state.table, word :: state.log,
        state.count, state.used + 1⟩)

/-- The input of one call of the native forking step. -/
private abbrev StepInput := SchnorrForkBanks × (Bool × List Bool) × SchnorrForkState

private abbrev encStepInput : StepInput ↪ List Bool :=
  encPair encSchnorrForkBanks (encPair (encPair encBool encBits) encSchnorrForkState)

/-- A signing call of `schnorrForkStep` with its transcript `(t, c, z)` already read. -/
private def forkSignFrom (p : StepInput × (List Bool × List Bool × List Bool)) :
    List Bool × SchnorrForkState :=
  (encPair encBits encBits (p.2.1, p.2.2.2),
    ⟨⟨encPair encBits encBits (p.1.2.1.2, p.2.1), p.2.2.1, 0⟩ :: p.1.2.2.table,
      p.1.2.1.2 :: p.1.2.2.log, p.1.2.2.count, p.1.2.2.used + 1⟩)

/-- A hash call of `schnorrForkStep` that takes the fresh answer `p.2`. -/
private def forkFreshFrom (p : StepInput × List Bool) : List Bool × SchnorrForkState :=
  (p.2, ⟨⟨p.1.2.1.2, p.2, p.1.2.2.count + 1⟩ :: p.1.2.2.table, p.1.2.2.log, p.1.2.2.count + 1,
    p.1.2.2.used + 1⟩)

/-- A call that changes nothing but the call count, replying `p.2`. -/
private def forkSkipWith (p : StepInput × List Bool) : List Bool × SchnorrForkState :=
  (p.2, ⟨p.1.2.2.table, p.1.2.2.log, p.1.2.2.count, p.1.2.2.used + 1⟩)

/-- `schnorrForkStep` with its reads made explicit, for the runtime certificate. -/
private def forkStepProj (x : StepInput) : List Bool × SchnorrForkState :=
  if x.2.1.1 then
    (x.2.2.table.find? (fun entry => entry.point == x.2.1.2)).elim
      ((x.1.answers[x.2.2.count]?).elim (forkSkipWith (x, [])) fun c => forkFreshFrom (x, c))
      fun entry => forkSkipWith (x, entry.challenge)
  else forkSignFrom (x, x.1.transcripts.getD x.2.2.used ([], [], []))

private theorem schnorrForkStep_eq_proj (x : StepInput) :
    schnorrForkStep x.1 x.2.1 x.2.2 = forkStepProj x := by
  obtain ⟨banks, ⟨hash, word⟩, state⟩ := x
  cases hash
  · rfl
  · simp only [schnorrForkStep, forkStepProj, ite_true]
    cases state.table.find? (fun entry => entry.point == word) with
    | some entry => rfl
    | none => cases banks.answers[state.count]? <;> rfl

/-- The native forking step is computable in polynomial time. -/
theorem computableInPolyTime_schnorrForkStep :
    ComputableInPolyTime
      (fun (banks, request, state) => schnorrForkStep banks request state)
      (encPair encSchnorrForkBanks (encPair (encPair encBool encBits) encSchnorrForkState))
      (encPair encBits encSchnorrForkState) := by
  have h : (fun x : StepInput =>
      match x with | (banks, request, state) => schnorrForkStep banks request state) =
      forkStepProj := funext schnorrForkStep_eq_proj
  change ComputableInPolyTime (fun x : StepInput =>
      match x with | (banks, request, state) => schnorrForkStep banks request state)
    encStepInput (encPair encBits encSchnorrForkState)
  rw [h]
  have hsign : ComputableInPolyTime forkSignFrom
      (encPair encStepInput (encPair encBits (encPair encBits encBits)))
      (encPair encBits encSchnorrForkState) := by
    have hsig : ComputableInPolyTime
        (fun p : StepInput × (List Bool × List Bool × List Bool) =>
          (encPair encBits encBits) (p.2.1, p.2.2.2))
        (encPair encStepInput (encPair encBits (encPair encBits encBits))) encBits := by
      apply ComputableInPolyTime.encoding_comp
      fun_prop
    have hpoint : ComputableInPolyTime
        (fun p : StepInput × (List Bool × List Bool × List Bool) =>
          (encPair encBits encBits) (p.1.2.1.2, p.2.1))
        (encPair encStepInput (encPair encBits (encPair encBits encBits))) encBits := by
      apply ComputableInPolyTime.encoding_comp
      fun_prop
    unfold forkSignFrom
    fun_prop
  have hfresh : ComputableInPolyTime forkFreshFrom (encPair encStepInput encBits)
      (encPair encBits encSchnorrForkState) := by
    unfold forkFreshFrom
    fun_prop
  have hskip : ComputableInPolyTime forkSkipWith (encPair encStepInput encBits)
      (encPair encBits encSchnorrForkState) := by
    unfold forkSkipWith
    fun_prop
  have hid : ComputableInPolyTime (fun x : StepInput => x) encStepInput encStepInput := by
    fun_prop
  have htable : ComputableInPolyTime (fun x : StepInput => x.2.2.table) encStepInput
      (encList encSchnorrForkEntry) := by fun_prop
  have htest : ComputableInPolyTime
      (fun p : StepInput × SchnorrForkEntry => p.2.point == p.1.2.1.2)
      (encPair encStepInput encSchnorrForkEntry) encBool := by fun_prop
  have hfind := ComputableInPolyTime.findWithInput
    (test := fun x (entry : SchnorrForkEntry) => entry.point == x.2.1.2) htable htest
  have hanswers : ComputableInPolyTime (fun x : StepInput => x.1.answers) encStepInput
      (encList encBits) := by fun_prop
  have hcount : ComputableInPolyTime (fun x : StepInput => x.2.2.count)
      encStepInput encUnary := by fun_prop
  have hanswer := ComputableTidilyInPolyTime.getElem? (encA := encBits) hanswers.tidy hcount.tidy
  have hmiss := ComputableInPolyTime.optionElimWithInput hanswer.computableInPolyTime
    (hskip.comp (hid.prod (ComputableInPolyTime.const [])))
    (body := fun x c => forkFreshFrom (x, c)) hfresh
  have hhit : ComputableInPolyTime (fun p : StepInput × SchnorrForkEntry =>
      forkSkipWith (p.1, p.2.challenge))
      (encPair encStepInput encSchnorrForkEntry) (encPair encBits encSchnorrForkState) :=
    hskip.comp (by fun_prop)
  have hhash := ComputableInPolyTime.optionElimWithInput hfind hmiss
    (body := fun x entry => forkSkipWith (x, entry.challenge)) hhit
  have htranscripts : ComputableInPolyTime (fun x : StepInput => x.1.transcripts) encStepInput
      (encList (encPair encBits (encPair encBits encBits))) := by fun_prop
  have hused : ComputableInPolyTime (fun x : StepInput => x.2.2.used) encStepInput
      encUnary := by fun_prop
  have hread := ComputableInPolyTime.listGetDWithInput htranscripts hused ([], [], [])
  have hsign' := hsign.comp (hid.prod hread)
  have hguard : ComputableInPolyTime (fun x : StepInput => x.2.1.1) encStepInput
      encBool := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.cond hguard.tidy hhash.tidy hsign'.tidy)

/-! ### The native pass -/

/-- The input of one native forking pass. -/
structure SchnorrForkPassInput where
  /-- The security parameter. -/
  secParam : ℕ
  /-- The public-key word given to the forger. -/
  publicKey : List Bool
  /-- The forger's saved coin tape. -/
  tape : List Bool
  /-- The presampled transcripts and answers. -/
  banks : SchnorrForkBanks

/-- The encoding of a pass input: the security parameter in unary, the public-key and tape words,
then the banks. -/
enc_structure encSchnorrForkPassInput : SchnorrForkPassInput where
  secParam : encUnary, publicKey : encBits, tape : encBits, banks : encSchnorrForkBanks

/-- Run the guarded saved-coin replay of a native forger against `schnorrForkStep`, from the empty
table. Returns the forger's output words and the final state. -/
noncomputable def schnorrForkRun {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ)
    (input : SchnorrForkPassInput) : ProbComp ((List Bool × List Bool) × SchnorrForkState) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (fun request state => pure (schnorrForkStep input.banks request state)))
    (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c e keyC keyD
      (input.secParam, input.publicKey, input.tape))).run ⟨[], [], 0, 0⟩

/-- Every challenge in the table of a reachable state is no longer than the encoded banks. -/
private def ForkInvariant (banks : SchnorrForkBanks) (state : SchnorrForkState) : Prop :=
  ∀ entry ∈ state.table, entry.challenge.length ≤ (encSchnorrForkBanks banks).length

private theorem forkInvariant_schnorrForkStep (banks : SchnorrForkBanks)
    (request : Bool × List Bool)
    (state : SchnorrForkState) (h : ForkInvariant banks state) :
    ForkInvariant banks (schnorrForkStep banks request state).2 ∧
      (schnorrForkStep banks request state).1.length ≤
        2 * (encSchnorrForkBanks banks).length + 1 ∧
      (encSchnorrForkState (schnorrForkStep banks request state).2).length ≤
        (encSchnorrForkState state).length +
          40 * ((encSchnorrForkBanks banks).length + request.2.length + 1) := by
  obtain ⟨transcripts, answers⟩ := banks
  obtain ⟨hash, word⟩ := request
  obtain ⟨table, log, count, used⟩ := state
  have hbanks : (encList (encPair encBits (encPair encBits encBits)) transcripts).length +
      (encList encBits answers).length ≤ (encSchnorrForkBanks ⟨transcripts, answers⟩).length := by
    enc_len [encSchnorrForkBanks_apply]
  cases hash with
  | false =>
    have hmem : (encPair encBits (encPair encBits encBits)
        (transcripts.getD used ([], [], []))).length ≤
        (encList (encPair encBits (encPair encBits encBits)) transcripts).length + 2 := by
      rw [List.getD_eq_getElem?_getD]
      cases hget : transcripts[used]? with
      | none => simp
      | some tr =>
        have := length_le_encList_of_mem (encPair encBits (encPair encBits encBits))
          (List.mem_of_getElem? hget)
        simp only [Option.getD_some]
        omega
    simp only [schnorrForkStep, Bool.false_eq_true, ite_false]
    generalize transcripts.getD used ([], [], []) = tr at hmem ⊢
    obtain ⟨t, ch, z⟩ := tr
    refine ⟨?_, ?_, ?_⟩
    · intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · dsimp only
        enc_len at hmem ⊢
      · exact h entry hentry
    · enc_len at hmem ⊢
    · enc_len [encSchnorrForkState_apply, encSchnorrForkEntry_apply] at hmem ⊢
  | true =>
    simp only [schnorrForkStep, ite_true]
    cases hfind : table.find? (fun entry => entry.point == word) with
    | some entry =>
      have hch := h _ (List.mem_of_find?_eq_some hfind)
      refine ⟨h, ?_, ?_⟩
      · dsimp only at hch ⊢
        omega
      · enc_len [encSchnorrForkState_apply]
    | none =>
      cases hget : answers[count]? with
      | none => exact ⟨h, by simp, by enc_len [encSchnorrForkState_apply]⟩
      | some ch =>
        have hch := length_le_encList_of_mem encBits (List.mem_of_getElem? hget)
        simp only [encBits_apply] at hch
        have hcount : count < answers.length := (List.getElem?_eq_some_iff.mp hget).1
        have hlen := length_le_length_encList encBits answers
        refine ⟨?_, ?_, ?_⟩
        · intro entry hentry
          simp only [List.mem_cons] at hentry
          rcases hentry with rfl | hentry
          · dsimp only
            omega
          · exact h entry hentry
        · dsimp only
          omega
        · enc_len [encSchnorrForkState_apply, encSchnorrForkEntry_apply] at hch ⊢

/-- **The native forking run is strict PPT** in its full input: the security parameter, public-key
word, saved tape and both banks, for every guarded replay machine. -/
theorem isPPTOn_schnorrForkRun {k : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ) :
    IsPPTOn encSchnorrForkPassInput (encPair (encPair encBits encBits) encSchnorrForkState)
      (schnorrForkRun machine c e keyC keyD) := by
  have hstep := computableInPolyTime_schnorrForkStep
  have hhandler : IsPPTOn
      (encPair encSchnorrForkPassInput (encPair (encPair encBool encBits) encSchnorrForkState))
      (encPair encBits encSchnorrForkState)
      (fun (caller, request, state) => pure (schnorrForkStep caller.banks request state)) := by
    have hprep : ComputableInPolyTime
        (fun x : SchnorrForkPassInput × (Bool × List Bool) × SchnorrForkState =>
          (x.1.banks, x.2.1, x.2.2))
        (encPair encSchnorrForkPassInput (encPair (encPair encBool encBits) encSchnorrForkState))
        (encPair encSchnorrForkBanks (encPair (encPair encBool encBits) encSchnorrForkState)) := by
      fun_prop
    exact (hstep.comp hprep).isPPTOn
  have hprepare : ComputableTidilyInPolyTime
      (fun caller : SchnorrForkPassInput => (caller.secParam, caller.publicKey, caller.tape))
      encSchnorrForkPassInput encReplayInput := by
    apply ComputableInPolyTime.tidy
    fun_prop
  have hrun := (isOraclePPTOn_savedWordReplay machine c e keyC keyD).run_interpret_preprocess
    (input := encSchnorrForkPassInput) (operationEncoding := encBool)
    (stateEncoding := encSchnorrForkState)
    (handler := fun caller request state => pure (schnorrForkStep caller.banks request state))
    (prepare := fun caller : SchnorrForkPassInput => (caller.secParam, caller.publicKey,
      caller.tape))
    (initial := fun _ => (⟨[], [], 0, 0⟩ : SchnorrForkState))
    (resources := fun caller word =>
      40 * ((encSchnorrForkPassInput caller).length + word.length + 1))
    hprepare hhandler (ComputableTidilyInPolyTime.const _)
    (fun caller state => ForkInvariant caller.banks state) (fun _ _ => by simp)
    (by fun_prop) ?_
  · exact hrun
  · intro caller request state hstate result hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst hresult
    obtain ⟨hinv, hreply, hgrowth⟩ :=
      forkInvariant_schnorrForkStep caller.banks request state hstate
    have hbanks : (encSchnorrForkBanks caller.banks).length ≤
        (encSchnorrForkPassInput caller).length := by
      enc_len [encSchnorrForkPassInput_apply]
    refine ⟨hinv, ?_, ?_⟩
    · omega
    · have : 40 * ((encSchnorrForkBanks caller.banks).length + request.2.length + 1) ≤
          40 * ((encSchnorrForkPassInput caller).length + request.2.length + 1) := by omega
      omega

/-! ### The final check -/

variable (F : PrimeOrderGroupFamily)

/-- The final check of a native pass on the forger's output `(msg, sig)`. The signature word is
decoded to `(t, z)` with the existing total pair decoder. The challenge of the point `(msg, t)` is
the table's, or else the next unused answer, which then counts as the pass's last own query. The
forgery wins when `schnorrSigVerifyBits` accepts and `msg` was never signed.

The result is the named index, the challenge word and the response word. The index is `j + 1`
when the forgery wins and its point is the pass's own query number `j`, with `j` below both the
number of answers and the number of own queries; otherwise it is `0`. This mirrors `validIndex`
applied to `ForkingReduction.verdict`. -/
@[expose] def schnorrForkFinish (d : F.Desc) (pk : List Bool) (answers : List (List Bool))
    (out : (List Bool × List Bool) × SchnorrForkState) : ℕ × List Bool × List Bool :=
  let ((msg, sig), state) := out
  let (t, z) := (Decoder.bits.pair Decoder.bits).decode sig
  let point := encPair encBits encBits (msg, t)
  let (challenge, tag, queries) :=
    (state.table.find? (fun entry => entry.point == point)).elim
      (answers.getD state.count [], state.count + 1, state.count + 1)
      fun entry => (entry.challenge, entry.tag, state.count)
  let won := F.schnorrSigVerifyBits (d, pk, [], (t, z), challenge) && !state.log.contains msg
  (if won && 0 < tag && tag ≤ answers.length && tag ≤ queries then tag else 0, challenge, z)

/-- The input of `schnorrForkFinish`. -/
private abbrev FinishInput (F : PrimeOrderGroupFamily) :=
  (F.Desc × List Bool × List (List Bool)) × ((List Bool × List Bool) × SchnorrForkState)

/-- The challenge, tag and own-query count of the final check, in projection form. -/
private def forkFinishLookup (x : FinishInput F) : List Bool × ℕ × ℕ :=
  (x.2.2.table.find? (fun entry => entry.point ==
      encPair encBits encBits (x.2.1.1, ((Decoder.bits.pair Decoder.bits).decode x.2.1.2).1))).elim
    (x.1.2.2.getD x.2.2.count [], x.2.2.count + 1, x.2.2.count + 1)
    fun entry => (entry.challenge, entry.tag, x.2.2.count)

/-- `schnorrForkFinish` after the lookup, in projection form. -/
private def forkFinishFrom (p : FinishInput F × (List Bool × ℕ × ℕ)) :
    ℕ × List Bool × List Bool :=
  (if (F.schnorrSigVerifyBits (p.1.1.1, p.1.1.2.1, [],
        (Decoder.bits.pair Decoder.bits).decode p.1.2.1.2, p.2.1) &&
      !p.1.2.2.log.contains p.1.2.1.1) && decide (0 < p.2.2.1) &&
      decide (p.2.2.1 ≤ p.1.1.2.2.length) && decide (p.2.2.1 ≤ p.2.2.2) then p.2.2.1 else 0,
    p.2.1, ((Decoder.bits.pair Decoder.bits).decode p.1.2.1.2).2)

private theorem schnorrForkFinish_eq_proj (x : FinishInput F) :
    F.schnorrForkFinish x.1.1 x.1.2.1 x.1.2.2 x.2 =
      forkFinishFrom F (x, forkFinishLookup F x) := by
  obtain ⟨⟨d, pk, answers⟩, ⟨msg, sig⟩, state⟩ := x
  rfl

private abbrev encFinishInput : FinishInput F ↪ List Bool :=
  encPair (encPair F.encDesc (encPair encBits (encList encBits)))
    (encPair (encPair encBits encBits) encSchnorrForkState)

/-- `computableInPolyTime_schnorrForkFinish` in projection form. -/
private theorem computableInPolyTime_schnorrForkFinish_proj :
    ComputableInPolyTime
      (fun x : FinishInput F => F.schnorrForkFinish x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encFinishInput F) (encPair encUnary (encPair encBits encBits)) := by
  have h : (fun x : FinishInput F => F.schnorrForkFinish x.1.1 x.1.2.1 x.1.2.2 x.2) =
      fun x => forkFinishFrom F (x, forkFinishLookup F x) := funext (schnorrForkFinish_eq_proj F)
  rw [h]
  have hdecode := (Decoder.bits.pair Decoder.bits).computableInPolyTime
  have htz : ComputableInPolyTime
      (fun x : FinishInput F => (Decoder.bits.pair Decoder.bits).decode x.2.1.2)
      (encFinishInput F) (encPair encBits encBits) := hdecode.comp (by fun_prop)
  have hpoint : ComputableInPolyTime
      (fun x : FinishInput F =>
        encPair encBits encBits (x.2.1.1, ((Decoder.bits.pair Decoder.bits).decode x.2.1.2).1))
      (encFinishInput F) encBits := by
    apply ComputableInPolyTime.encoding_comp
    exact (show ComputableInPolyTime (fun x : FinishInput F => x.2.1.1)
      (encFinishInput F) encBits by fun_prop).prod htz.fst'
  have htable : ComputableInPolyTime (fun x : FinishInput F => x.2.2.table) (encFinishInput F)
      (encList encSchnorrForkEntry) := by fun_prop
  have htest : ComputableInPolyTime
      (fun p : FinishInput F × SchnorrForkEntry => p.2.point ==
        encPair encBits encBits (p.1.2.1.1, ((Decoder.bits.pair Decoder.bits).decode p.1.2.1.2).1))
      (encPair (encFinishInput F) encSchnorrForkEntry) encBool := by
    have hfst : ComputableInPolyTime
        (fun p : FinishInput F × SchnorrForkEntry => p.1)
        (encPair (encFinishInput F) encSchnorrForkEntry)
        (encFinishInput F) := by fun_prop
    exact (show ComputableInPolyTime (fun p : FinishInput F × SchnorrForkEntry =>
      p.2.1) _ encBits by fun_prop).beq (hpoint.comp hfst)
  have hfind := ComputableInPolyTime.findWithInput
    (test := fun x (entry : SchnorrForkEntry) => entry.point ==
      encPair encBits encBits (x.2.1.1, ((Decoder.bits.pair Decoder.bits).decode x.2.1.2).1))
    htable htest
  have hanswers : ComputableInPolyTime (fun x : FinishInput F => x.1.2.2)
      (encFinishInput F) (encList encBits) := by fun_prop
  have hcount : ComputableInPolyTime (fun x : FinishInput F => x.2.2.count)
      (encFinishInput F) encUnary := by fun_prop
  have hfresh := ComputableInPolyTime.listGetDWithInput hanswers hcount []
  have hmiss : ComputableInPolyTime
      (fun x : FinishInput F => (x.1.2.2.getD x.2.2.count [], x.2.2.count + 1,
        x.2.2.count + 1)) (encFinishInput F) (encPair encBits (encPair encUnary encUnary)) := by
    fun_prop
  have hhit : ComputableInPolyTime
      (fun p : FinishInput F × SchnorrForkEntry => (p.2.challenge, p.2.tag, p.1.2.2.count))
      (encPair (encFinishInput F) encSchnorrForkEntry)
      (encPair encBits (encPair encUnary encUnary)) := by fun_prop
  have hlookup : ComputableInPolyTime (forkFinishLookup F) (encFinishInput F)
      (encPair encBits (encPair encUnary encUnary)) := by
    unfold forkFinishLookup
    exact ComputableInPolyTime.optionElimWithInput hfind hmiss
      (body := fun x entry => (entry.challenge, entry.tag, x.2.2.count)) hhit
  have hverify := F.computableInPolyTime_schnorrSigVerifyBits
  let encP := encPair (encFinishInput F) (encPair encBits (encPair encUnary encUnary))
  have htzP : ComputableInPolyTime
      (fun p : FinishInput F × (List Bool × ℕ × ℕ) =>
        (Decoder.bits.pair Decoder.bits).decode p.1.2.1.2) encP (encPair encBits encBits) :=
    hdecode.comp (by fun_prop)
  have hverifyP : ComputableInPolyTime
      (fun p : FinishInput F × (List Bool × ℕ × ℕ) =>
        F.schnorrSigVerifyBits (p.1.1.1, p.1.1.2.1, [],
          (Decoder.bits.pair Decoder.bits).decode p.1.2.1.2, p.2.1)) encP encBool :=
    hverify.comp ((show ComputableInPolyTime (fun p : FinishInput F × (List Bool × ℕ × ℕ) =>
      p.1.1.1) encP F.encDesc by fun_prop).prod
      ((show ComputableInPolyTime (fun p : FinishInput F × (List Bool × ℕ × ℕ) =>
        p.1.1.2.1) encP encBits by fun_prop).prod
        ((ComputableInPolyTime.const ([] : List Bool)).prod (htzP.prod (by fun_prop)))))
  have hfrom : ComputableInPolyTime (forkFinishFrom F) encP
      (encPair encUnary (encPair encBits encBits)) := by
    unfold forkFinishFrom
    fun_prop
  have hid : ComputableInPolyTime (fun x : FinishInput F => x) (encFinishInput F)
      (encFinishInput F) := by fun_prop
  exact hfrom.comp (hid.prod hlookup)

/-- The final check of a native pass is computable in polynomial time. -/
theorem computableInPolyTime_schnorrForkFinish :
    ComputableInPolyTime (fun ((d, pk, answers), out) => F.schnorrForkFinish d pk answers out)
      (encPair (encPair F.encDesc (encPair encBits (encList encBits)))
        (encPair (encPair encBits encBits) encSchnorrForkState))
      (encPair encUnary (encPair encBits encBits)) := by
  have h : (fun x : FinishInput F =>
      match x with | ((d, pk, answers), out) => F.schnorrForkFinish d pk answers out) =
      fun x => F.schnorrForkFinish x.1.1 x.1.2.1 x.1.2.2 x.2 := funext fun _ => rfl
  change ComputableInPolyTime (fun x : FinishInput F =>
      match x with | ((d, pk, answers), out) => F.schnorrForkFinish d pk answers out)
    (encFinishInput F) (encPair encUnary (encPair encBits encBits))
  rw [h]
  exact computableInPolyTime_schnorrForkFinish_proj F

/-- **One native pass of the Schnorr forking reduction**: run the forger's guarded saved-coin
replay against `schnorrForkStep`, then make the final check `schnorrForkFinish`. -/
noncomputable def schnorrForkPass {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ) (d : F.Desc)
    (input : SchnorrForkPassInput) : ProbComp (ℕ × List Bool × List Bool) :=
  F.schnorrForkFinish d input.publicKey input.banks.answers <$>
    schnorrForkRun machine c e keyC keyD input

/-- **One native forking pass is strict PPT** in the full group description and pass input:
security parameter, public-key word, saved tape and both banks. -/
theorem isPPTOn_schnorrForkPass {k : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ) :
    IsPPTOn (encPair F.encDesc encSchnorrForkPassInput) (encPair encUnary (encPair encBits encBits))
      (fun (d, input) => F.schnorrForkPass machine c e keyC keyD d input) := by
  have hrun := (isPPTOn_schnorrForkRun machine c e keyC keyD).preprocess
    (input := encPair F.encDesc encSchnorrForkPassInput)
    (prepare := fun x : F.Desc × SchnorrForkPassInput => x.2) (by fun_prop)
  have hfinish := computableInPolyTime_schnorrForkFinish_proj F
  have hprep : ComputableInPolyTime
      (fun p : (F.Desc × SchnorrForkPassInput) × ((List Bool × List Bool) × SchnorrForkState) =>
        ((p.1.1, p.1.2.publicKey, p.1.2.banks.answers), p.2))
      (encPair (encPair F.encDesc encSchnorrForkPassInput)
        (encPair (encPair encBits encBits) encSchnorrForkState))
      (encFinishInput F) := by fun_prop
  have hf := hfinish.comp hprep
  simp only [Function.comp_def] at hf
  have h := hrun.map_with
    (f := fun (x : F.Desc × SchnorrForkPassInput) out =>
      F.schnorrForkFinish x.1 x.2.publicKey x.2.banks.answers out)
    hf
  exact h.congr fun _ => rfl

/-! ### Agreement with the typed forking program -/

section Agreement

variable {m : ℕ}

open OracleComp

/-- The typed forking reduction's state, for `m`-bit challenges and word transcripts. -/
private abbrev TypedState (m : ℕ) :=
  ForkingReduction.State (List Bool) (BitString m) (List Bool) (List Bool × BitString m × List Bool)

/-- The tag of a typed table position. -/
private def positionTag : Option ℕ → ℕ
  | none => 0
  | some i => i + 1

/-- The native view of a typed transcript. -/
@[expose] def transcriptWords :
    List Bool × BitString m × List Bool → List Bool × List Bool × List Bool
  | (t, c, z) => (t, List.ofFn c, z)

/-- The native view of a typed table entry. -/
private def nativeEntry : List Bool × BitString m × Option ℕ → SchnorrForkEntry
  | (x, c, position) => ⟨x, List.ofFn c, positionTag position⟩

/-- The native view of a typed reduction state that has handled `used` calls. -/
private def nativeState (st : TypedState m) (used : ℕ) : SchnorrForkState :=
  ⟨st.table.map nativeEntry, st.log, st.count, used⟩

/-- The typed reduction's answer to one raw call of a native forger: the call routed as in
`schnorrDecodedForger` and `wordQuery`, then answered by `ForkingReduction.handler`. -/
private noncomputable def typedRawStep (request : Bool × List Bool) :
    StateT (TypedState m) (OracleComp (fun _ : List Bool => BitString m)) (List Bool) :=
  interpret (ForkingReduction.handler (FiatShamir.signer (encPair encBits encBits)))
    (interpret (sumHandler
      (fun msg => encPair encBits encBits <$>
        OracleComp.query (spec := ForgerSpec (List Bool) (List Bool) (List Bool × List Bool)
          (BitString m)) (Sum.inl msg))
      (fun word => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
          (List Bool × List Bool) (BitString m)) (Sum.inr word)))
      (wordQuery (encBitString m) request.1 request.2))

private theorem typedRawStep_false (word : List Bool) :
    typedRawStep (m := m) (false, word) =
      encPair encBits encBits <$>
        ForkingReduction.handler (FiatShamir.signer (encPair encBits encBits)) (Sum.inl word) := by
  simp only [typedRawStep, wordQuery, interpret_query, sumHandler, interpret_map]

private theorem typedRawStep_true (word : List Bool) :
    typedRawStep (m := m) (true, word) =
      List.ofFn <$>
        ForkingReduction.handler (FiatShamir.signer (encPair encBits encBits)) (Sum.inr word) := by
  simp only [typedRawStep, wordQuery, interpret_query, sumHandler, interpret_map]
  rfl

/-- A native table lookup agrees with the typed one. -/
private theorem find?_nativeTable (table : List (List Bool × BitString m × Option ℕ))
    (word : List Bool) :
    (table.map nativeEntry).find? (fun entry => entry.point == word) =
      (@List.lookup _ _ instBEqOfDecidableEq word table).map
        fun (c, position) => nativeEntry (word, c, position) := by
  induction table with
  | nil => rfl
  | cons entry table ih =>
    obtain ⟨x, c, position⟩ := entry
    by_cases hx : x = word
    · subst hx
      simp [nativeEntry]
    · have hx' : @BEq.beq _ instBEqOfDecidableEq word x = false := by
        simpa using Ne.symm hx
      simp [nativeEntry, List.lookup_cons, hx, hx', ih]

/-- **One raw call.** While a transcript and an answer remain, the native step returns the typed
reduction's reply and moves to the native view of its next state, consuming one transcript and at
most one answer. -/
private theorem schnorrForkStep_nativeState (trs : List (List Bool × BitString m × List Bool))
    (answers : List (BitString m)) (default : BitString m) (st : TypedState m) (used : ℕ)
    (hsamples : st.samples = trs.drop used) (hused : used < trs.length)
    (hcount : st.count < answers.length) (request : Bool × List Bool) :
    let run := runWithAnswers default ((typedRawStep request).run st) (answers.drop st.count)
    schnorrForkStep ⟨trs.map transcriptWords, answers.map List.ofFn⟩ request (nativeState st used) =
      (run.1.1, nativeState run.1.2 (used + 1)) ∧ run.1.2.samples = trs.drop (used + 1) ∧
      run.1.2.count = st.count + run.2.length ∧ run.2.length ≤ 1 := by
  obtain ⟨tr, htr⟩ : ∃ tr, trs[used]? = some tr := ⟨trs[used], List.getElem?_eq_getElem hused⟩
  have hhead : st.samples.headD (FiatShamir.signer (Z := List Bool)
      (encPair encBits encBits)).fallback = tr := by
    rw [hsamples, List.headD_eq_head?_getD, List.head?_drop, htr, Option.getD_some]
  have htail : st.samples.tail = trs.drop (used + 1) := by
    rw [hsamples, List.tail_drop]
  obtain ⟨answer, hanswer⟩ : ∃ answer, answers[st.count]? = some answer :=
    ⟨answers[st.count], List.getElem?_eq_getElem hcount⟩
  have hnext : (answers.drop st.count).headD default = answer := by
    rw [List.headD_eq_head?_getD, List.head?_drop, hanswer, Option.getD_some]
  obtain ⟨op, word⟩ := request
  obtain ⟨t, c, z⟩ := tr
  cases op with
  | false =>
    have hget : (trs.map transcriptWords).getD used ([], [], []) = (t, List.ofFn c, z) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, htr]
      rfl
    simp only [typedRawStep_false, StateT.run_map, OracleComp.runWithAnswers_map]
    simp only [ForkingReduction.handler, StateT.run, runWithAnswers_pure, hhead]
    simp only [FiatShamir.signer, ForkingReduction.State.record]
    refine ⟨?_, htail, by simp, by simp⟩
    simp only [schnorrForkStep, Bool.false_eq_true, ite_false, nativeState, hget,
      List.map_cons, nativeEntry, positionTag]
  | true =>
    simp only [typedRawStep_true, StateT.run_map, OracleComp.runWithAnswers_map]
    have hfind := find?_nativeTable st.table word
    cases hlookup : @List.lookup _ _ instBEqOfDecidableEq word st.table with
    | some entry =>
      obtain ⟨c', position⟩ := entry
      have hrun : (ForkingReduction.handler (FiatShamir.signer (Z := List Bool)
          (encPair encBits encBits)) (Sum.inr word)).run st =
          pure (c', { st with samples := st.samples.tail }) := by
        simp only [ForkingReduction.handler, StateT.run, hlookup]
      rw [hrun, runWithAnswers_pure]
      refine ⟨?_, htail, by simp, by simp⟩
      rw [hlookup] at hfind
      simp only [schnorrForkStep, ite_true, nativeState, hfind, Option.map_some, nativeEntry]
    | none =>
      have hrun : (ForkingReduction.handler (FiatShamir.signer (Z := List Bool)
          (encPair encBits encBits)) (Sum.inr word)).run st =
          (fun c => (c, ⟨(word, c, some st.count) :: st.table, st.log, st.count + 1,
            st.samples.tail⟩)) <$> OracleComp.query word := by
        simp only [ForkingReduction.handler, StateT.run, hlookup]
      rw [hrun, runWithAnswers_map_query, hnext]
      refine ⟨?_, htail, by simp, by simp⟩
      rw [hlookup] at hfind
      have hget : (answers.map List.ofFn)[st.count]? = some (List.ofFn answer) := by
        rw [List.getElem?_map, hanswer]
        rfl
      simp only [schnorrForkStep, ite_true, nativeState, hfind, Option.map_none, hget,
        List.map_cons, nativeEntry, positionTag]

/-- The native pass's handler for the forger's raw calls. -/
private abbrev nativeHandler (banks : SchnorrForkBanks) (request : Bool × List Bool) :
    StateT SchnorrForkState ProbComp (List Bool) :=
  fun state => pure (schnorrForkStep banks request state)

/-- **A whole raw program.** A program making at most `k` calls, run natively from the native
view of a typed state, ends in the native view of the typed reduction's final state on the
unused answers, while `k` transcripts and `k` answers remain. -/
private theorem run_nativeHandler (trs : List (List Bool × BitString m × List Bool))
    (answers : List (BitString m)) (default : BitString m) {α : Type}
    {program : OracleComp RawWordSpec α} {k : ℕ} (hk : IsQueryBounded program k)
    (st : TypedState m) (used : ℕ) (hsamples : st.samples = trs.drop used)
    (hused : used + k ≤ trs.length) (hcount : st.count + k ≤ answers.length) :
    let run := runWithAnswers default ((interpret typedRawStep program).run st)
      (answers.drop st.count)
    ∃ used', ProbComp.eval ((interpret (nativeHandler ⟨trs.map transcriptWords,
        answers.map List.ofFn⟩) program).run (nativeState st used)) =
        PMF.pure (run.1.1, nativeState run.1.2 used') ∧
      run.1.2.samples = trs.drop used' ∧ run.1.2.count = st.count + run.2.length ∧
      run.2.length ≤ k := by
  induction hk generalizing st used with
  | pure a n =>
    refine ⟨used, ?_, hsamples, by simp, by simp⟩
    simp [ProbComp.eval_pure]
  | liftBind q cont n hcont ih =>
    obtain ⟨hstep, hsamples₁, hcount₁, hlen₁⟩ := schnorrForkStep_nativeState trs answers default
      st used hsamples (by omega) (by omega) q
    generalize hrun₁ : runWithAnswers default ((typedRawStep q).run st)
      (answers.drop st.count) = run₁ at hstep hsamples₁ hcount₁ hlen₁
    obtain ⟨⟨reply, st₁⟩, queries₁⟩ := run₁
    dsimp only at hstep hsamples₁ hcount₁ hlen₁
    obtain ⟨used', heval, hsamples', hcount', hlen'⟩ := ih reply st₁ (used + 1) hsamples₁
      (by omega) (by omega)
    refine ⟨used', ?_, ?_, ?_, ?_⟩
    · have hq : (nativeHandler ⟨trs.map transcriptWords, answers.map List.ofFn⟩ q).run
          (nativeState st used) = pure (reply, nativeState st₁ (used + 1)) := by
        rw [← hstep]
        rfl
      simp only [interpret_bind, interpret_query, StateT.run_bind, ProbComp.eval_bind, hq,
        ProbComp.eval_pure, PMF.pure_bind]
      rw [heval]
      simp only [runWithAnswers_bind, hrun₁, List.drop_drop, hcount₁]
    · simpa only [interpret_bind, interpret_query, StateT.run_bind, runWithAnswers_bind, hrun₁,
        List.drop_drop, hcount₁, Nat.add_comm] using hsamples'
    · simp only [interpret_bind, interpret_query, StateT.run_bind, runWithAnswers_bind, hrun₁,
        List.drop_drop, List.length_append]
      rw [Nat.add_comm queries₁.length, ← hcount₁, hcount']
      omega
    · simp only [interpret_bind, interpret_query, StateT.run_bind, runWithAnswers_bind, hrun₁,
        List.drop_drop, List.length_append]
      rw [Nat.add_comm queries₁.length, ← hcount₁]
      omega

/-- The raw program of a guarded saved-coin replay. -/
private abbrev rawReplay {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ)
    (input : ℕ × List Bool × List Bool) : OracleComp RawWordSpec (List Bool × List Bool) :=
  savedWordReplay machine (fun op word => OracleComp.query (spec := RawWordSpec) (op, word))
    c e keyC keyD input

/-- The native run interprets the raw replay with `nativeHandler`. -/
private theorem schnorrForkRun_eq {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD n : ℕ)
    (pk tape : List Bool) (banks : SchnorrForkBanks) :
    schnorrForkRun machine c e keyC keyD ⟨n, pk, tape, banks⟩ =
      (interpret (nativeHandler banks) (rawReplay machine c e keyC keyD (n, pk, tape))).run
        ⟨[], [], 0, 0⟩ := by
  simp only [schnorrForkRun, rawReplay]
  rw [savedWordReplay_eq_interpret, interpret_interpret]
  rfl

/-- The typed reduction runs the decoded saved-coin forger through `typedRawStep`. -/
private theorem run_interpret_handler_forge {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD n : ℕ) (d : F.Desc)
    (y : F.Carrier d) (coins : List Bool) (st : TypedState m) :
    (interpret (ForkingReduction.handler (FiatShamir.signer (Z := List Bool)
        (encPair encBits encBits)))
      ((F.schnorrDecodedForger d (savedCoinForger machine (encBitString m)
        c e keyC keyD n)).forge y coins)).run st =
      Prod.map (Prod.map id (Decoder.bits.pair Decoder.bits).decode) id <$>
        (interpret typedRawStep (rawReplay machine c e keyC keyD (n, F.encode d y, coins))).run
          st := by
  simp only [schnorrDecodedForger, savedCoinForger, rawReplay]
  rw [savedWordReplay_eq_interpret, interpret_interpret, interpret_map, interpret_interpret,
    StateT.run_map]
  rfl

end Agreement

/-- The native code of a named fork index: `0` for none and `j + 1` for index `j`. -/
@[expose] def forkIndexCode {q : ℕ} : Option (Fin q) → ℕ
  | none => 0
  | some j => j.val + 1

/-- The code of a named index determines the index. -/
theorem forkIndexCode_injective {q : ℕ} : Function.Injective (forkIndexCode (q := q)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [forkIndexCode, Fin.ext_iff]

/-- The words a native pass returns for one run of the typed forking algorithm: the code of the
named index, the forgery's challenge as a word, and its response. -/
@[expose] def forkRunWords {q m : ℕ} {M T Z Query : Type} :
    Option (Fin q) × ((Option ℕ × ForkingReduction.Outcome M T (BitString m) Z) × List Query) →
      ℕ × List Bool × Z
  | (index, (_, outcome), _) => (forkIndexCode index, List.ofFn outcome.challenge, outcome.response)

/-- The code of a valid named index, as the native final check computes it. -/
private theorem forkIndexCode_validIndex (q count j : ℕ) (won : Bool) :
    forkIndexCode (OracleComp.validIndex q count (if won = true then some j else none)) =
      if (won && decide (0 < j + 1) && decide (j + 1 ≤ q) && decide (j + 1 ≤ count)) = true
      then j + 1 else 0 := by
  cases won
  · simp [OracleComp.validIndex, forkIndexCode]
  · simp only [OracleComp.validIndex, ite_true, Option.bind_some, Bool.true_and]
    by_cases h : j < q ∧ j < count
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      simp only [forkIndexCode]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))]
    · rw [dite_eq_right_of_eq_false (eq_false h)]
      simp only [forkIndexCode]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp; omega))]

section Agreement

variable {m : ℕ}

/-- **The final check.** While an answer remains, the native final check returns the code of the
index that `validIndex` takes from the typed final check, and the forgery's challenge and
response. -/
private theorem schnorrForkFinish_nativeState (d : F.Desc) (hm : 2 ^ m ≤ F.order d)
    (y : F.Carrier d) (answers : List (BitString m)) (default : BitString m)
    (msg sig : List Bool) (st : TypedState m) (used : ℕ) (queries : List (List Bool))
    (hcount : st.count = queries.length) (hlt : st.count < answers.length) :
    let fin := OracleComp.runWithAnswers default
      (ForkingReduction.finish (FiatShamir.check (encPair encBits encBits) (F.schnorrWordSigma d hm)
        y) ((msg, (Decoder.bits.pair Decoder.bits).decode sig), st))
      (answers.drop queries.length)
    F.schnorrForkFinish d (F.encode d y) (answers.map List.ofFn) ((msg, sig), nativeState st used) =
      (forkIndexCode (OracleComp.validIndex answers.length (queries ++ fin.2).length fin.1.1),
        List.ofFn fin.1.2.challenge, fin.1.2.response) := by
  have hcontains (log : List (List Bool)) :
      @List.contains _ instBEqOfDecidableEq log msg = log.contains msg := by
    apply Bool.eq_iff_iff.mpr
    simp
  generalize htz : (Decoder.bits.pair Decoder.bits).decode sig = tz
  obtain ⟨t, z⟩ := tz
  have hfind := find?_nativeTable st.table (encPair encBits encBits (msg, t))
  simp only [schnorrForkFinish, htz, nativeState]
  cases hlookup : @List.lookup _ _ instBEqOfDecidableEq (encPair encBits encBits (msg, t))
      st.table with
  | some entry =>
    obtain ⟨ch, position⟩ := entry
    rw [hlookup] at hfind
    have hrun : ForkingReduction.finish (FiatShamir.check (encPair encBits encBits)
        (F.schnorrWordSigma d hm) y) ((msg, t, z), st) =
        pure (ForkingReduction.verdict (FiatShamir.check (encPair encBits encBits)
          (F.schnorrWordSigma d hm) y) ((msg, t, z), st) ch position) := by
      simp only [ForkingReduction.finish, FiatShamir.check, hlookup]
    simp only [hfind, Option.map_some, Option.elim_some, nativeEntry, hrun,
      OracleComp.runWithAnswers_pure, List.append_nil]
    simp only [ForkingReduction.verdict, FiatShamir.check, schnorrWordSigma, hcontains]
    cases position with
    | none => simp [positionTag, forkIndexCode, OracleComp.validIndex]
    | some j =>
      simp only [positionTag, List.length_map, ← hcount, forkIndexCode_validIndex]
      congr 4
  | none =>
    rw [hlookup] at hfind
    obtain ⟨answer, hanswer⟩ : ∃ answer, answers[st.count]? = some answer :=
      ⟨answers[st.count], List.getElem?_eq_getElem hlt⟩
    have hnext : (answers.drop queries.length).headD default = answer := by
      rw [← hcount, List.headD_eq_head?_getD, List.head?_drop, hanswer, Option.getD_some]
    have hget : (answers.map List.ofFn).getD st.count [] = List.ofFn answer := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hanswer]
      rfl
    have hrun : ForkingReduction.finish (FiatShamir.check (encPair encBits encBits)
        (F.schnorrWordSigma d hm) y) ((msg, t, z), st) =
        (fun c => ForkingReduction.verdict (FiatShamir.check (encPair encBits encBits)
          (F.schnorrWordSigma d hm) y) ((msg, t, z), st) c (some st.count)) <$>
          OracleComp.query (encPair encBits encBits (msg, t)) := by
      simp only [ForkingReduction.finish, FiatShamir.check, hlookup]
    simp only [hfind, Option.map_none, Option.elim_none, hrun, OracleComp.runWithAnswers_map_query,
      hnext, hget]
    simp only [ForkingReduction.verdict, FiatShamir.check, schnorrWordSigma, hcontains,
      List.length_map, List.length_append, List.length_singleton, ← hcount,
      forkIndexCode_validIndex]

end Agreement

/-- **One native pass agrees with the typed forking program.** Let `B` be the saved-coin budget.
On a canonical public key, at least `B` transcripts and `B + 1` answers, the native pass returns
exactly `forkRunWords` of `forkingAlgorithm` for the existing `FiatShamir.forkingProgram` of the
word Schnorr scheme and the decoded saved-coin forger: the code of the named index and the
forgery's challenge and response. The default answer of `forkingAlgorithm` is never used. -/
theorem eval_schnorrForkPass {m k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD n : ℕ)
    (d : F.Desc) (hm : 2 ^ m ≤ F.order d) (y : F.Carrier d) (coins : List Bool)
    (trs : List (List Bool × BitString m × List Bool))
    (htrs : savedCoinBudget c e keyC keyD n ≤ trs.length)
    (answers : Fin (savedCoinBudget c e keyC keyD n + 1) → BitString m) (default : BitString m) :
    ProbComp.eval (F.schnorrForkPass machine c e keyC keyD d
        ⟨n, F.encode d y, coins, ⟨trs.map transcriptWords, (List.ofFn answers).map List.ofFn⟩⟩) =
      PMF.pure (forkRunWords (OracleComp.forkingAlgorithm default
        (savedCoinBudget c e keyC keyD n + 1)
        (FiatShamir.forkingProgram (encPair encBits encBits) (F.schnorrWordSigma d hm)
          (F.schnorrDecodedForger d (savedCoinForger machine (encBitString m)
            c e keyC keyD n))) (y, coins, trs) answers)) := by
  have hR := isQueryBounded_savedWordReplay machine
    (fun op word => OracleComp.query (spec := RawWordSpec) (op, word))
    (fun _ _ => OracleComp.IsCostBounded.query _) c e keyC keyD n (F.encode d y) coins
  let st₀ : TypedState m := ⟨[], [], 0, trs⟩
  obtain ⟨used, heval, -, hcount, hlen⟩ := run_nativeHandler trs (List.ofFn answers) default hR
    st₀ 0 (by simp [st₀]) (by simpa using htrs) (by simp [st₀])
  generalize hrun : OracleComp.runWithAnswers default
    ((OracleComp.interpret typedRawStep
      (rawReplay machine c e keyC keyD (n, F.encode d y, coins))).run st₀)
    ((List.ofFn answers).drop st₀.count) = run at heval hcount hlen
  obtain ⟨⟨⟨msg, sig⟩, st⟩, queries⟩ := run
  dsimp only at heval hcount hlen
  have hnative : ProbComp.eval (F.schnorrForkPass machine c e keyC keyD d
      ⟨n, F.encode d y, coins, ⟨trs.map transcriptWords, (List.ofFn answers).map List.ofFn⟩⟩) =
      PMF.pure (F.schnorrForkFinish d (F.encode d y) ((List.ofFn answers).map List.ofFn)
        ((msg, sig), nativeState st used)) := by
    simp only [schnorrForkPass, ProbComp.eval_map, schnorrForkRun_eq]
    rw [show (⟨[], [], 0, 0⟩ : SchnorrForkState) = nativeState st₀ 0 from rfl, heval,
      PMF.pure_map]
  rw [hnative]
  simp only [OracleComp.forkingAlgorithm, FiatShamir.forkingProgram, ForkingReduction.program,
    OracleComp.runWithAnswers_bind, run_interpret_handler_forge, OracleComp.runWithAnswers_map]
  simp only [st₀, List.drop_zero] at hrun
  rw [hrun]
  simp only [st₀, Nat.zero_add] at hcount
  have hfinish := schnorrForkFinish_nativeState F d hm y (List.ofFn answers) default msg sig st
    used queries hcount (by rw [List.length_ofFn]; omega)
  rw [List.length_ofFn] at hfinish
  rw [hfinish]
  simp only [Prod.map, id, OracleComp.forkNamedPosition, OracleComp.runWithAnswersOutput,
    forkRunWords]


end Cslib.Crypto.PrimeOrderGroupFamily
