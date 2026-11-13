/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.OT.CorrelatedBound.Information
public import CslibFrontier.Crypto.Protocols.MPC.Basic
public import CslibFrontier.Crypto.Protocols.MPC.BatchOT
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-!
# Semi-honest two-party protocols over correlated randomness with a public transcript

This module specializes the synchronous two-party plain-channel protocol model
`Cslib.Crypto.Protocols.MPC.Protocol` (`m = 2`, `spec = noOracleSpec`) to executions over a
correlated source `source : PMF (A × B)` with a public communication transcript, and also connects
adaptive-speaker binary communication trees `Cslib.Communication.Protocol` and
`Cslib.Communication.PrivateCoin` over `(A, B)`.

Every inter-party message round (`sender ≠ receiver`) contributes to the public transcript
`PublicTranscript sc`, which both parties reconstruct deterministically from their views
(`transcriptOfView`). For any `Protocol 2 noOracleSpec sc`, conditioning on the public transcript
never increases the conditional mutual information between the two parties' initial correlated-plus-
coin states (`condMutualInfo_transcript_le_mutualInfo`). Combined with
`natCast_le_mutualInfo_of_rot`,
any protocol realizing `k` independent random OTs (`rotFunctionality k`) or `k` chosen-input OTs
(`batchOTFunctionality k Bool`) with perfect semi-honest privacy over `source` requires
`k ≤ I(A; B)` (`rot_le_mutualInfo`, `chosenOT_le_mutualInfo`, `commProtocol_rot_le_mutualInfo`,
`privateCoin_rot_le_mutualInfo`).

Privacy over a correlated source is the shared MPC notion
`Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivateProperWithSetup`, with the source dealt by the
trusted setup `dealSource source` (or `dealSourceWithInput source` next to external inputs) and
simulators `Cslib.Crypto.Protocols.MPC.SetupSimulator` that never see the dealt share.

## Main definitions

* `Cslib.Crypto.Protocols.OT.PublicMsg`, `Cslib.Crypto.Protocols.OT.PublicTranscript`: public
  communication transcript type of a two-party plain-channel schedule.
* `Cslib.Crypto.Protocols.OT.stepsTranscriptOfView`, `Cslib.Crypto.Protocols.OT.transcriptOfView`:
  deterministic reconstruction of the public transcript from either party's `PartyView`.
* `Cslib.Crypto.Protocols.OT.realWithInputDist`, `Cslib.Crypto.Protocols.OT.realCorrelated`: real
  executions over a joint input distribution and over a correlated source.
* `Cslib.Crypto.Protocols.OT.dealSource`, `Cslib.Crypto.Protocols.OT.dealSourceWithInput`: trusted
  setups dealing a correlated source to the two parties, alone or next to their external inputs.
* `Cslib.Crypto.Protocols.OT.idealROT`, `Cslib.Crypto.Protocols.OT.rotFunctionality`: ideal
  distribution and input-free functionality of `k` independent random 1-out-of-2 bit oblivious
  transfers.

## Main results

* `Cslib.Crypto.Protocols.OT.transcriptOfView_zero_eq_one`: both parties reconstruct the same public
  transcript on every supported execution.
* `Cslib.Crypto.Protocols.OT.dealSource_bind_realJoint`: the real side of privacy over
  `dealSource source` is `realCorrelated` restricted to the coalition.
* `Cslib.Crypto.Protocols.OT.condMutualInfo_transcript_le_mutualInfo_input`,
  `Cslib.Crypto.Protocols.OT.condMutualInfo_transcript_le_mutualInfo`: public communication over a
  correlated source satisfies `I((In₀, R₀); (In₁, R₁) | T) ≤ I(In₀; In₁)`.
* `Cslib.Crypto.Protocols.OT.rot_le_mutualInfo`: any perfectly semi-honest private `k`-ROT protocol
  over `source` satisfies `(k : ℝ) ≤ I(A; B)`.
* `Cslib.Crypto.Protocols.OT.chosenOT_le_mutualInfo`: any perfectly semi-honest private chosen-input
  `k`-OT protocol (`batchOTFunctionality k Bool`) over `source` satisfies `(k : ℝ) ≤ I(A; B)`.
* `Cslib.Crypto.Protocols.OT.commProtocol_rot_le_mutualInfo`,
  `Cslib.Crypto.Protocols.OT.privateCoin_rot_le_mutualInfo`: `(k : ℝ) ≤ I(A; B)` for adaptive-
  speaker binary communication trees `Cslib.Communication.Protocol` and
  `Cslib.Communication.PrivateCoin`.

## References

* [R. Ahlswede and I. Csiszár, *Common Randomness in Information Theory and Cryptography.
  Part I: Secret Sharing*][AhlswedeCsiszar1993] (bibliographic metadata verified; primary full text
  uninspected; locators unverified).
* [A. C. A. Nascimento and A. Winter, *On the Oblivious-Transfer Capacity of Noisy
  Resources*][NascimentoWinter2008] (bibliographic metadata verified; primary full text uninspected;
  locators unverified).
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004]
  (semi-honest simulation background; primary full text uninspected; locators unverified).
-/

public section

namespace Cslib.Crypto.Protocols.OT

open Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Protocols.MPC Cslib.Communication
open scoped ENNReal

/-- Dependent pair constructor on `Fin 2`. -/
@[expose] def pairVec {F : Fin 2 → Type} (x0 : F 0) (x1 : F 1) : (i : Fin 2) → F i
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1

/-- Restrict a constant value at party `0` to the singleton coalition `{0}`. -/
private def restrictZero {F : Fin 2 → Type} (x0 : F 0) :
    (i : ({0} : Finset (Fin 2))) → F i.1 :=
  fun ⟨i, hi⟩ => Finset.mem_singleton.mp hi ▸ x0

/-- Restrict a constant value at party `1` to the singleton coalition `{1}`. -/
private def restrictOne {F : Fin 2 → Type} (x1 : F 1) :
    (i : ({1} : Finset (Fin 2))) → F i.1 :=
  fun ⟨i, hi⟩ => Finset.mem_singleton.mp hi ▸ x1

private theorem restrictZero_pairVec {F : Fin 2 → Type} (x0 : F 0) (x1 : F 1) :
    ({0} : Finset (Fin 2)).restrict (pairVec x0 x1) = restrictZero x0 := by
  funext ⟨i, hi⟩
  obtain rfl := Finset.mem_singleton.mp hi
  rfl

private theorem restrictOne_pairVec {F : Fin 2 → Type} (x0 : F 0) (x1 : F 1) :
    ({1} : Finset (Fin 2)).restrict (pairVec x0 x1) = restrictOne x1 := by
  funext ⟨i, hi⟩
  obtain rfl := Finset.mem_singleton.mp hi
  rfl

private lemma finite_finCases {A B : Type} [Finite A] [Finite B] (i : Fin 2) :
    Finite (Fin.cases A (fun _ => B) i) := by
  fin_cases i
  · exact ‹Finite A›
  · exact ‹Finite B›

/-! ### Public transcripts of two-party plain-channel schedules -/

/-- Public message payload of a round in a two-party plain-channel schedule: inter-party messages
(`sender ≠ receiver`) are public, while self-messages carry no public payload. -/
@[expose, reducible] def PublicMsg : Round 2 noOracleSpec → Type
  | .message sender receiver Msg => (sender ≠ receiver) → Msg
  | .oracle (op := op) _ => op.elim

/-- Public communication transcript along a two-party plain-channel schedule. -/
@[expose, reducible] def PublicTranscript : Schedule 2 noOracleSpec → Type
  | [] => Unit
  | r :: sc => PublicMsg r × PublicTranscript sc

/-- Reconstruct the public transcript from party `i`'s current local state and received messages. -/
@[expose] noncomputable def stepsTranscriptOfView {State Out : Fin 2 → Type}
    {sc : Schedule 2 noOracleSpec}
    (steps : Steps State Out sc) (i : Fin 2) (st_i : State i)
    (recv_i : sc.Received i) : PublicTranscript sc :=
  match steps, recv_i with
  | .done _, () => ()
  | .message (sender := sender) (receiver := receiver) send next, (r_head, r_tail) =>
      let msgHead : (sender ≠ receiver) → _ := fun hne =>
        if hi : i = sender then
          send (hi ▸ st_i)
        else
          r_head (by omega)
      (msgHead, stepsTranscriptOfView next i (st_i, r_head) r_tail)
  | .oracle (op := op) _ _, _ => op.elim

/-- Reconstruct the public transcript of `proto` from party `i`'s `PartyView`. -/
@[expose] noncomputable def transcriptOfView {sc : Schedule 2 noOracleSpec}
    {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out) (i : Fin 2)
    (v : PartyView In Coins sc i) : PublicTranscript sc :=
  stepsTranscriptOfView proto.steps i (v.input, v.coins) v.received

/-- Deterministic execution of `steps` in `noOracleWorld`: returns the tuple of received transcripts
for each party. -/
private noncomputable def stepsExecPure {State Out : Fin 2 → Type} {sc : Schedule 2 noOracleSpec}
    (steps : Steps State Out sc) (st : (i : Fin 2) → State i) : (i : Fin 2) → sc.Received i :=
  match steps with
  | .done _ => fun _ => ()
  | .message (sender := sender) send next =>
      let r_head : (i : Fin 2) → _ := Round.deliverMessage (send (st sender))
      let r_tail := stepsExecPure next (fun i => (st i, r_head i))
      fun i => (r_head i, r_tail i)
  | .oracle (op := op) _ _ => op.elim

/-- Deterministic public transcript produced by `steps` from initial states `st`. -/
private noncomputable def stepsTranscriptPure {State Out : Fin 2 → Type}
    {sc : Schedule 2 noOracleSpec} (steps : Steps State Out sc)
    (st : (i : Fin 2) → State i) : PublicTranscript sc :=
  match steps with
  | .done _ => ()
  | .message (sender := sender) send next =>
      let r_head : (i : Fin 2) → _ := Round.deliverMessage (send (st sender))
      (fun _ => send (st sender), stepsTranscriptPure next (fun i => (st i, r_head i)))
  | .oracle (op := op) _ _ => op.elim

private theorem stepsEvalWith_eq_pure :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      (steps : Steps State Out sc) (st : (i : Fin 2) → State i),
      steps.evalWith noOracleWorld st = PMF.pure (stepsExecPure steps st)
  | [], _, _, .done _, _ => rfl
  | _ :: _, _, _, .message send next, st => by
      rw [Steps.evalWith_message, stepsEvalWith_eq_pure next _, PMF.pure_map]
      rfl
  | _ :: _, _, _, .oracle (op := op) _ _, _ => op.elim

private theorem stepsTranscriptOfView_execPure :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      (steps : Steps State Out sc) (st : (i : Fin 2) → State i) (i : Fin 2),
      stepsTranscriptOfView steps i (st i) (stepsExecPure steps st i) =
        stepsTranscriptPure steps st
  | [], _, _, .done _, _, _ => rfl
  | _ :: _, _, _, .message (sender := sender) (receiver := receiver) send next, st, i => by
      simp only [stepsExecPure, stepsTranscriptOfView, stepsTranscriptPure]
      refine Prod.ext (funext fun hne => ?_) ?_
      · by_cases hi : i = sender
        · subst hi
          simp only [dite_true]
        · have hrev : i = receiver := by omega
          subst hrev
          simp only [hi, dite_false, Round.deliverMessage]
      · exact stepsTranscriptOfView_execPure next
          (fun j => (st j, Round.deliverMessage (send (st sender)) j)) i
  | _ :: _, _, _, .oracle (op := op) _ _, _, _ => op.elim

private theorem stepsTranscriptOfView_eq_transcriptPure_of_mem_support
    {State Out : Fin 2 → Type} {sc : Schedule 2 noOracleSpec}
    (steps : Steps State Out sc) {st : (i : Fin 2) → State i}
    {recv : (i : Fin 2) → sc.Received i}
    (h : recv ∈ (steps.evalWith noOracleWorld st).support) (i : Fin 2) :
    stepsTranscriptOfView steps i (st i) (recv i) = stepsTranscriptPure steps st := by
  rw [stepsEvalWith_eq_pure, PMF.mem_support_pure_iff] at h
  subst h
  exact stepsTranscriptOfView_execPure steps st i

/-- In every supported execution of a two-party plain-channel protocol, Alice (`0`) and Bob (`1`)
reconstruct the exact same public transcript from their views. -/
theorem transcriptOfView_zero_eq_one {sc : Schedule 2 noOracleSpec} {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out) {x : (i : Fin 2) → In i}
    {res : ((i : Fin 2) → PartyView In Coins sc i) × ((i : Fin 2) → Out i)}
    (h : res ∈ (proto.evalWith noOracleWorld x).support) :
    transcriptOfView proto 0 (res.1 0) = transcriptOfView proto 1 (res.1 1) := by
  rw [Protocol.evalWith_eq, PMF.mem_support_bind_iff] at h
  obtain ⟨r, _, hrecv⟩ := h
  rw [PMF.mem_support_map_iff] at hrecv
  obtain ⟨recv, hrecv_supp, rfl⟩ := hrecv
  dsimp only [transcriptOfView]
  exact (stepsTranscriptOfView_eq_transcriptPure_of_mem_support proto.steps hrecv_supp 0).trans
    (stepsTranscriptOfView_eq_transcriptPure_of_mem_support proto.steps hrecv_supp 1).symm

/-- Given `st_i` and the public transcript `T`, party `i` deterministically reconstructs its
received messages `sc.Received i` along `steps`. -/
private noncomputable def stepsReceivedOfTranscript {State Out : Fin 2 → Type}
    {sc : Schedule 2 noOracleSpec} (steps : Steps State Out sc) (i : Fin 2) (st_i : State i)
    (T : PublicTranscript sc) : sc.Received i :=
  match steps, T with
  | .done _, () => ()
  | .message (sender := sender) (receiver := receiver) send next, (msgHead, msgTail) =>
      let r_head : (Round.message (spec := noOracleSpec) sender receiver _).Received i := fun hr =>
        if hs : sender = receiver then
          have hi : i = sender := hr.trans hs.symm
          send (hi ▸ st_i)
        else
          msgHead hs
      (r_head, stepsReceivedOfTranscript next i (st_i, r_head) msgTail)
  | .oracle (op := op) _ _, _ => op.elim

private theorem stepsReceivedOfTranscript_transcriptPure :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      (steps : Steps State Out sc) (st : (i : Fin 2) → State i) (i : Fin 2),
      stepsReceivedOfTranscript steps i (st i) (stepsTranscriptPure steps st) =
        stepsExecPure steps st i
  | [], _, _, .done _, _, _ => rfl
  | _ :: _, _, _, .message (sender := sender) (receiver := receiver) send next, st, i => by
      simp only [stepsReceivedOfTranscript, stepsTranscriptPure, stepsExecPure]
      have hhead :
          (fun hr : i = receiver =>
            if hs : sender = receiver then send ((hr.trans hs.symm) ▸ st i)
            else send (st sender)) =
            Round.deliverMessage (spec := noOracleSpec) (sender := sender) (receiver := receiver)
              (send (st sender)) i := by
        refine Round.received_message_ext fun hr => ?_
        by_cases hs : sender = receiver
        · have hi : i = sender := hr.trans hs.symm
          subst hi
          simp only [hs, dite_true, Round.deliverMessage]
        · simp only [hs, dite_false, Round.deliverMessage]
      rw [hhead]
      refine Prod.ext rfl ?_
      exact stepsReceivedOfTranscript_transcriptPure next
        (fun j => (st j, Round.deliverMessage (send (st sender)) j)) i
  | _ :: _, _, _, .oracle (op := op) _ _, _, _ => op.elim

/-- On every supported execution, each party's view and output are determined by its input, coins,
and the public transcript. -/
private theorem partyView_eq_of_mem_support_evalWith
    {sc : Schedule 2 noOracleSpec} {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out) {x : (i : Fin 2) → In i}
    {views : (i : Fin 2) → PartyView In Coins sc i} {out : (i : Fin 2) → Out i}
    (hev : (views, out) ∈ (proto.evalWith noOracleWorld x).support) (i : Fin 2) :
    views i = ⟨(views i).input, (views i).coins,
        stepsReceivedOfTranscript proto.steps i ((views i).input, (views i).coins)
          (transcriptOfView proto 0 (views 0))⟩ ∧
      out i = proto.outputOfView i (views i) := by
  have h01 := transcriptOfView_zero_eq_one proto hev
  have hout := Protocol.snd_eq_outputOfView_of_mem_support_evalWith hev
  rw [Protocol.evalWith_eq, PMF.mem_support_bind_iff] at hev
  obtain ⟨r, _, hrecv⟩ := hev
  rw [PMF.mem_support_map_iff] at hrecv
  obtain ⟨recv, hrecv_supp, hres⟩ := hrecv
  have hrecv_pure : recv = stepsExecPure proto.steps (fun j => (x j, r j)) := by
    rw [stepsEvalWith_eq_pure, PMF.mem_support_pure_iff] at hrecv_supp
    exact hrecv_supp
  have htr : transcriptOfView proto 0 (views 0) = transcriptOfView proto i (views i) := by
    fin_cases i
    · rfl
    · exact h01
  have hv := congrFun (congrArg Prod.fst hres.symm) i
  dsimp only at hv
  refine ⟨?_, congrFun hout i⟩
  rw [htr]
  dsimp only [transcriptOfView]
  rw [hv]
  refine PartyView.ext rfl rfl ?_
  subst hrecv_pure
  have h1 := stepsTranscriptOfView_execPure proto.steps (fun j => (x j, r j)) i
  rw [h1]
  exact stepsReceivedOfTranscript_transcriptPure proto.steps (fun j => (x j, r j)) i |>.symm

/-- Auxiliary round-by-round induction: conditioning on a public transcript never increases
conditional mutual information between Alice's and Bob's initial correlated-plus-coin states. -/
private theorem exists_state_next_of_party {Ω τ₀ χ : Type*} {State : Fin 2 → Type}
    {sender receiver : Fin 2} {Msg : Type} (send : State sender → Msg)
    (ν : PMF Ω) (T0 : Ω → τ₀) (X : Ω → χ) (st : Ω → (j : Fin 2) → State j)
    (i : Fin 2) (f : χ × τ₀ → State i) (hf : ∀ ω ∈ ν.support, st ω i = f (X ω, T0 ω)) :
    let msgPub : Ω → PublicMsg (Round.message sender receiver Msg) := fun ω _ => send (st ω sender)
    let r_head : Ω → (j : Fin 2) →
        (Round.message (spec := noOracleSpec) sender receiver Msg).Received j :=
      fun ω => Round.deliverMessage (send (st ω sender))
    ∃ f' : χ × (τ₀ × PublicMsg (Round.message sender receiver Msg)) →
        State i × (Round.message (spec := noOracleSpec) sender receiver Msg).Received i,
      ∀ ω ∈ ν.support, (st ω i, r_head ω i) = f' (X ω, (T0 ω, msgPub ω)) := by
  intro msgPub r_head
  by_cases hs : sender = i
  · subst hs
    refine ⟨fun p => (f (p.1, p.2.1), Round.deliverMessage (send (f (p.1, p.2.1))) sender),
      fun ω hω => ?_⟩
    refine Prod.ext (hf ω hω) ?_
    change Round.deliverMessage (send (st ω sender)) sender =
      Round.deliverMessage (send (f (X ω, T0 ω))) sender
    rw [hf ω hω]
  · by_cases hr : receiver = i
    · subst hr
      refine ⟨fun p => (f (p.1, p.2.1), fun _ => p.2.2 hs), fun ω hω => ?_⟩
      refine Prod.ext (hf ω hω) (Round.received_message_ext fun _ => rfl)
    · refine ⟨fun p => (f (p.1, p.2.1), fun h => absurd h.symm hr), fun ω hω => ?_⟩
      refine Prod.ext (hf ω hω) (Round.received_message_eq_of_ne (Ne.symm hr) _ _)

/-- Adding a plain-channel communication schedule cannot increase conditional mutual information
between the parties' local states. -/
private theorem condMutualInfo_steps_transcriptPure_le
    {Ω α₀ β₀ τ₀ : Type*} [Finite α₀] [Finite β₀] [Finite τ₀]
    (ν : PMF Ω) (A0 : Ω → α₀) (B0 : Ω → β₀) (T0 : Ω → τ₀) :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      [Finite (PublicTranscript sc)]
      (steps : Steps State Out sc) (st0 : Ω → State 0) (st1 : Ω → State 1),
      (∃ f0 : α₀ × τ₀ → State 0, ∀ ω ∈ ν.support, st0 ω = f0 (A0 ω, T0 ω)) →
      (∃ f1 : β₀ × τ₀ → State 1, ∀ ω ∈ ν.support, st1 ω = f1 (B0 ω, T0 ω)) →
      condMutualInfo (ν.map fun ω =>
        ((T0 ω, stepsTranscriptPure steps (fun i => pairVec (st0 ω) (st1 ω) i)),
          A0 ω, B0 ω)) ≤
        condMutualInfo (ν.map fun ω => (T0 ω, A0 ω, B0 ω))
  | [], _, _, _, .done _, _, _, _, _ =>
      (condMutualInfo_map_congr_cond ν A0 B0 (e := (·, ()))
        (fun _ _ h => congrArg Prod.fst h) (fun _ _ => rfl)).le
  | _ :: sc, State, Out, _,
      .message (sender := sender) (receiver := receiver) (Msg := Msg) send next,
      st0, st1, ⟨f0, hf0⟩, ⟨f1, hf1⟩ => by
      obtain ⟨ω₀, _⟩ := ν.support_nonempty
      let msgPub : Ω → PublicMsg (Round.message sender receiver Msg) :=
        fun ω _ => send (pairVec (st0 ω) (st1 ω) sender)
      let r_head : Ω → (i : Fin 2) →
          (Round.message (spec := noOracleSpec) sender receiver Msg).Received i :=
        fun ω => Round.deliverMessage (send (pairVec (st0 ω) (st1 ω) sender))
      let tTail₀ : PublicTranscript sc :=
        stepsTranscriptPure next (fun i => (pairVec (st0 ω₀) (st1 ω₀) i, r_head ω₀ i))
      have : Finite (PublicMsg (Round.message sender receiver Msg)) :=
        Finite.of_injective (fun m => (m, tTail₀)) (fun _ _ h => congrArg Prod.fst h)
      have : Finite (PublicTranscript sc) :=
        Finite.of_injective (fun t => (msgPub ω₀, t)) (fun _ _ h => congrArg Prod.snd h)
      -- Step A: `I(A0; B0 | (T0, msgPub)) ≤ I(A0; B0 | T0)`.
      have hStep : condMutualInfo (ν.map fun ω => ((T0 ω, msgPub ω), A0 ω, B0 ω)) ≤
          condMutualInfo (ν.map fun ω => (T0 ω, A0 ω, B0 ω)) := by
        by_cases hSR : sender = receiver
        · have hsub : ∀ ω : Ω, msgPub ω = msgPub ω₀ := fun ω => funext fun h => (h hSR).elim
          exact (condMutualInfo_map_congr_cond ν (C := T0) (C' := fun ω => (T0 ω, msgPub ω))
            A0 B0 (e := (·, msgPub ω₀)) (fun _ _ h => congrArg Prod.fst h)
            (fun ω _ => Prod.ext rfl (hsub ω))).le
        · fin_cases sender
          · refine condMutualInfo_map_pair_fst_le_of_eq_zero ν T0 msgPub A0 B0 ?_
            rw [condMutualInfo_map_swap]
            refine condMutualInfo_map_eq_zero_of_determined ν (fun ω => (T0 ω, A0 ω)) B0 msgPub
              (fun ta _ => send (f0 (ta.2, ta.1))) fun ω hω => ?_
            funext _
            exact congrArg send (hf0 ω hω)
          · refine condMutualInfo_map_pair_snd_le_of_eq_zero ν T0 msgPub A0 B0 ?_
            rw [condMutualInfo_map_swap]
            refine condMutualInfo_map_eq_zero_of_determined ν (fun ω => (T0 ω, B0 ω)) A0 msgPub
              (fun tb _ => send (f1 (tb.2, tb.1))) fun ω hω => ?_
            funext _
            exact congrArg send (hf1 ω hω)
      -- Step B: updated states remain functions of `(A0, (T0, msgPub))` and `(B0, (T0, msgPub))`.
      have hst0' := exists_state_next_of_party (receiver := receiver) send ν T0 A0
        (fun ω => pairVec (st0 ω) (st1 ω)) 0 f0 hf0
      have hst1' := exists_state_next_of_party (receiver := receiver) send ν T0 B0
        (fun ω => pairVec (st0 ω) (st1 ω)) 1 f1 hf1
      have hIH := condMutualInfo_steps_transcriptPure_le ν A0 B0 (fun ω => (T0 ω, msgPub ω))
        next (fun ω => (st0 ω, r_head ω 0)) (fun ω => (st1 ω, r_head ω 1)) hst0' hst1'
      -- Step C: re-associate `((T0, msgPub), T_tail)` with `(T0, (msgPub, T_tail))`.
      have hFinStep : ∀ ω : Ω,
          (fun i : Fin 2 => (pairVec (st0 ω) (st1 ω) i, r_head ω i)) =
            fun i => @pairVec (fun j => State j ×
              (Round.message (spec := noOracleSpec) sender receiver Msg).Received j)
              (st0 ω, r_head ω 0) (st1 ω, r_head ω 1) i := by
        intro ω
        funext i
        fin_cases i <;> rfl
      have hTrEq : ∀ ω : Ω,
          stepsTranscriptPure (.message send next) (fun i => pairVec (st0 ω) (st1 ω) i) =
            (msgPub ω, stepsTranscriptPure next
              (fun i => @pairVec (fun j => State j ×
                (Round.message (spec := noOracleSpec) sender receiver Msg).Received j)
                (st0 ω, r_head ω 0) (st1 ω, r_head ω 1) i)) := by
        intro ω
        dsimp only [stepsTranscriptPure, msgPub, r_head]
        rw [hFinStep ω]
      have hAssoc := condMutualInfo_map_congr_cond ν A0 B0
        (C := fun ω => (T0 ω, stepsTranscriptPure (.message send next)
          (fun i => pairVec (st0 ω) (st1 ω) i)))
        (C' := fun ω => ((T0 ω, msgPub ω), stepsTranscriptPure next
          (fun i => @pairVec (fun j => State j ×
            (Round.message (spec := noOracleSpec) sender receiver Msg).Received j)
            (st0 ω, r_head ω 0) (st1 ω, r_head ω 1) i)))
        (e := (Equiv.prodAssoc _ _ _).symm) (Equiv.prodAssoc _ _ _).symm.injective
        (fun ω _ => by rw [hTrEq ω]; rfl)
      exact hAssoc.symm.trans_le (hIH.trans hStep)
  | _ :: _, _, _, _, .oracle (op := op) _ _, _, _, _, _ => op.elim

/-! ### Correlated-source 2PC semantics and privacy -/

section Correlated2PC

variable {A B : Type} {sc : Schedule 2 noOracleSpec} {Coins Out : Fin 2 → Type}

/-- Real execution of a two-party plain-channel protocol over an arbitrary joint input distribution
`inputDist : PMF (In 0 × In 1)`. -/
@[expose] noncomputable def realWithInputDist {In : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (inputDist : PMF (In 0 × In 1)) :
    PMF (((i : Fin 2) → PartyView In Coins sc i) × ((i : Fin 2) → Out i)) :=
  inputDist.bind fun xy => proto.evalWith noOracleWorld (pairVec xy.1 xy.2)

private theorem bind_evalWith_map_input {Ω α β : Type*} {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (μ : PMF Ω) (f : Ω → (i : Fin 2) → In i) (g0 : In 0 → α) (g1 : In 1 → β) :
    ((μ.bind fun ω => proto.evalWith noOracleWorld (f ω)).map fun (views, _) =>
      (g0 (views 0).input, g1 (views 1).input)) = μ.map fun ω => (g0 (f ω 0), g1 (f ω 1)) := by
  simp only [Protocol.evalWith_eq, stepsEvalWith_eq_pure, PMF.pure_map, PMF.map_bind]
  calc μ.bind (fun ω =>
        (ProbComp.eval (OracleComp.pi proto.sampleCoins)).bind fun _ =>
          PMF.pure (g0 (f ω 0), g1 (f ω 1)))
      = μ.bind (fun ω => PMF.pure (g0 (f ω 0), g1 (f ω 1))) := by
        congr 1 with ω : 1
        exact PMF.bind_const _ _
    _ = μ.map fun ω => (g0 (f ω 0), g1 (f ω 1)) := PMF.bind_pure_comp _ _

/-- Real execution of a two-party plain-channel protocol over correlated source
`source : PMF (A × B)`. -/
@[expose] noncomputable def realCorrelated
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins Out)
    (source : PMF (A × B)) :
    PMF (((i : Fin 2) → PartyView (Fin.cases A (fun _ => B)) Coins sc i) × ((i : Fin 2) → Out i)) :=
  source.bind fun ab => proto.evalWith noOracleWorld (Fin.cases ab.1 (fun _ => ab.2))

/-- The trusted setup dealing correlated source `source : PMF (A × B)` to the two parties: party `0`
receives the `A` share and party `1` the `B` share. Privacy over `source` is
`PerfectSemiHonestPrivateProperWithSetup` with setup `fun _ => dealSource source`. -/
noncomputable def dealSource (source : PMF (A × B)) :
    PMF ((i : Fin 2) → Fin.cases A (fun _ => B) i) :=
  source.map fun ab => Fin.cases ab.1 (fun _ => ab.2)

/-- The real side of privacy over `dealSource source` is the correlated execution restricted to
the coalition. -/
theorem dealSource_bind_realJoint
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins Out)
    (source : PMF (A × B)) (I : Finset (Fin 2)) :
    (dealSource source).bind (proto.realJoint noOracleWorld I) =
      (realCorrelated proto source).map (Prod.map I.restrict id) := by
  rw [Protocol.bind_realJoint, dealSource, PMF.bind_map]
  rfl

/-- The ideal distribution of `k` independent random 1-out-of-2 bit oblivious transfers:
party `0` (sender) receives `k` pairs of independent fair bits, and party `1` (receiver) receives
`k` independent fair choice bits paired with the selected sender bits. -/
@[expose] noncomputable def idealROT (k : ℕ) : PMF ((i : Fin 2) → (Fin k → Bool × Bool)) :=
  (PMF.uniformOfFintype ((Fin k → Bool × Bool) × (Fin k → Bool))).map
    fun (senderBits, choices) =>
      Fin.cases senderBits (fun _ j => (choices j, otSelect (senderBits j) (choices j)))

/-- The input-free functionality of `k` independent random 1-out-of-2 bit oblivious transfers: it
samples uniform sender pairs and receiver choices and outputs the sender pairs to party `0` and
the choices with the selected bits to party `1`. -/
noncomputable def rotFunctionality (k : ℕ) :
    Functionality 2 (fun _ => Unit) (fun _ => Fin k → Bool × Bool) :=
  fun _ => (fun (senderBits, choices) =>
      (Fin.cases senderBits (fun _ j => (choices j, otSelect (senderBits j) (choices j))) :
        (i : Fin 2) → Fin k → Bool × Bool)) <$>
    ProbComp.uniform ((Fin k → Bool × Bool) × (Fin k → Bool))

/-- `rotFunctionality k` samples `idealROT k`. -/
@[simp] theorem eval_rotFunctionality (k : ℕ) (x : (i : Fin 2) → Unit) :
    ProbComp.eval (rotFunctionality k x) = idealROT k := by
  rw [rotFunctionality, ProbComp.eval_map, ProbComp.eval_uniform]
  rfl

/-- The ideal joint distribution of `rotFunctionality k`: sample `idealROT k`, then the simulated
views from the coalition's outputs. -/
private theorem eval_idealJoint_rotFunctionality {k : ℕ} {I : Finset (Fin 2)}
    (S : SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool) I) (x : (i : Fin 2) → Unit) :
    ProbComp.eval (idealJoint (rotFunctionality k) I S x) =
      (idealROT k).bind fun y => (ProbComp.eval (S (fun _ => ()) (I.restrict y))).map (·, y) := by
  rw [eval_idealJoint, eval_rotFunctionality]

/-- Public communication over any joint input distribution `inputDist : PMF (In 0 × In 1)` never
increases conditional mutual information: `I((In₀, R₀); (In₁, R₁) | T) ≤ I(In₀; In₁)`. -/
theorem condMutualInfo_transcript_le_mutualInfo_input {In : Fin 2 → Type}
    [Finite (In 0)] [Finite (In 1)] [Finite (Coins 0)] [Finite (Coins 1)]
    [Finite (PublicTranscript sc)]
    (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (inputDist : PMF (In 0 × In 1)) :
    condMutualInfo ((realWithInputDist proto inputDist).map fun (views, _) =>
      (transcriptOfView proto 0 (views 0),
        ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
        ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0)))) ≤
      mutualInfo inputDist := by
  -- Each party's initial state `(input, coins)`, sampled jointly.
  let ν : PMF ((In 0 × Coins 0) × (In 1 × Coins 1)) :=
    inputDist.bind fun xy =>
      (ProbComp.eval (proto.sampleCoins 0)).bind fun r0 =>
        (ProbComp.eval (proto.sampleCoins 1)).map fun r1 => ((xy.1, r0), (xy.2, r1))
  let stOf : (In 0 × Coins 0) × (In 1 × Coins 1) → (i : Fin 2) → (In i × Coins i) :=
    fun ω => pairVec ω.1 ω.2
  let pureOut : (In 0 × Coins 0) × (In 1 × Coins 1) →
      ((i : Fin 2) → PartyView In Coins sc i) × ((i : Fin 2) → Out i) :=
    fun ω =>
      let st := stOf ω
      let recv := stepsExecPure proto.steps st
      let views : (i : Fin 2) → PartyView In Coins sc i :=
        fun i => ⟨(st i).1, (st i).2, recv i⟩
      (views, fun i => proto.outputOfView i (views i))
  let T_pure := fun ω => stepsTranscriptPure proto.steps (stOf ω)
  have hreal : realWithInputDist proto inputDist = ν.map pureOut := by
    rw [realWithInputDist]
    have hpi : ProbComp.eval (OracleComp.pi proto.sampleCoins) =
        ((ProbComp.eval (proto.sampleCoins 0)).bind fun r0 =>
          (ProbComp.eval (proto.sampleCoins 1)).map fun r1 => pairVec r0 r1) := by
      rw [OracleComp.pi_succ, OracleComp.pi_succ, OracleComp.pi_zero]
      simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.map_bind,
        PMF.pure_map]
      congr 1 with r0 : 1
      rw [← PMF.bind_pure_comp]
      congr 1 with r1 : 1
      dsimp only [Function.comp_def]
      congr 1
      funext i
      fin_cases i <;> rfl
    simp only [Protocol.evalWith_eq, hpi, stepsEvalWith_eq_pure, PMF.pure_map]
    simp only [ν, PMF.map_bind]
    congr 1 with xy : 1
    rw [PMF.bind_bind]
    congr 1 with r0 : 1
    rw [PMF.bind_map, PMF.map_comp, ← PMF.bind_pure_comp]
    congr 1 with r1 : 1
    dsimp only [Function.comp_def, pureOut]
    have hst : (fun i : Fin 2 => (pairVec xy.1 xy.2 i, pairVec r0 r1 i)) =
        stOf ((xy.1, r0), (xy.2, r1)) := by
      funext i
      fin_cases i <;> rfl
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · rw [hst]
      fin_cases i <;> rfl
    · rw [hst]
      fin_cases i <;> rfl
  have hBase : condMutualInfo (ν.map fun ω => (T_pure ω, ω.1, ω.2)) ≤ mutualInfo inputDist := by
    have hStrip : condMutualInfo (ν.map fun ω => (T_pure ω, ω.1, ω.2)) =
        condMutualInfo (ν.map fun ω => (((), T_pure ω), ω.1, ω.2)) :=
      (condMutualInfo_map_congr_cond ν Prod.fst Prod.snd (e := ((), ·))
        (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl)).symm
    have hSteps := condMutualInfo_steps_transcriptPure_le ν Prod.fst Prod.snd (fun _ => ())
      proto.steps Prod.fst Prod.snd ⟨Prod.fst, fun _ _ => rfl⟩ ⟨Prod.fst, fun _ _ => rfl⟩
    have hUnit : condMutualInfo (ν.map fun ω => ((), ω.1, ω.2)) = mutualInfo inputDist := by
      rw [condMutualInfo_map,
        entropy_map_eq_of_comp ν (F := fun ω => ω.1) (e := ((), ·))
          (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl),
        entropy_map_eq_of_comp ν (F := fun ω => ω.2) (e := ((), ·))
          (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl),
        entropy_map_eq_of_comp ν (F := fun ω => (ω.1, ω.2)) (e := ((), ·))
          (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl),
        show (ν.map fun _ => ()).entropy = 0 from
          entropy_eq_zero_of_subsingleton_support _ fun _ _ _ _ => rfl,
        sub_zero, ← mutualInfo_map]
      exact (congrArg mutualInfo (PMF.map_id ν)).trans (mutualInfo_bind_pair_indep inputDist _ _)
    exact hStrip.trans_le (hSteps.trans_eq hUnit)
  have hReencode :
      condMutualInfo ((realWithInputDist proto inputDist).map fun (views, _) =>
        (transcriptOfView proto 0 (views 0),
          ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
          ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0)))) ≤
      condMutualInfo (ν.map fun ω => (T_pure ω, ω.1, ω.2)) := by
    rw [hreal, PMF.map_comp]
    have htr : ∀ ω, transcriptOfView proto 0 ((pureOut ω).1 0) = T_pure ω :=
      fun ω => stepsTranscriptOfView_execPure proto.steps (stOf ω) 0
    have hmap : condMutualInfo (ν.map ((fun (views, _) =>
        (transcriptOfView proto 0 (views 0),
          ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
          ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0)))) ∘ pureOut)) =
        condMutualInfo (ν.map fun ω =>
          (T_pure ω, (ω.1.1, ω.1.2, T_pure ω), (ω.2.1, ω.2.2, T_pure ω))) := by
      refine congrArg (fun f => condMutualInfo (ν.map f)) ?_
      funext ⟨⟨_, _⟩, ⟨_, _⟩⟩
      dsimp only [Function.comp_def]
      exact Prod.ext (htr _) (Prod.ext (Prod.ext rfl (Prod.ext rfl (htr _)))
        (Prod.ext rfl (Prod.ext rfl (htr _))))
    rw [hmap]
    exact (condMutualInfo_map_le_of_comp ν T_pure
      (fun ω => (ω.1, T_pure ω)) (fun ω => (ω.1.1, ω.1.2, T_pure ω))
      (fun ω => (ω.2, T_pure ω)) (fun ω => (ω.2.1, ω.2.2, T_pure ω))
      (fun p => (p.1.1, p.1.2, p.2)) (fun _ _ => rfl)
      (fun p => (p.1.1, p.1.2, p.2)) (fun _ _ => rfl)).trans_eq
      (condMutualInfo_map_pair_self ν T_pure Prod.fst Prod.snd)
  exact hReencode.trans hBase

/-- Public communication over a correlated source never increases conditional mutual information:
`I((A, R₀); (B, R₁) | T) ≤ I(A; B)`. -/
theorem condMutualInfo_transcript_le_mutualInfo
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins Out)
    (source : PMF (A × B)) :
    condMutualInfo ((realCorrelated proto source).map fun (views, _) =>
      (transcriptOfView proto 0 (views 0),
        ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
        ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0))) :
        PMF (PublicTranscript sc × (A × Coins 0 × PublicTranscript sc) ×
          (B × Coins 1 × PublicTranscript sc))) ≤
      mutualInfo source := by
  let In : Fin 2 → Type := Fin.cases A (fun _ => B)
  let source' : PMF (In 0 × In 1) := source
  have hFin0 := finite_finCases (A := A) (B := B) 0
  have hFin1 := finite_finCases (A := A) (B := B) 1
  have hreal : realCorrelated proto source = realWithInputDist proto source' := by
    dsimp only [realCorrelated, realWithInputDist, source']
    congr 1 with ab : 1
    have hfin : (Fin.cases ab.1 (fun _ => ab.2) : (i : Fin 2) → In i) =
        pairVec (F := In) ab.1 ab.2 := by
      funext i
      fin_cases i <;> rfl
    rw [hfin]
  have hBound := @condMutualInfo_transcript_le_mutualInfo_input sc Coins Out In
    hFin0 hFin1 ‹Finite (Coins 0)› ‹Finite (Coins 1)› ‹Finite (PublicTranscript sc)›
    proto source'
  have hEq : condMutualInfo ((realCorrelated proto source).map fun (views, _) =>
      (transcriptOfView proto 0 (views 0),
        ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
        ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0))) :
        PMF (PublicTranscript sc × (A × Coins 0 × PublicTranscript sc) ×
          (B × Coins 1 × PublicTranscript sc))) =
      condMutualInfo ((realWithInputDist proto source').map fun (views, _) =>
        (transcriptOfView proto 0 (views 0),
          ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
          ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0)))) := by
    rw [hreal]
    rfl
  exact hEq.trans_le hBound

/-- Reparametrizing `k` uniform ROT instances `(S, C) ↔ ((C, Y), U)` preserves uniformity. -/
private def rotEquiv (k : ℕ) :
    ((Fin k → Bool × Bool) × (Fin k → Bool)) ≃
      ((Fin k → Bool × Bool) × (Fin k → Bool)) where
  toFun sc :=
    (fun j => (sc.2 j, otSelect (sc.1 j) (sc.2 j)),
      fun j => otSelect (sc.1 j) (!(sc.2 j)))
  invFun ru :=
    (fun j => if (ru.1 j).1 then (ru.2 j, (ru.1 j).2) else ((ru.1 j).2, ru.2 j),
      fun j => (ru.1 j).1)
  left_inv sc := by
    obtain ⟨s, c⟩ := sc
    refine Prod.ext (funext fun j => ?_) rfl
    rcases hs : s j with ⟨m0, m1⟩
    by_cases hc : c j = true
    · simp only [otSelect, hc, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, hs]
    · have hc' : c j = false := Bool.eq_false_iff.mpr hc
      simp only [otSelect, hc', Bool.not_false, Bool.false_eq_true, ite_true, ite_false, hs]
  right_inv ru := by
    obtain ⟨r, u⟩ := ru
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · rcases hr : r j with ⟨c, y⟩
      by_cases hc : c = true
      · simp only [otSelect, hr, hc, ite_true]
      · have hc' : c = false := Bool.eq_false_iff.mpr hc
        simp only [otSelect, hr, hc', Bool.false_eq_true, ite_false]
    · rcases hr : r j with ⟨c, y⟩
      by_cases hc : c = true
      · simp only [otSelect, hr, hc, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
      · have hc' : c = false := Bool.eq_false_iff.mpr hc
        simp only [otSelect, hr, hc', Bool.not_false, Bool.false_eq_true, ite_true, ite_false]

/-- **Ahlswede–Csiszár-style upper bound for correlated-source MPC protocols**:
any two-party plain-channel protocol over correlated source `source : PMF (A × B)` that realizes
`k` independent random OTs (`rotFunctionality k`) with perfect semi-honest privacy against `{0}`
and `{1}` requires `(k : ℝ) ≤ I(A; B)`. -/
theorem rot_le_mutualInfo
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource source) (rotFunctionality k) S) :
    (k : ℝ) ≤ mutualInfo source := by
  have hFin0 := finite_finCases (A := A) (B := B) 0
  have hFin1 := finite_finCases (A := A) (B := B) 1
  let real := realCorrelated proto source
  let in0 : (((i : Fin 2) → PartyView (Fin.cases A (fun _ => B)) Coins sc i) ×
      ((i : Fin 2) → Fin k → Bool × Bool)) → A := fun ω => (ω.1 0).input
  let in1 : (((i : Fin 2) → PartyView (Fin.cases A (fun _ => B)) Coins sc i) ×
      ((i : Fin 2) → Fin k → Bool × Bool)) → B := fun ω => (ω.1 1).input
  let T : (((i : Fin 2) → PartyView (Fin.cases A (fun _ => B)) Coins sc i) ×
      ((i : Fin 2) → Fin k → Bool × Bool)) → PublicTranscript sc :=
    fun (views, _) => transcriptOfView proto 0 (views 0)
  let VA : (((i : Fin 2) → PartyView (Fin.cases A (fun _ => B)) Coins sc i) ×
      ((i : Fin 2) → Fin k → Bool × Bool)) → A × Coins 0 × PublicTranscript sc :=
    fun (views, _) => ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0))
  let VB : (((i : Fin 2) → PartyView (Fin.cases A (fun _ => B)) Coins sc i) ×
      ((i : Fin 2) → Fin k → Bool × Bool)) → B × Coins 1 × PublicTranscript sc :=
    fun (views, _) => ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0))
  let outA : A × Coins 0 × PublicTranscript sc → Fin k → Bool × Bool :=
    fun (a, r0, t) =>
      proto.outputOfView 0 ⟨a, r0, stepsReceivedOfTranscript proto.steps 0 (a, r0) t⟩
  let outB : B × Coins 1 × PublicTranscript sc → Fin k → Bool × Bool :=
    fun (b, r1, t) =>
      proto.outputOfView 1 ⟨b, r1, stepsReceivedOfTranscript proto.steps 1 (b, r1) t⟩
  have hOutA : ∀ ω ∈ real.support, ω.2 0 = outA (VA ω) := by
    intro ⟨views, out⟩ hω
    dsimp only [real] at hω
    rw [realCorrelated, PMF.mem_support_bind_iff] at hω
    obtain ⟨_, _, hev⟩ := hω
    obtain ⟨hvw0, hout⟩ := partyView_eq_of_mem_support_evalWith proto hev 0
    exact hout.trans (congrArg (proto.outputOfView 0) hvw0)
  have hOutB : ∀ ω ∈ real.support, ω.2 1 = outB (VB ω) := by
    intro ⟨views, out⟩ hω
    dsimp only [real] at hω
    rw [realCorrelated, PMF.mem_support_bind_iff] at hω
    obtain ⟨_, _, hev⟩ := hω
    obtain ⟨hvw1, hout⟩ := partyView_eq_of_mem_support_evalWith proto hev 1
    exact hout.trans (congrArg (proto.outputOfView 1) hvw1)
  have h0_neq : ({0} : Finset (Fin 2)) ≠ Finset.univ := by decide
  have h1_neq : ({1} : Finset (Fin 2)) ≠ Finset.univ := by decide
  have hPriv0 : ProbComp.eval (idealJoint (rotFunctionality k) {0} (S {0}) fun _ => ()) =
      (realCorrelated proto source).map (Prod.map ({0} : Finset (Fin 2)).restrict id) :=
    (hPriv {0} h0_neq _).trans (dealSource_bind_realJoint proto source {0})
  have hPriv1 : ProbComp.eval (idealJoint (rotFunctionality k) {1} (S {1}) fun _ => ()) =
      (realCorrelated proto source).map (Prod.map ({1} : Finset (Fin 2)).restrict id) :=
    (hPriv {1} h1_neq _).trans (dealSource_bind_realJoint proto source {1})
  have hCorrect : ∀ ω ∈ real.support, ∀ j : Fin k,
      (ω.2 1 j).2 = otSelect (ω.2 0 j) (ω.2 1 j).1 := by
    intro ⟨views, out⟩ hω j
    have hmem : (({0} : Finset (Fin 2)).restrict views, out) ∈
        ((realCorrelated proto source).map
          (Prod.map ({0} : Finset (Fin 2)).restrict id)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨(views, out), hω, rfl⟩
    rw [← hPriv0, eval_idealJoint_rotFunctionality, PMF.mem_support_bind_iff] at hmem
    obtain ⟨y, hy, hres⟩ := hmem
    rw [PMF.mem_support_map_iff] at hres
    obtain ⟨_, _, hy_eq⟩ := hres
    have hout : out = y := congrArg Prod.snd hy_eq.symm
    rw [idealROT, PMF.mem_support_map_iff] at hy
    obtain ⟨⟨sb, ch⟩, _, rfl⟩ := hy
    rw [hout]
    rfl
  have hAlicePriv : real.map (fun ω => ((ω.2 0, T ω), rotChoices (ω.2 1))) =
      (real.map fun ω => (ω.2 0, T ω)).bind fun st =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·) := by
    let proj0 : (((i : ({0} : Finset (Fin 2))) →
        PartyView (Fin.cases A (fun _ => B)) Coins sc i) ×
        ((i : Fin 2) → Fin k → Bool × Bool)) →
        ((Fin k → Bool × Bool) × PublicTranscript sc) × (Fin k → Bool) :=
      fun (v0, y) => ((y 0, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)),
        rotChoices (y 1))
    have hRealProj : real.map (fun ω => ((ω.2 0, T ω), rotChoices (ω.2 1))) =
        ((realCorrelated proto source).map
          (Prod.map ({0} : Finset (Fin 2)).restrict id)).map proj0 := by
      rw [PMF.map_comp]
      rfl
    have hIdealEq : ProbComp.eval (idealJoint (rotFunctionality k) {0} (S {0})
        fun _ => ()) =
        (PMF.uniformOfFintype (Fin k → Bool × Bool)).bind fun sb =>
          (ProbComp.eval (S {0} (fun _ => ()) (restrictZero (F := fun _ => Fin k → Bool × Bool)
            sb))).bind fun v0 =>
            (PMF.uniformOfFintype (Fin k → Bool)).map fun ch =>
              (v0, Fin.cases (motive := fun _ => Fin k → Bool × Bool) sb
                (fun _ j => (ch j, otSelect (sb j) (ch j)))) := by
      rw [eval_idealJoint_rotFunctionality,
        idealROT, ← uniformOfFintype_prod, PMF.bind_map, PMF.bind_bind]
      congr 1 with sb : 1
      rw [PMF.bind_map]
      dsimp only [Function.comp_def]
      have hres : ∀ ch : Fin k → Bool,
          ({0} : Finset (Fin 2)).restrict
            (Fin.cases (motive := fun _ => Fin k → Bool × Bool) sb
              (fun _ j => (ch j, otSelect (sb j) (ch j)))) =
            restrictZero (F := fun _ => Fin k → Bool × Bool) sb := by
        intro ch
        funext ⟨i, hi⟩
        obtain rfl := Finset.mem_singleton.mp hi
        rfl
      simp only [hres, ← PMF.bind_pure_comp]
      rw [PMF.bind_comm]
      rfl
    have hLHS : (ProbComp.eval (idealJoint (rotFunctionality k) {0} (S {0})
        fun _ => ())).map proj0 =
        ((PMF.uniformOfFintype (Fin k → Bool × Bool)).bind fun sb =>
          (ProbComp.eval (S {0} (fun _ => ()) (restrictZero (F := fun _ => Fin k → Bool × Bool)
            sb))).map fun v0 =>
            (sb, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩))).bind
          fun st => (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·) := by
      rw [hIdealEq, PMF.map_bind, PMF.bind_bind]
      congr 1 with sb : 1
      rw [PMF.map_bind, PMF.bind_map]
      congr 1 with v0 : 1
      rw [PMF.map_comp]
      rfl
    have hMarginal : (ProbComp.eval (idealJoint (rotFunctionality k) {0} (S {0})
        fun _ => ())).map (fun p => (proj0 p).1) =
        real.map fun ω => (ω.2 0, T ω) := by
      rw [hPriv0, PMF.map_comp]
      rfl
    have hMargSimp : (ProbComp.eval (idealJoint (rotFunctionality k) {0} (S {0})
        fun _ => ())).map (fun p => (proj0 p).1) =
        (PMF.uniformOfFintype (Fin k → Bool × Bool)).bind fun sb =>
          (ProbComp.eval (S {0} (fun _ => ()) (restrictZero (F := fun _ => Fin k → Bool × Bool)
            sb))).map fun v0 =>
            (sb, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)) := by
      rw [hIdealEq, PMF.map_bind]
      congr 1 with sb : 1
      rw [PMF.map_bind]
      congr 1 with v0 : 1
      rw [PMF.map_comp]
      change PMF.map (Function.const (Fin k → Bool)
          (sb, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)))
          (PMF.uniformOfFintype (Fin k → Bool)) = _
      exact PMF.map_const _ _
    rw [hRealProj, ← hPriv0, hLHS, ← hMargSimp, hMarginal]
  have hBobPriv : real.map (fun ω => ((T ω, ω.2 1), rotUnselected (ω.2 0) (ω.2 1))) =
      (real.map fun ω => (T ω, ω.2 1)).bind fun tr =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·) := by
    let proj1 : (((i : ({1} : Finset (Fin 2))) →
        PartyView (Fin.cases A (fun _ => B)) Coins sc i) ×
        ((i : Fin 2) → Fin k → Bool × Bool)) →
        (PublicTranscript sc × (Fin k → Bool × Bool)) × (Fin k → Bool) :=
      fun (v1, y) => ((transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩), y 1),
        rotUnselected (y 0) (y 1))
    have hRealProj : (realCorrelated proto source).map
          (fun ω => ((T ω, ω.2 1), rotUnselected (ω.2 0) (ω.2 1))) =
        ((realCorrelated proto source).map
          (Prod.map ({1} : Finset (Fin 2)).restrict id)).map proj1 := by
      rw [PMF.map_comp]
      refine map_congr_on_support (realCorrelated proto source) _ _ fun ⟨views, out⟩ hω => ?_
      have h01 : transcriptOfView proto 0 (views 0) = transcriptOfView proto 1 (views 1) := by
        rw [realCorrelated, PMF.mem_support_bind_iff] at hω
        obtain ⟨_, _, hev⟩ := hω
        exact transcriptOfView_zero_eq_one proto hev
      exact Prod.ext (Prod.ext h01 rfl) rfl
    have hRealMarg : ((realCorrelated proto source).map
          (Prod.map ({1} : Finset (Fin 2)).restrict id)).map (fun p => (proj1 p).1) =
        real.map fun ω => (T ω, ω.2 1) := by
      have hm := congrArg (PMF.map Prod.fst) hRealProj
      simp only [PMF.map_comp] at hm ⊢
      exact hm.symm
    have hIdealRotRe : idealROT k =
        (PMF.uniformOfFintype ((Fin k → Bool × Bool) × (Fin k → Bool))).map
          fun (rb, ub) =>
            Fin.cases (fun j => if (rb j).1 then (ub j, (rb j).2) else ((rb j).2, ub j))
              (fun _ => rb) := by
      have hU : (PMF.uniformOfFintype ((Fin k → Bool × Bool) × (Fin k → Bool))).map
            (rotEquiv k).symm =
          PMF.uniformOfFintype ((Fin k → Bool × Bool) × (Fin k → Bool)) :=
        uniformOfFintype_map_equiv (rotEquiv k).symm
      rw [idealROT]
      conv_lhs => rw [← hU, PMF.map_comp]
      congr 1
      funext ⟨rb, ub⟩
      funext i
      fin_cases i
      · rfl
      · funext j
        dsimp only [Function.comp_def, rotEquiv, Equiv.coe_fn_symm_mk]
        change ((rb j).1,
          otSelect (if (rb j).1 then (ub j, (rb j).2) else ((rb j).2, ub j)) (rb j).1) = rb j
        cases hc : (rb j).1
        · exact Prod.ext hc.symm rfl
        · exact Prod.ext hc.symm rfl
    have hIdealEq : ProbComp.eval (idealJoint (rotFunctionality k) {1} (S {1})
        fun _ => ()) =
        (PMF.uniformOfFintype (Fin k → Bool × Bool)).bind fun rb =>
          (ProbComp.eval (S {1} (fun _ => ()) (restrictOne (F := fun _ => Fin k → Bool × Bool)
            rb))).bind fun v1 =>
            (PMF.uniformOfFintype (Fin k → Bool)).map fun ub =>
              (v1, Fin.cases (motive := fun _ => Fin k → Bool × Bool)
                (fun j => if (rb j).1 then (ub j, (rb j).2) else ((rb j).2, ub j))
                (fun _ => rb)) := by
      rw [eval_idealJoint_rotFunctionality,
        hIdealRotRe, ← uniformOfFintype_prod, PMF.bind_map, PMF.bind_bind]
      congr 1 with rb : 1
      rw [PMF.bind_map]
      dsimp only [Function.comp_def]
      have hres : ∀ ub : Fin k → Bool,
          ({1} : Finset (Fin 2)).restrict
            (Fin.cases (motive := fun _ => Fin k → Bool × Bool)
              (fun j => if (rb j).1 then (ub j, (rb j).2) else ((rb j).2, ub j))
              (fun _ => rb)) =
            restrictOne (F := fun _ => Fin k → Bool × Bool) rb := by
        intro ub
        funext ⟨i, hi⟩
        obtain rfl := Finset.mem_singleton.mp hi
        rfl
      simp only [hres, ← PMF.bind_pure_comp]
      rw [PMF.bind_comm]
      rfl
    have hLHS : (ProbComp.eval (idealJoint (rotFunctionality k) {1} (S {1})
        fun _ => ())).map proj1 =
        ((PMF.uniformOfFintype (Fin k → Bool × Bool)).bind fun rb =>
          (ProbComp.eval (S {1} (fun _ => ())
            (restrictOne (F := fun _ => Fin k → Bool × Bool) rb))).map fun v1 =>
            (transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩), rb)).bind
          fun tr => (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·) := by
      rw [hIdealEq, PMF.map_bind, PMF.bind_bind]
      congr 1 with rb : 1
      rw [PMF.map_bind, PMF.bind_map]
      congr 1 with v1 : 1
      rw [PMF.map_comp]
      congr 1 with ub : 1
      refine Prod.ext rfl (funext fun j => ?_)
      dsimp only [Function.comp_def, proj1, rotUnselected]
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ, Fin.cases_zero]
      cases hc : (rb j).1 <;> simp only [Bool.not_false, Bool.not_true, otSelect,
        Bool.false_eq_true, ↓reduceIte]
    have hMarginal : (ProbComp.eval (idealJoint (rotFunctionality k) {1} (S {1})
        fun _ => ())).map (fun p => (proj1 p).1) =
        real.map fun ω => (T ω, ω.2 1) := by
      rw [hPriv1, hRealMarg]
    have hMargSimp : (ProbComp.eval (idealJoint (rotFunctionality k) {1} (S {1})
        fun _ => ())).map (fun p => (proj1 p).1) =
        (PMF.uniformOfFintype (Fin k → Bool × Bool)).bind fun rb =>
          (ProbComp.eval (S {1} (fun _ => ())
            (restrictOne (F := fun _ => Fin k → Bool × Bool) rb))).map fun v1 =>
            (transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩), rb) := by
      rw [hIdealEq, PMF.map_bind]
      congr 1 with rb : 1
      rw [PMF.map_bind]
      congr 1 with v1 : 1
      rw [PMF.map_comp]
      change PMF.map (Function.const (Fin k → Bool)
          (transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩), rb))
          (PMF.uniformOfFintype (Fin k → Bool)) = _
      exact PMF.map_const _ _
    rw [hRealProj, ← hPriv1, hLHS, ← hMargSimp, hMarginal]
  have hSourceEq : real.map (fun ω => (in0 ω, in1 ω)) = source := by
    have h := bind_evalWith_map_input proto source
      (fun ab => Fin.cases ab.1 (fun _ => ab.2)) (fun a : A => a) (fun b : B => b)
    exact h.trans (PMF.map_id source)
  rw [← hSourceEq]
  exact natCast_le_mutualInfo_of_rot real in0 in1 VA VB T (fun ω => ω.2 0) (fun ω => ω.2 1)
    (by
      rw [hSourceEq]
      exact condMutualInfo_transcript_le_mutualInfo proto source)
    outA hOutA outB hOutB hCorrect hAlicePriv hBobPriv

end Correlated2PC

/-! ### Chosen-input OT protocols over correlated randomness -/

section ChosenInputOT

variable {A B : Type} {sc : Schedule 2 noOracleSpec} {ExtIn Coins Out : Fin 2 → Type}

/-- Real execution of a correlated-source protocol taking external party inputs
`x : (i : Fin 2) → ExtIn i`. -/
@[expose] noncomputable def realCorrelatedWithInput
    (proto : Protocol 2 noOracleSpec sc (fun i => ExtIn i × Fin.cases A (fun _ => B) i) Coins Out)
    (source : PMF (A × B)) (x : (i : Fin 2) → ExtIn i) :
    PMF (((i : Fin 2) → PartyView (fun i => ExtIn i × Fin.cases A (fun _ => B) i) Coins sc i) ×
      ((i : Fin 2) → Out i)) :=
  source.bind fun ab =>
    proto.evalWith noOracleWorld (fun i => (x i, Fin.cases ab.1 (fun _ => ab.2) i))

/-- The trusted setup dealing correlated source `source : PMF (A × B)` next to the external inputs
`x`: party `i` receives `(x i, share i)`. Privacy over `source` with external inputs is
`PerfectSemiHonestPrivateProperWithSetup` with setup `dealSourceWithInput source`. -/
noncomputable def dealSourceWithInput (source : PMF (A × B))
    (x : (i : Fin 2) → ExtIn i) : PMF ((i : Fin 2) → ExtIn i × Fin.cases A (fun _ => B) i) :=
  source.map fun ab i => (x i, Fin.cases ab.1 (fun _ => ab.2) i)

/-- The real side of privacy over `dealSourceWithInput source` on inputs `x` is the correlated
execution on `x` restricted to the coalition. -/
theorem dealSourceWithInput_bind_realJoint
    (proto : Protocol 2 noOracleSpec sc (fun i => ExtIn i × Fin.cases A (fun _ => B) i) Coins Out)
    (source : PMF (A × B)) (I : Finset (Fin 2)) (x : (i : Fin 2) → ExtIn i) :
    (dealSourceWithInput source x).bind (proto.realJoint noOracleWorld I) =
      (realCorrelatedWithInput proto source x).map (Prod.map I.restrict id) := by
  rw [Protocol.bind_realJoint, dealSourceWithInput, PMF.bind_map]
  rfl

/-- Reparametrize `(y1, u)` into sender input tables `Fin k → Bool → Bool` relative to choice
vector `c : Fin k → Bool` so `x0 j (c j) = y1 j` and `x0 j (!(c j)) = u j`. -/
private def otPairEquiv {k : ℕ} (c : Fin k → Bool) :
    ((Fin k → Bool) × (Fin k → Bool)) ≃ (Fin k → Bool → Bool) where
  toFun p j b := if b == c j then p.1 j else p.2 j
  invFun x0 := (fun j => x0 j (c j), fun j => x0 j (!(c j)))
  left_inv p := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    · dsimp only
      cases hc : c j <;> rfl
  right_inv x0 := by
    funext j b
    dsimp only
    cases hc : c j <;> cases b <;> rfl

/-- Choosing uniform random sender tables and receiver choices turns any perfectly semi-honest
private chosen-input `k`-OT protocol (`batchOTFunctionality k Bool`) over correlated source
`source : PMF (A × B)` into a `k`-ROT protocol over `source`, hence `(k : ℝ) ≤ I(A; B)`. -/
theorem chosenOT_le_mutualInfo
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec k Bool).Query ())
        (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
        ((batchOTSpec k Bool).Answer ()) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput source) (batchOTFunctionality k Bool) S) :
    (k : ℝ) ≤ mutualInfo source := by
  let eQ0 : (Fin k → Bool → Bool) ≃ (batchOTSpec k Bool).Query () 0 :=
    Equiv.cast (rfl : (Fin k → Bool → Bool) = (batchOTSpec k Bool).Query () 0)
  let eQ1 : (Fin k → Bool) ≃ (batchOTSpec k Bool).Query () 1 :=
    Equiv.cast (rfl : (Fin k → Bool) = (batchOTSpec k Bool).Query () 1)
  let eA1 : (Fin k → Bool) ≃ (batchOTSpec k Bool).Answer () 1 :=
    Equiv.cast (rfl : (Fin k → Bool) = (batchOTSpec k Bool).Answer () 1)
  have heQ0 : ∀ x0 j b, eQ0 x0 j b = x0 j b := fun _ _ _ => rfl
  have heQ1 : ∀ x1 j, eQ1 x1 j = x1 j := fun _ _ => rfl
  let eA : A ≃ Fin.cases A (fun _ => B) (0 : Fin 2) :=
    Equiv.cast (rfl : A = Fin.cases A (fun _ => B) (0 : Fin 2))
  let eB : B ≃ Fin.cases A (fun _ => B) (1 : Fin 2) :=
    Equiv.cast (rfl : B = Fin.cases A (fun _ => B) (1 : Fin 2))
  let In := fun i : Fin 2 => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i
  have : Finite (In 0) := inferInstanceAs (Finite ((Fin k → Bool → Bool) × A))
  have : Finite (In 1) := inferInstanceAs (Finite ((Fin k → Bool) × B))
  let inputDist : PMF (In 0 × In 1) :=
    source.bind fun ab =>
      (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
        (PMF.uniformOfFintype (Fin k → Bool)).map fun x1 =>
          ((eQ0 x0, eA ab.1), (eQ1 x1, eB ab.2))
  let real := realWithInputDist proto inputDist
  have hRealUnif : real =
      (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
        (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
          realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1)) := by
    dsimp only [real]
    rw [realWithInputDist]
    simp only [inputDist, PMF.bind_bind]
    rw [PMF.bind_comm]
    congr 1 with x0 : 1
    calc source.bind (fun ab =>
          ((PMF.uniformOfFintype (Fin k → Bool)).map fun x1 =>
            ((eQ0 x0, eA ab.1), (eQ1 x1, eB ab.2))).bind fun xy =>
            proto.evalWith noOracleWorld (pairVec (F := In) xy.1 xy.2))
        = source.bind (fun ab =>
            (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
              proto.evalWith noOracleWorld
                (pairVec (F := In) (eQ0 x0, eA ab.1) (eQ1 x1, eB ab.2))) := by
          congr 1 with ab : 1
          rw [PMF.bind_map]
          rfl
      _ = (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
            source.bind fun ab =>
              proto.evalWith noOracleWorld
                (pairVec (F := In) (eQ0 x0, eA ab.1) (eQ1 x1, eB ab.2)) := PMF.bind_comm _ _ _
      _ = (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
            realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1)) := by
          congr 1 with x1 : 1
          dsimp only [realCorrelatedWithInput]
          congr 1 with ab : 1
          have hfin : pairVec (F := In) (eQ0 x0, eA ab.1) (eQ1 x1, eB ab.2) =
              fun i => (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1) i,
                Fin.cases ab.1 (fun _ => ab.2) i) := by
            funext i
            fin_cases i <;> rfl
          rw [hfin]
  let T : (((i : Fin 2) → PartyView In Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i)) → PublicTranscript sc :=
    fun (views, _) => transcriptOfView proto 0 (views 0)
  let VA : (((i : Fin 2) → PartyView In Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i)) → In 0 × Coins 0 × PublicTranscript sc :=
    fun (views, _) => ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0))
  let VB : (((i : Fin 2) → PartyView In Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i)) → In 1 × Coins 1 × PublicTranscript sc :=
    fun (views, _) => ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0))
  let SOut : (((i : Fin 2) → PartyView In Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i)) → Fin k → Bool × Bool :=
    fun (views, _) j => ((views 0).input.1 j false, (views 0).input.1 j true)
  let ROut : (((i : Fin 2) → PartyView In Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i)) → Fin k → Bool × Bool :=
    fun (views, out) j => ((views 1).input.1 j, out 1 j)
  let outA : In 0 × Coins 0 × PublicTranscript sc → Fin k → Bool × Bool :=
    fun (x, _, _) j => (x.1 j false, x.1 j true)
  let outB : In 1 × Coins 1 × PublicTranscript sc → Fin k → Bool × Bool :=
    fun (x, r1, t) j =>
      (x.1 j, proto.outputOfView 1 ⟨x, r1, stepsReceivedOfTranscript proto.steps 1 (x, r1) t⟩ j)
  have hOutA : ∀ ω ∈ real.support, SOut ω = outA (VA ω) := fun _ _ => rfl
  have hOutB : ∀ ω ∈ real.support, ROut ω = outB (VB ω) := by
    intro ⟨views, out⟩ hω
    dsimp only [real] at hω
    rw [realWithInputDist, PMF.mem_support_bind_iff] at hω
    obtain ⟨_, _, hev⟩ := hω
    obtain ⟨hvw1, hout⟩ := partyView_eq_of_mem_support_evalWith proto hev 1
    funext j
    exact Prod.ext rfl ((congrArg (fun f => f j) hout).trans
      (congrArg (fun v => proto.outputOfView 1 v j) hvw1))
  have h0_neq : ({0} : Finset (Fin 2)) ≠ Finset.univ := by decide
  have h1_neq : ({1} : Finset (Fin 2)) ≠ Finset.univ := by decide
  have hPriv0 : ∀ x, ProbComp.eval (idealJoint (batchOTFunctionality k Bool) {0} (S {0}) x) =
      (realCorrelatedWithInput proto source x).map (Prod.map ({0} : Finset (Fin 2)).restrict id) :=
    fun x => (hPriv {0} h0_neq x).trans (dealSourceWithInput_bind_realJoint proto source {0} x)
  have hPriv1 : ∀ x, ProbComp.eval (idealJoint (batchOTFunctionality k Bool) {1} (S {1}) x) =
      (realCorrelatedWithInput proto source x).map (Prod.map ({1} : Finset (Fin 2)).restrict id) :=
    fun x => (hPriv {1} h1_neq x).trans (dealSourceWithInput_bind_realJoint proto source {1} x)
  have hInOfSupport :
      ∀ (x0 : (batchOTSpec k Bool).Query () 0) (x1 : (batchOTSpec k Bool).Query () 1)
      {views out},
      (views, out) ∈ (realCorrelatedWithInput proto source (pairVec x0 x1)).support →
      (views 0).input.1 = x0 ∧ (views 1).input.1 = x1 := by
    intro x0 x1 views out hmem
    rw [realCorrelatedWithInput, PMF.mem_support_bind_iff] at hmem
    obtain ⟨ab, _, hev⟩ := hmem
    rw [Protocol.evalWith_eq, PMF.mem_support_bind_iff] at hev
    obtain ⟨r, _, hrecv⟩ := hev
    rw [PMF.mem_support_map_iff] at hrecv
    obtain ⟨recv, _, hres⟩ := hrecv
    have hviews := congrArg Prod.fst hres.symm
    refine ⟨?_, ?_⟩
    · have h0 := congrFun hviews 0
      exact congrArg (fun v => v.input.1) h0
    · have h1 := congrFun hviews 1
      exact congrArg (fun v => v.input.1) h1
  have hCorrect : ∀ ω ∈ real.support, ∀ j : Fin k,
      (ROut ω j).2 = otSelect (SOut ω j) (ROut ω j).1 := by
    intro ⟨views, out⟩ hω j
    rw [hRealUnif, PMF.mem_support_bind_iff] at hω
    obtain ⟨x0, _, hω⟩ := hω
    rw [PMF.mem_support_bind_iff] at hω
    obtain ⟨x1, _, hω⟩ := hω
    obtain ⟨hin0, hin1⟩ := hInOfSupport (eQ0 x0) (eQ1 x1) hω
    have hmem : (({0} : Finset (Fin 2)).restrict views, out) ∈
        ((realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
          (Prod.map ({0} : Finset (Fin 2)).restrict id)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨(views, out), hω, rfl⟩
    rw [← hPriv0, eval_idealJoint, PMF.mem_support_bind_iff] at hmem
    obtain ⟨y, hy, hres⟩ := hmem
    rw [PMF.mem_support_map_iff] at hres
    obtain ⟨_, _, hy_eq⟩ := hres
    have hout : out = y := congrArg Prod.snd hy_eq.symm
    have hy_eq' : y = batchOTAnswer (pairVec (eQ0 x0) (eQ1 x1)) := by
      simpa only [batchOTFunctionality, Functionality.ofDeterministic, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] using hy
    have hy1 : out 1 j = x0 j (x1 j) := by
      rw [hout, hy_eq']
      rfl
    dsimp only [ROut, SOut]
    rw [hin0, hin1, hy1, heQ0, heQ0, heQ1]
    cases x1 j <;> simp only [otSelect_false, otSelect_true]
  have hAlicePriv : real.map (fun ω => ((SOut ω, T ω), rotChoices (ROut ω))) =
      (real.map fun ω => (SOut ω, T ω)).bind fun st =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·) := by
    let sOf : (Fin k → Bool → Bool) → (Fin k → Bool × Bool) :=
      fun x0 j => (x0 j false, x0 j true)
    have hStep0 : ∀ (x0 : Fin k → Bool → Bool) (x1 : Fin k → Bool),
        (realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
          (fun ω => ((SOut ω, T ω), rotChoices (ROut ω))) =
        ((ProbComp.eval (S {0} (restrictZero (eQ0 x0))
            (restrictZero (F := (batchOTSpec k Bool).Answer ()) ()))).map
          fun v0 =>
            ((sOf x0, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)), x1)) := by
      intro x0 x1
      have hLHS : (realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
          (fun ω => ((SOut ω, T ω), rotChoices (ROut ω))) =
          ((realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
            (Prod.map ({0} : Finset (Fin 2)).restrict id)).map
            (fun (v0, _) => ((sOf ((v0 ⟨0, Finset.mem_singleton_self 0⟩).input.1),
              transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)), x1)) := by
        rw [PMF.map_comp]
        refine map_congr_on_support _ _ _ fun ⟨views, out⟩ hω => ?_
        obtain ⟨hin0, hin1⟩ := hInOfSupport (eQ0 x0) (eQ1 x1) hω
        refine Prod.ext (Prod.ext ?_ rfl) ?_
        · rfl
        · dsimp only [Function.comp_def, Prod.map_apply, id_eq, rotChoices, ROut]
          rw [hin1]
          exact funext (heQ1 x1)
      rw [hLHS, ← hPriv0, eval_idealJoint, batchOTFunctionality, Functionality.ofDeterministic]
      simp only [ProbComp.eval_pure, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      have hrest : ({0} : Finset (Fin 2)).restrict
          (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1)) =
          restrictZero (eQ0 x0) := restrictZero_pairVec _ _
      have hresty : ({0} : Finset (Fin 2)).restrict
          (batchOTAnswer (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1))) =
          restrictZero (F := (batchOTSpec k Bool).Answer ()) () := by
        funext ⟨i, hi⟩
        obtain rfl := Finset.mem_singleton.mp hi
        rfl
      rw [hrest, hresty]
      refine map_congr_on_support
        (ProbComp.eval (S {0} (restrictZero (eQ0 x0))
          (restrictZero (F := (batchOTSpec k Bool).Answer ()) ())))
        _ _ fun v0 hv0 => ?_
      have hv0_supp :
          (v0, batchOTAnswer (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1))) ∈
            ((realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
              (Prod.map ({0} : Finset (Fin 2)).restrict id)).support := by
        rw [← hPriv0, eval_idealJoint, batchOTFunctionality, Functionality.ofDeterministic]
        simp only [ProbComp.eval_pure, PMF.pure_bind, PMF.mem_support_map_iff]
        rw [hrest, hresty]
        exact ⟨v0, hv0, rfl⟩
      rw [PMF.mem_support_map_iff] at hv0_supp
      obtain ⟨⟨views, out⟩, hω, hres⟩ := hv0_supp
      obtain ⟨hin0, _⟩ := hInOfSupport (eQ0 x0) (eQ1 x1) hω
      have hv0_eq : v0 ⟨0, Finset.mem_singleton_self 0⟩ = views 0 :=
        (congrFun (congrArg Prod.fst hres) ⟨0, Finset.mem_singleton_self 0⟩).symm
      rw [hv0_eq, hin0]
      refine Prod.ext (Prod.ext (funext fun j => ?_) rfl) rfl
      simp only [sOf, heQ0]
    have hMain : real.map (fun ω => ((SOut ω, T ω), rotChoices (ROut ω))) =
        ((PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
          (ProbComp.eval (S {0} (restrictZero (eQ0 x0))
              (restrictZero (F := (batchOTSpec k Bool).Answer ()) ()))).map
            fun v0 =>
              (sOf x0, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩))).bind
          fun st => (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·) := by
      rw [hRealUnif, PMF.map_bind]
      simp only [PMF.map_bind, hStep0]
      rw [PMF.bind_bind]
      congr 1 with x0 : 1
      rw [PMF.bind_map]
      simp only [← PMF.bind_pure_comp, Function.comp_def]
      exact PMF.bind_comm _ _ _
    have hMarg : real.map (fun ω => (SOut ω, T ω)) =
        (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
          (ProbComp.eval (S {0} (restrictZero (eQ0 x0))
              (restrictZero (F := (batchOTSpec k Bool).Answer ()) ()))).map
            fun v0 => (sOf x0, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)) := by
      have h1 : real.map (fun ω => (SOut ω, T ω)) =
          (real.map fun ω => ((SOut ω, T ω), rotChoices (ROut ω))).map Prod.fst := by
        rw [PMF.map_comp]
        rfl
      rw [h1, hMain, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def]
      have hmc : ∀ a : (Fin k → Bool × Bool) × PublicTranscript sc,
          PMF.map (fun _ : Fin k → Bool => a) (PMF.uniformOfFintype (Fin k → Bool)) = PMF.pure a :=
        fun a => PMF.map_const _ a
      simp only [hmc]
      exact PMF.bind_pure _
    rw [hMain, hMarg]
  have hBobPriv : real.map (fun ω => ((T ω, ROut ω), rotUnselected (SOut ω) (ROut ω))) =
      (real.map fun ω => (T ω, ROut ω)).bind fun tr =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·) := by
    have hStep1 : ∀ (x1 : Fin k → Bool) (y1 u : Fin k → Bool),
        let x0 := otPairEquiv x1 (y1, u)
        (realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
          (fun ω => ((T ω, ROut ω), rotUnselected (SOut ω) (ROut ω))) =
        (ProbComp.eval (S {1} (restrictOne (eQ1 x1)) (restrictOne (eA1 y1)))).map fun v1 =>
          ((transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩),
            fun j => (x1 j, y1 j)), u) := by
      intro x1 y1 u x0
      have hLHS : (realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
          (fun ω => ((T ω, ROut ω), rotUnselected (SOut ω) (ROut ω))) =
          ((realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))).map
            (Prod.map ({1} : Finset (Fin 2)).restrict id)).map
            (fun (v1, y) => ((transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩),
              fun j => (x1 j, y 1 j)), u)) := by
        rw [PMF.map_comp]
        refine map_congr_on_support _ _ _ fun ⟨views, out⟩ hω => ?_
        obtain ⟨hin0, hin1⟩ := hInOfSupport (eQ0 x0) (eQ1 x1) hω
        have h01 : transcriptOfView proto 0 (views 0) = transcriptOfView proto 1 (views 1) := by
          rw [realCorrelatedWithInput, PMF.mem_support_bind_iff] at hω
          obtain ⟨_, _, hev⟩ := hω
          exact transcriptOfView_zero_eq_one proto hev
        refine Prod.ext (Prod.ext h01 (funext fun j => ?_)) (funext fun j => ?_)
        · dsimp only [Function.comp_def, Prod.map_apply, id_eq, ROut]
          rw [hin1]
          rfl
        · dsimp only [Function.comp_def, Prod.map_apply, id_eq, rotUnselected, SOut, ROut]
          rw [hin0, hin1, heQ0, heQ0, heQ1]
          cases hx : x1 j
          · simp only [hx, Bool.not_false, otSelect_true, x0, otPairEquiv, Equiv.coe_fn_mk]
            rfl
          · simp only [hx, Bool.not_true, otSelect_false, x0, otPairEquiv, Equiv.coe_fn_mk]
            rfl
      rw [hLHS, ← hPriv1, eval_idealJoint, batchOTFunctionality, Functionality.ofDeterministic]
      simp only [ProbComp.eval_pure, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      have hrest : ({1} : Finset (Fin 2)).restrict
          (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1)) =
          restrictOne (eQ1 x1) := restrictOne_pairVec _ _
      have hy1 : ∀ j : Fin k,
          batchOTAnswer (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1)) 1 j =
            y1 j := by
        intro j
        change x0 j (x1 j) = y1 j
        dsimp only [x0, otPairEquiv, Equiv.coe_fn_mk]
        simp only [beq_self_eq_true, ↓reduceIte]
      have hresty : ({1} : Finset (Fin 2)).restrict
          (batchOTAnswer (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1))) =
          restrictOne (eA1 y1) := by
        funext ⟨i, hi⟩
        obtain rfl := Finset.mem_singleton.mp hi
        funext j
        exact hy1 j
      rw [hrest, hresty]
      congr 1 with v1 : 1
      refine Prod.ext (Prod.ext rfl (funext fun j => Prod.ext rfl (hy1 j))) rfl
    have hMain : real.map (fun ω => ((T ω, ROut ω), rotUnselected (SOut ω) (ROut ω))) =
        ((PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
          (PMF.uniformOfFintype (Fin k → Bool)).bind fun y1 =>
            (ProbComp.eval (S {1} (restrictOne (eQ1 x1)) (restrictOne (eA1 y1)))).map fun v1 =>
              (transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩),
                fun j => (x1 j, y1 j))).bind
          fun tr => (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·) := by
      rw [hRealUnif]
      simp only [PMF.map_bind, PMF.bind_bind]
      conv_lhs => rw [PMF.bind_comm]
      congr 1 with x1 : 1
      rw [← uniformOfFintype_map_equiv (otPairEquiv x1), PMF.bind_map, ← uniformOfFintype_prod,
        PMF.bind_bind]
      simp only [PMF.bind_map]
      congr 1 with y1 : 1
      dsimp only [Function.comp_def]
      simp only [hStep1 x1 y1]
      simp only [← PMF.bind_pure_comp, Function.comp_def]
      exact PMF.bind_comm _ _ _
    have hMarg : real.map (fun ω => (T ω, ROut ω)) =
        (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
          (PMF.uniformOfFintype (Fin k → Bool)).bind fun y1 =>
            (ProbComp.eval (S {1} (restrictOne (eQ1 x1)) (restrictOne (eA1 y1)))).map fun v1 =>
              (transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩),
                fun j => (x1 j, y1 j)) := by
      have h1 : real.map (fun ω => (T ω, ROut ω)) =
          (real.map fun ω => ((T ω, ROut ω), rotUnselected (SOut ω) (ROut ω))).map Prod.fst := by
        rw [PMF.map_comp]
        rfl
      rw [h1, hMain, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def]
      have hmc : ∀ a : PublicTranscript sc × (Fin k → Bool × Bool),
          PMF.map (fun _ : Fin k → Bool => a) (PMF.uniformOfFintype (Fin k → Bool)) = PMF.pure a :=
        fun a => PMF.map_const _ a
      simp only [hmc]
      exact PMF.bind_pure _
    rw [hMain, hMarg]
  have hInputEq : real.map (fun ω => ((ω.1 0).input, (ω.1 1).input)) = inputDist :=
    (bind_evalWith_map_input proto inputDist (fun xy => pairVec xy.1 xy.2) id id).trans
      (PMF.map_id inputDist)
  have hMutualEq : mutualInfo inputDist = mutualInfo source := by
    let swap0 : In 0 ≃ A × (Fin k → Bool → Bool) :=
      { toFun := fun (x0, a) => (eA.symm a, eQ0.symm x0)
        invFun := fun (a, x0) => (eQ0 x0, eA a)
        left_inv := fun (_, _) => rfl
        right_inv := fun (_, _) => rfl }
    let swap1 : In 1 ≃ B × (Fin k → Bool) :=
      { toFun := fun (x1, b) => (eB.symm b, eQ1.symm x1)
        invFun := fun (b, x1) => (eQ1 x1, eB b)
        left_inv := fun (_, _) => rfl
        right_inv := fun (_, _) => rfl }
    let rawDist := source.bind fun ab =>
      (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
        (PMF.uniformOfFintype (Fin k → Bool)).map fun x1 => ((ab.1, x0), (ab.2, x1))
    have hRaw : rawDist = inputDist.map (Prod.map swap0 swap1) := by
      dsimp only [rawDist, inputDist]
      rw [PMF.map_bind]
      congr 1 with ab : 1
      rw [PMF.map_bind]
      congr 1 with x0 : 1
      rw [PMF.map_comp]
      rfl
    have hMI : mutualInfo rawDist = mutualInfo inputDist := by
      have hid : inputDist.map (fun p => (p.1, p.2)) = inputDist := PMF.map_id _
      have hRaw' : rawDist = inputDist.map (fun p => (swap0 p.1, swap1 p.2)) := hRaw
      rw [hRaw', ← hid, mutualInfo_map, mutualInfo_map, hid]
      rw [entropy_map_eq_of_comp inputDist (F := Prod.fst) (e := swap0) swap0.injective
          (fun _ _ => rfl),
        entropy_map_eq_of_comp inputDist (F := Prod.snd) (e := swap1) swap1.injective
          (fun _ _ => rfl),
        entropy_map_eq_of_comp inputDist (F := id)
          (G := fun p => (swap0 p.1, swap1 p.2))
          (e := Prod.map swap0 swap1) (swap0.injective.prodMap swap1.injective)
          (fun _ _ => rfl),
        PMF.map_id]
    rw [← hMI]
    exact mutualInfo_bind_pair_indep source _ _
  calc (k : ℝ)
      ≤ mutualInfo (real.map fun ω => ((ω.1 0).input, (ω.1 1).input)) := by
        refine natCast_le_mutualInfo_of_rot real (fun ω => (ω.1 0).input) (fun ω => (ω.1 1).input)
          VA VB T SOut ROut ?_ outA hOutA outB hOutB hCorrect hAlicePriv hBobPriv
        rw [hInputEq]
        exact condMutualInfo_transcript_le_mutualInfo_input proto inputDist
    _ = mutualInfo inputDist := by rw [hInputEq]
    _ = mutualInfo source := hMutualEq

end ChosenInputOT

/-! ### Adaptive binary communication trees over correlated randomness -/

section CommunicationTrees

variable {X Y A B Z : Type*}

/-- **Ahlswede–Csiszár-style upper bound for binary communication trees**:
any `Cslib.Communication.Protocol` over joint source `μ : PMF (X × Y)` whose leaf-determined
outputs form `k` independent, correct, and perfectly private random OTs satisfies
`(k : ℝ) ≤ I(X; Y)`. -/
theorem commProtocol_rot_le_mutualInfo [Finite X] [Finite Y] {k : ℕ}
    (p : Cslib.Communication.Protocol X Y Z) (μ : PMF (X × Y))
    (outA : X × Fin p.leafCount → Fin k → Bool × Bool)
    (outB : Y × Fin p.leafCount → Fin k → Bool × Bool)
    (hCorrect : ∀ x y j, (x, y) ∈ μ.support →
      (outB (y, p.leaf x y) j).2 = otSelect (outA (x, p.leaf x y) j) (outB (y, p.leaf x y) j).1)
    (hAlicePriv : (p.transcriptLaw μ).map
        (fun q => ((outA (q.1, Prod.snd q.2), Prod.snd q.2),
          rotChoices (outB (Prod.fst q.2, Prod.snd q.2)))) =
      ((p.transcriptLaw μ).map fun q => (outA (q.1, Prod.snd q.2), Prod.snd q.2)).bind fun st =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·))
    (hBobPriv : (p.transcriptLaw μ).map
        (fun q => ((Prod.snd q.2, outB (Prod.fst q.2, Prod.snd q.2)),
          rotUnselected (outA (q.1, Prod.snd q.2)) (outB (Prod.fst q.2, Prod.snd q.2)))) =
      ((p.transcriptLaw μ).map fun q =>
          (Prod.snd q.2, outB (Prod.fst q.2, Prod.snd q.2))).bind fun tr =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·)) :
    (k : ℝ) ≤ mutualInfo μ := by
  let ν := p.transcriptLaw μ
  have hTrLaw : p.transcriptLaw μ = PMF.map (fun q => (q.1, q.2, p.leaf q.1 q.2)) μ :=
    Cslib.Communication.Protocol.transcriptLaw_eq p μ
  have hSupp : ∀ ω ∈ ν.support, ω.2.2 = p.leaf ω.1 ω.2.1 ∧ (ω.1, ω.2.1) ∈ μ.support := by
    intro ⟨x, y, t⟩ hω
    dsimp only [ν] at hω
    rw [hTrLaw, PMF.mem_support_map_iff] at hω
    obtain ⟨⟨x', y'⟩, hxy, heq⟩ := hω
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, hxy⟩
  have hCorr' : ∀ ω ∈ ν.support, ∀ j : Fin k,
      (outB (ω.2.1, ω.2.2) j).2 = otSelect (outA (ω.1, ω.2.2) j) (outB (ω.2.1, ω.2.2) j).1 := by
    intro ⟨x, y, t⟩ hω j
    obtain ⟨ht, hxy⟩ := hSupp (x, y, t) hω
    rw [ht]
    exact hCorrect x y j hxy
  have hMu : ν.map (fun q => (q.1, q.2.1)) = μ := by
    dsimp only [ν]
    rw [hTrLaw, PMF.map_comp]
    exact PMF.map_id μ
  have hInfo : condMutualInfo (ν.map fun q => (q.2.2, (q.1, q.2.2), (q.2.1, q.2.2))) ≤
      mutualInfo (ν.map fun q => (q.1, q.2.1)) := by
    have hStrip : condMutualInfo (ν.map fun q => (q.2.2, (q.1, q.2.2), (q.2.1, q.2.2))) =
        condMutualInfo (ν.map fun q => (q.2.2, q.1, q.2.1)) :=
      condMutualInfo_map_pair_self ν (fun q => q.2.2) Prod.fst (fun q => q.2.1)
    have htr1 : (fun q : X × Y × Fin p.leafCount => (q.2.2, q.1, q.2.1)) =
        fun (x, y, t) => (t, x, y) := funext fun ⟨_, _, _⟩ => rfl
    have htr2 : (fun q : X × Y × Fin p.leafCount => (q.1, q.2.1)) =
        fun (x, y, _) => (x, y) := funext fun ⟨_, _, _⟩ => rfl
    rw [hStrip, htr1, htr2]
    exact condMutualInfo_le_mutualInfo_of_internal_le_external ν
      (p.internalInfoCost_le_externalInfoCost μ)
  rw [← hMu]
  exact natCast_le_mutualInfo_of_rot ν Prod.fst (fun q => q.2.1)
    (fun q => (q.1, q.2.2)) (fun q => (q.2.1, q.2.2)) (fun q => q.2.2)
    (fun q => outA (q.1, q.2.2)) (fun q => outB (q.2.1, q.2.2))
    hInfo outA (fun _ _ => rfl) outB (fun _ _ => rfl) hCorr' hAlicePriv hBobPriv

/-- **Ahlswede–Csiszár-style upper bound for private-coin binary communication protocols** over
correlated source `source : PMF (A × B)`. -/
theorem privateCoin_rot_le_mutualInfo [Finite A] [Finite B] {a b k : ℕ}
    (P : Cslib.Communication.PrivateCoin a b A B Z) (source : PMF (A × B))
    (outA : (A × BitString a) × Fin P.leafCount → Fin k → Bool × Bool)
    (outB : (B × BitString b) × Fin P.leafCount → Fin k → Bool × Bool)
    (hCorrect : ∀ u v j, (u.1, v.1) ∈ source.support →
      (outB (v, P.leaf u v) j).2 = otSelect (outA (u, P.leaf u v) j) (outB (v, P.leaf u v) j).1)
    (hAlicePriv : (Cslib.Communication.Protocol.transcriptLaw P
        (Cslib.Communication.PrivateCoin.inputLaw a b source)).map
        (fun q => ((outA (q.1, Prod.snd q.2), Prod.snd q.2),
          rotChoices (outB (Prod.fst q.2, Prod.snd q.2)))) =
      ((Cslib.Communication.Protocol.transcriptLaw P
          (Cslib.Communication.PrivateCoin.inputLaw a b source)).map
          fun q => (outA (q.1, Prod.snd q.2), Prod.snd q.2)).bind fun st =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·))
    (hBobPriv : (Cslib.Communication.Protocol.transcriptLaw P
        (Cslib.Communication.PrivateCoin.inputLaw a b source)).map
        (fun q => ((Prod.snd q.2, outB (Prod.fst q.2, Prod.snd q.2)),
          rotUnselected (outA (q.1, Prod.snd q.2)) (outB (Prod.fst q.2, Prod.snd q.2)))) =
      ((Cslib.Communication.Protocol.transcriptLaw P
          (Cslib.Communication.PrivateCoin.inputLaw a b source)).map
          fun q => (Prod.snd q.2, outB (Prod.fst q.2, Prod.snd q.2))).bind fun tr =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·)) :
    (k : ℝ) ≤ mutualInfo source := by
  let μ := Cslib.Communication.PrivateCoin.inputLaw a b source
  have hMu : μ = source.bind fun ab =>
      (PMF.uniformOfFintype (BitString a)).bind fun ra =>
        (PMF.uniformOfFintype (BitString b)).map fun rb => ((ab.1, ra), (ab.2, rb)) := by
    refine PMF.ext fun ((x, r), (y, r')) => ?_
    dsimp only [μ]
    rw [Cslib.Communication.PrivateCoin.inputLaw_apply, PMF.bind_apply]
    have hPairMap : ∀ ab : A × B,
        ((PMF.uniformOfFintype (BitString a)).bind fun ra =>
          (PMF.uniformOfFintype (BitString b)).map fun rb => ((ab.1, ra), (ab.2, rb))) =
        (PMF.uniformOfFintype (BitString a × BitString b)).map
          fun rr => ((ab.1, rr.1), (ab.2, rr.2)) := by
      intro ab
      rw [← uniformOfFintype_prod, PMF.map_bind]
      congr 1 with ra : 1
      rw [PMF.map_comp]
      rfl
    simp_rw [hPairMap]
    have htsum : (∑' ab : A × B, source ab *
          ((PMF.uniformOfFintype (BitString a × BitString b)).map
            fun rr => ((ab.1, rr.1), (ab.2, rr.2))) ((x, r), (y, r'))) =
        source (x, y) *
          ((PMF.uniformOfFintype (BitString a × BitString b)).map
            fun rr => ((x, rr.1), (y, rr.2))) ((x, r), (y, r')) := by
      refine tsum_eq_single (x, y) fun ab hab => ?_
      have hzero : ((PMF.uniformOfFintype (BitString a × BitString b)).map
            fun rr => ((ab.1, rr.1), (ab.2, rr.2))) ((x, r), (y, r')) = 0 := by
        by_contra hne
        have hmem : ((x, r), (y, r')) ∈
            ((PMF.uniformOfFintype (BitString a × BitString b)).map
              fun rr => ((ab.1, rr.1), (ab.2, rr.2))).support := hne
        rw [PMF.mem_support_map_iff] at hmem
        obtain ⟨rr, _, h⟩ := hmem
        simp only [Prod.mk.injEq] at h
        exact hab (Prod.ext h.1.1 h.2.1)
      rw [hzero, mul_zero]
    rw [htsum, PMF.map_apply, tsum_eq_single (r, r')]
    · split_ifs with h
      · rw [uniformOfFintype_apply]
      · exact False.elim (h rfl)
    · intro rr hrr
      split_ifs with h
      · simp only [Prod.mk.injEq] at h
        exact False.elim (hrr (Prod.ext h.1.2.symm h.2.2.symm))
      · rfl
  have hCorr' : ∀ u v j, (u, v) ∈ μ.support →
      (outB (v, P.leaf u v) j).2 =
        otSelect (outA (u, P.leaf u v) j) (outB (v, P.leaf u v) j).1 := by
    intro u v j huv
    rw [hMu, PMF.mem_support_bind_iff] at huv
    obtain ⟨⟨x, y⟩, hxy, huv⟩ := huv
    rw [PMF.mem_support_bind_iff] at huv
    obtain ⟨ra, _, huv⟩ := huv
    rw [PMF.mem_support_map_iff] at huv
    obtain ⟨rb, _, heq⟩ := huv
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact hCorrect (x, ra) (y, rb) j hxy
  have hBound := commProtocol_rot_le_mutualInfo P μ outA outB hCorr' hAlicePriv hBobPriv
  rw [hMu, mutualInfo_bind_pair_indep] at hBound
  exact hBound

end CommunicationTrees

end Cslib.Crypto.Protocols.OT
