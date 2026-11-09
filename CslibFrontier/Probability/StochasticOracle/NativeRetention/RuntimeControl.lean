/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.InitialContext
public import CslibFrontier.Computability.Probabilistic.NativeReplyContext
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Tactic

/-!
# Uniform post-response semantic control computation

The runtime data contain the original rational instance and stored raw history,
private word and remaining turn/opportunity/allotment counts. A concrete pure
algorithm updates all fields and recomputes local retention and completion from
the received report. Its native realization writes an actual guard packet back
to reserved tape zero, clearing local workspace. No context is compiled into code.

Requests in this transport phase are framed runtime-state bytes, not the source
concurrent-batch codec. Allotments are integral policy reservations, not observed real
latency. Connecting this phase to a repeated source-admitted native selector,
external clock interfaces and Theorem 5's quantitative upper endpoint remains open.
The phase frontend always issues one query; it does not execute an initial or
post-response guard. Old history supplied as input is not authenticated by this
phase, so a repeated execution still needs a history/oracle-ledger invariant.
The decremented opportunity counter is a planning allowance, not a proved source
used-opportunity ledger for arbitrary concurrent batches.
The source conventions are [Wang2027], model pp. 4--6, Theorem 5 p. 12/App. A.5 p. 16.

## Main definitions

* `State`, `initial`, `afterReply`: actual runtime data and the concrete control update.
* `stopped`, `result`, `packet`: recomputed control and retained-output framing.
* `HistoryMatches`: raw histories/private bytes agree with actual native events.

## Main results

* `exists_native_processor`: uniform runtime-context update with local cleanup.
* `exists_native_phase`: actual blank-tape query/read/update law.
* `afterReply_history_matches`: the actual transport request preserves raw history.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.RuntimeControl
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRuntimeContext

/-- Runtime control for the supported deterministic append-private-word controller.
Each completed transaction consumes one turn, opportunity and reserved allotment.
This is not a compiler for arbitrary `Selector.Scheduler` functions. -/
structure State where
  /-- Original input, total opportunity count and stored raw replies, newest first. -/
  work : Packets.Work
  /-- Actually submitted raw requests, newest first. -/
  requests : List (List Bool)
  /-- Private seed followed by framed visible replies. -/
  privateWord : List Bool
  /-- Remaining transaction budget. -/
  turns : ℕ
  /-- Remaining one-opportunity planning allowances.
  No source admission invariant is asserted. -/
  opportunities : ℕ
  /-- Remaining uniform latency allotments, rather than measured real time. -/
  allotments : ℕ
  deriving DecidableEq

/-- Every runtime field occurs in the data encoding. -/
@[expose] def encoding : State ↪ List Bool :=
  ⟨fun s => encPair Packets.encWork (encPair (encList encBits)
      (encPair encBits (encPair encUnary (encPair encUnary encUnary))))
      (s.work, s.requests, s.privateWord, s.turns, s.opportunities, s.allotments), by
    intro a b h
    have he := (encPair Packets.encWork (encPair (encList encBits)
      (encPair encBits (encPair encUnary (encPair encUnary encUnary))))).injective h
    cases a; cases b; cases he; rfl⟩

/-- Initialization ignores any caller-supplied proposals and installs no old replies
or requests. The allotment count is an explicit reservation budget. -/
@[expose] def initial (data : InitialContext.Startup) (allotments : ℕ) : State :=
  ⟨⟨data.system, data.opportunities, []⟩, [], data.privateSelector,
    data.turns, data.opportunities, allotments⟩

/-- Semantic update after one actual full reply. The raw request of this supported
transport ABI is the framed encoding of the old runtime state. -/
@[expose] def afterReply (state : State) (reply : List Bool) : State :=
  ⟨{ state.work with history := reply :: state.work.history },
    frame (encoding state) :: state.requests, state.privateWord ++ frame reply,
    state.turns - 1, state.opportunities - 1, state.allotments - 1⟩

/-- Stop on computed completion or any exhausted policy budget. -/
@[expose] def stopped (state : State) : Bool :=
  decide (state.turns = 0) || decide (state.opportunities = 0) ||
    decide (state.allotments = 0) || (Packets.decision state.work).1

/-- Emit only the mask computed by actual raw-history retention on completion. -/
@[expose] def result (state : State) : List Bool :=
  if (Packets.decision state.work).1 then (Packets.decision state.work).2 else []

/-- Native guard layout: updated stopping bit, framed certified-output candidate,
and the complete updated runtime state. -/
@[expose] def packet (state : State) : List Bool :=
  NativeStopGuard.packet (stopped state) (result state) (frame (encoding state))

/-- The same algorithm handles every runtime context and arbitrary complete reply. -/
@[expose] def process (input : State × List Bool) : List Bool :=
  packet (afterReply input.1 input.2)

/-- Authenticate both stored public histories and the append controller's private
word against actual native events. This does not certify source batch admission. -/
@[expose] def HistoryMatches (seed : List Bool) (state : State)
    (events : List (Event Unit)) : Prop :=
  state.work.history = events.map (fun e => e.reply.word) ∧
    state.requests = events.map (fun e => e.request) ∧
      state.privateWord = seed ++ events.reverse.flatMap (fun e => frame e.reply.word)

/-- Original-input initialization creates no fabricated event history. -/
theorem initial_history_matches (data : InitialContext.Startup) (allotments : ℕ) :
    HistoryMatches data.privateSelector (initial data allotments) [] := by
  simp [HistoryMatches, initial]

/-- The concrete updater preserves authenticated history after the request it
actually uses in this transport ABI. The new reply is not a supplied decoded family. -/
theorem afterReply_history_matches {P : Type} (seed : List Bool) (state : State)
    (memory : Memory Unit P) (reply : Reply) (next : P)
    (h : HistoryMatches seed state memory.events) :
    HistoryMatches seed (afterReply state reply.word)
      (memory.record ((), frame (encoding state)) reply next).events := by
  obtain ⟨hh, hreq, hp⟩ := h
  simp [HistoryMatches, afterReply, Memory.record, hh, hreq, hp,
    List.reverse_cons, List.flatMap_append, List.append_assoc]

private theorem fields : ComputableInPolyTime
    (fun s : State => (s.work, s.requests, s.privateWord, s.turns, s.opportunities, s.allotments))
    encoding (encPair Packets.encWork (encPair (encList encBits)
      (encPair encBits (encPair encUnary (encPair encUnary encUnary))))) := .of_eq fun _ => rfl

private abbrev inputEncoding := encPair encoding NativeReplyContext.framedBits

private theorem reply_computable :
    ComputableInPolyTime (fun p : State × List Bool => p.2) inputEncoding encBits := by
  have he : ComputableInPolyTime (fun w : List Bool => frame w)
      NativeReplyContext.framedBits encBits := .of_eq fun _ => rfl
  have hr := ComputableInPolyTime.unframe.comp
    (he.comp (ComputableInPolyTime.snd encoding NativeReplyContext.framedBits))
  simpa only [Function.comp_def, unframe_frame] using hr

private theorem input_fields : ComputableInPolyTime
    (fun p : State × List Bool =>
      (p.1.work, p.1.requests, p.1.privateWord, p.1.turns, p.1.opportunities, p.1.allotments))
    inputEncoding (encPair Packets.encWork (encPair (encList encBits)
      (encPair encBits (encPair encUnary (encPair encUnary encUnary))))) :=
  fields.comp (ComputableInPolyTime.fst encoding NativeReplyContext.framedBits)

private theorem updated_work_computable : ComputableInPolyTime
    (fun p : State × List Bool => { p.1.work with history := p.2 :: p.1.work.history })
    inputEncoding Packets.encWork := by
  have hw : ComputableInPolyTime
      (fun p : State × List Bool =>
        (p.1.work.system, p.1.work.opportunities, p.1.work.history))
      inputEncoding (encPair encInput (encPair encUnary (encList encBits))) :=
    Packets.work_fields.comp input_fields.fst'
  have hh : ComputableInPolyTime
      (fun p : State × List Bool => p.2 :: p.1.work.history)
      inputEncoding (encList encBits) :=
    ComputableInPolyTime.cons' reply_computable hw.snd'.snd'
  have hpack : ComputableInPolyTime
      (fun p : NativeRetention.Input × ℕ × List (List Bool) =>
        Packets.Work.mk p.1 p.2.1 p.2.2)
      (encPair encInput (encPair encUnary (encList encBits))) Packets.encWork :=
    .of_eq fun _ => rfl
  have hout := hpack.comp (hw.fst'.prod (hw.snd'.fst'.prod hh))
  exact hout

private theorem computable_afterReply : ComputableInPolyTime
    (fun p : State × List Bool => afterReply p.1 p.2)
    (encPair encoding NativeReplyContext.framedBits) encoding := by
  have hs := ComputableInPolyTime.fst encoding NativeReplyContext.framedBits
  have hf := input_fields
  have hreply := reply_computable
  have hnewwork := updated_work_computable
  have he : ComputableInPolyTime (fun s : State => encoding s) encoding encBits :=
    .of_eq fun _ => rfl
  have hrequest := ComputableInPolyTime.frame.comp (he.comp hs)
  have hrequests := ComputableInPolyTime.cons' hrequest hf.snd'.fst'
  have hp := (ComputableInPolyTime.frame.comp hreply).prod hf.snd'.snd'.fst'
  have hconcat : ComputableInPolyTime (fun p : List Bool × List Bool => p.2 ++ p.1)
      (encPair encBits encBits) encBits := by
    exact ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.snd encBits encBits) (ComputableInPolyTime.fst encBits encBits)
  have hprivate := hconcat.comp hp
  have hpred := ComputableInPolyTime.unary_sub
  have ht := hpred.comp (hf.snd'.snd'.snd'.fst'.prod (ComputableInPolyTime.const 1))
  have ho := hpred.comp (hf.snd'.snd'.snd'.snd'.fst'.prod (ComputableInPolyTime.const 1))
  have ha := hpred.comp (hf.snd'.snd'.snd'.snd'.snd'.prod (ComputableInPolyTime.const 1))
  have hpack : ComputableInPolyTime
      (fun p : Packets.Work × List (List Bool) × List Bool × ℕ × ℕ × ℕ =>
        State.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (encPair Packets.encWork (encPair (encList encBits)
        (encPair encBits (encPair encUnary (encPair encUnary encUnary))))) encoding :=
    .of_eq fun _ => rfl
  have hout := hpack.comp (hnewwork.prod (hrequests.prod (hprivate.prod (ht.prod (ho.prod ha)))))
  exact hout

/-- The actual recomputed guard packet is uniformly computable from runtime data. -/
theorem computable_packet : ComputableInPolyTime packet encoding encBits := by
  have hd := Packets.computable_decision.comp fields.fst'
  have ht := ComputableInPolyTime.unary_le' fields.snd'.snd'.snd'.fst'
    (ComputableInPolyTime.const 0)
  have ho := ComputableInPolyTime.unary_le' fields.snd'.snd'.snd'.snd'.fst'
    (ComputableInPolyTime.const 0)
  have ha := ComputableInPolyTime.unary_le' fields.snd'.snd'.snd'.snd'.snd'
    (ComputableInPolyTime.const 0)
  have hstop := ComputableInPolyTime.bool_or.comp
    ((ComputableInPolyTime.bool_or.comp
      ((ComputableInPolyTime.bool_or.comp (ht.prod ho)).prod ha)).prod hd.fst')
  have hout := ComputableInPolyTime.ite hd.fst' hd.snd'
    (ComputableInPolyTime.const ([] : List Bool))
  have he : ComputableInPolyTime (fun s : State => encoding s) encoding encBits :=
    .of_eq fun _ => rfl
  have hdata := ComputableInPolyTime.frame.comp he
  have htail : ComputableInPolyTime (fun p : List Bool × List Bool => frame p.1 ++ p.2)
      (encPair encBits encBits) encBits := .of_eq fun _ => rfl
  have hall := ComputableInPolyTime.bitsCons hstop (htail.comp (hout.prod hdata))
  convert hall using 1
  funext state
  simp [packet, NativeStopGuard.packet, stopped, result]


/-- Pure computation is derived from actual parsing, rational retention and explicit
counter/private-word updates. No native execution or desired success law is assumed. -/
theorem computable_process : ComputableInPolyTime process
    (encPair encoding NativeReplyContext.framedBits) encBits :=
  computable_packet.comp computable_afterReply

/-- One finite native program updates the actual runtime tape for every old state
and every full reply, and clears its local scratch/input/flag storage. -/
theorem exists_native_processor :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (code : MultiTapeTM (3 + k) Bool S),
      ∀ (state : State) (reply : List Bool), ∃ time space : ℕ,
        TransformsTapes code
          (fun input ws => input = reply ∧
            ws = Function.update (fun _ => []) 0 (frame (encoding state)))
          (fun _ _ ws' emitted =>
            ws' = Function.update (fun _ => []) 0 (process (state, reply)) ∧ emitted = [])
          time space := NativeReplyContext.exists_processor encoding process computable_process

/-- Actual blank-tape query/reader/runtime-update execution. The program is fixed
before quantifying over runtime states and correlated environments; it assumes no
prepared context or native representation law. It terminates this single local
phase with a guard packet on tape zero, rather than executing the feedback loop. -/
theorem exists_native_phase :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (program : MultiTapePTM ((3 + k) + 2) Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (state : State) (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal program env
          ⟨program.initialConfig (frame (encoding state)), memory⟩).map
          (Option.map (NativeReplyContext.observe 0)) =
          (env ((), frame (encoding state)) memory).map fun (reply, next) =>
            some (⟨tapeOfList (process (state, reply.word)), [],
              memory.record ((), frame (encoding state)) reply next⟩ :
                NativeReplyContext.Observation P) :=
  NativeReplyContext.exists_query_processor encoding process computable_process

end Cslib.Probability.StochasticOracle.NativeRetention.RuntimeControl
