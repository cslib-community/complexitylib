/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Packets
public import CslibFrontier.Computability.Probabilistic.NativeStopGuard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Tactic

/-!
# Original-input initialization of native selector context

The actual encoded input contains rational incidence data and startup allowances,
not a precomputed context or native execution witness. Native code constructs the
header, ignores caller-supplied proposals when computing initial completion, and
loads the reserved tape before native dispatch. The guarded entry emits the computed
initial output without any query when the initial stop flag is true; otherwise it
enters the existing two-query runtime transport program.
Its supported scheduler still submits raw original/context words: source batch
admission, semantic post-response control updates and repeated selection/stopping
remain open. This is initialization for [Wang2027], model pp. 4--6/Theorem 5 p. 12,
not the complete source upper policy or a conventional external PTM encoding.

## Main definitions

* `Startup`, `encoding`: original instance and runtime startup metadata.
* `initialDecision`, `header`, `context`: computed empty-history initial control data.
* `guardedContext`: the initial dispatch flag, framed output and retained header.

## Main results

* `exists_original_input_runtime`: the original unconditional raw two-query carrier.
* `exists_guarded_original_input`: blank-tape initialization with actual initial stopping.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.InitialContext
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRuntimeContext

/-- Original rational instance plus runtime startup metadata; no context is supplied. -/
structure Startup where
  /-- Original rows, weights and dual-price data; validity is a separate promise.
  Initial proposals are ignored. -/
  system : NativeRetention.Input
  /-- Runtime turn allowance. -/
  turns : ℕ
  /-- Runtime number of labeled opportunities. -/
  opportunities : ℕ
  /-- Initial private selector word. -/
  privateSelector : ConcurrentBatch.Word
  deriving DecidableEq

/-- Concrete instance/startup ABI. Counters are unary and rational data use `encInput`. -/
@[expose] def encoding : Startup ↪ List Bool :=
  ⟨fun data => encPair encInput (encPair encUnary (encPair encUnary encBits))
    (data.system, data.turns, data.opportunities, data.privateSelector), by
    intro a b h
    have he := (encPair encInput (encPair encUnary (encPair encUnary encBits))).injective h
    cases a
    cases b
    cases he
    rfl⟩

/-- Initial local decision uses no externally proposed candidates. -/
@[expose] def initialDecision (data : Startup) : Bool × List Bool :=
  Packets.decision ⟨data.system, data.opportunities, []⟩

/-- Construct actual initial control data from the original instance and allowances.
The stop bit also records no available turn/opportunity; later raw transport code
is not claimed to obey that bit. -/
@[expose] def header (data : Startup) : Header :=
  { originalInstance := encInput data.system
    requests := []
    replies := []
    privateSelector := data.privateSelector
    remainingTurns := data.turns
    opportunities := encUnary data.opportunities
    stopped := decide (data.turns ≤ 0) || decide (data.opportunities ≤ 0) ||
      (initialDecision data).1
    output := if (initialDecision data).1 then (initialDecision data).2 else [] }

/-- The context word is computed by the initializer, not encoded in its input. -/
@[expose] def context (data : Startup) : List Bool := (header data).initialWord

/-- Read the original input and startup allowances through the canonical encoding. -/
theorem fields : ComputableInPolyTime
    (fun data : Startup => (data.system, data.turns, data.opportunities, data.privateSelector))
    encoding (encPair encInput (encPair encUnary (encPair encUnary encBits))) :=
  .of_eq fun _ => rfl

private theorem system_computable : ComputableInPolyTime Startup.system encoding encInput :=
  fields.fst'
private theorem turns_computable : ComputableInPolyTime Startup.turns encoding encUnary :=
  fields.snd'.fst'
private theorem opportunities_computable :
    ComputableInPolyTime Startup.opportunities encoding encUnary := fields.snd'.snd'.fst'
private theorem private_computable :
    ComputableInPolyTime Startup.privateSelector encoding encBits := fields.snd'.snd'.snd'

private theorem decision_computable :
    ComputableInPolyTime initialDecision encoding (encPair encBool encBits) := by
  have hp : ComputableInPolyTime
      (fun p : NativeRetention.Input × ℕ × List ConcurrentBatch.Word =>
        Packets.Work.mk p.1 p.2.1 p.2.2)
      (encPair encInput (encPair encUnary (encList encBits))) Packets.encWork :=
    .of_eq fun _ => rfl
  have hh : ComputableInPolyTime (fun _ : Startup => ([] : List ConcurrentBatch.Word))
      encoding (encList encBits) := .const []
  have htuple := system_computable.prod (opportunities_computable.prod hh)
  have hw := hp.comp htuple
  exact Packets.computable_decision.comp hw

private def encHeader : Header ↪ List Bool := ⟨Header.encode, Header.encode_injective⟩

private theorem header_computable : ComputableInPolyTime header encoding encHeader := by
  have he : ComputableInPolyTime (fun x : NativeRetention.Input => encInput x)
      encInput encBits := .of_eq fun _ => rfl
  have ho := he.comp system_computable
  have hreq : ComputableInPolyTime (fun _ : Startup => ([] : List ConcurrentBatch.Word))
      encoding (encList encBits) := .const []
  have hmask : ComputableInPolyTime (fun x : Startup => encUnary x.opportunities)
      encoding encBits :=
    (show ComputableInPolyTime (fun n : ℕ => encUnary n) encUnary encBits from
      .of_eq fun _ => rfl).comp opportunities_computable
  have ht := ComputableInPolyTime.unary_le' turns_computable
    (ComputableInPolyTime.const 0)
  have hn := ComputableInPolyTime.unary_le' opportunities_computable
    (ComputableInPolyTime.const 0)
  have hstop := ComputableInPolyTime.bool_or.comp
    ((ComputableInPolyTime.bool_or.comp (ht.prod hn)).prod decision_computable.fst')
  have hout := ComputableInPolyTime.ite decision_computable.fst' decision_computable.snd'
    (ComputableInPolyTime.const ([] : List Bool))
  have hp : ComputableInPolyTime
      (fun p : List Bool × List (List Bool) × List (List Bool) × List Bool × ℕ ×
        List Bool × Bool × List Bool =>
        Header.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
          p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)
      (encPair encBits (encPair (encList encBits) (encPair (encList encBits)
        (encPair encBits (encPair encUnary (encPair encBits (encPair encBool encBits)))))))
      encHeader := .of_eq fun _ => by
        simp [encHeader, Header.encode, List.append_assoc]
  have htuple := ho.prod (hreq.prod (hreq.prod (private_computable.prod
    (turns_computable.prod (hmask.prod (hstop.prod hout))))))
  have hh0 := hp.comp htuple
  exact hh0

private theorem computable_context : ComputableInPolyTime context encoding encBits := by
  have hb : ComputableInPolyTime Header.encode encHeader encBits := .of_eq fun _ => rfl
  exact ComputableInPolyTime.frame.comp (hb.comp header_computable)

/-- Actual native guard packet, computed from the same initial control data.
The payload retains the original header used by the raw runtime carrier. -/
@[expose] def guardedContext (data : Startup) : List Bool :=
  NativeStopGuard.packet (header data).stopped (header data).output (context data)

private theorem header_fields : ComputableInPolyTime
    (fun h : Header => (h.originalInstance, h.requests, h.replies, h.privateSelector,
      h.remainingTurns, h.opportunities, h.stopped, h.output)) encHeader
    (encPair encBits (encPair (encList encBits) (encPair (encList encBits)
      (encPair encBits (encPair encUnary (encPair encBits (encPair encBool encBits))))))) :=
  .of_eq fun _ => by simp [encHeader, Header.encode, List.append_assoc]

private theorem guarded_context_computable :
    ComputableInPolyTime guardedContext encoding encBits := by
  have hf := header_fields.comp header_computable
  have hs := hf.snd'.snd'.snd'.snd'.snd'.snd'.fst'
  have ho := hf.snd'.snd'.snd'.snd'.snd'.snd'.snd'
  have hp := ho.prod computable_context
  have he : ComputableInPolyTime (fun p : List Bool × List Bool => encPair encBits encBits p)
      (encPair encBits encBits) encBits := .of_eq fun _ => rfl
  have ht := he.comp hp
  exact ComputableInPolyTime.bitsCons hs ht

/-- A constructed native machine starts on the original encoded instance/startup
input with every work tape blank, loads its computed header, and then executes the
two actual correlated queries and inner cleanup. No preinstalled context or native
realization contract is a premise. Raw transport does not yet enforce the computed
stop flag or source batch admission. -/
theorem exists_original_input_runtime :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (machine : MultiTapePTM (4 + scratch) Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (data : Startup) (memory : Memory Unit P),
      (NativeUnboundedExecution.terminal machine env
        ⟨machine.initialConfig (encoding data), memory⟩).map
          (Option.map NativeContextLoader.observe) =
        (env ((), encoding data) memory).bind fun (first, next) =>
          let recorded := memory.record ((), encoding data) first next
          (env ((), context data ++ frame first.word) recorded).map fun (second, last) =>
            some (⟨(context data ++ frame first.word) ++ second.word,
              tapeOfList (context data ++ frame first.word), 0, fun _ => none,
              recorded.record ((), context data ++ frame first.word) second last⟩ :
                Observation P) :=
  NativeContextLoader.exists_loaded_runtime encoding context computable_context

/-- A blank-tape native program enforces the computed initial stop bit before any
oracle call. Completion, zero turn allowance and zero opportunity allowance now
halt with the computed output. The live branch is still the concrete two-query
raw carrier; no post-response stopping or source-batch admission is asserted. -/
theorem exists_guarded_original_input :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (code : MultiTapePTM (4 + scratch) Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (data : Startup) (memory : Memory Unit P),
      (NativeUnboundedExecution.terminal code env
        ⟨code.initialConfig (encoding data), memory⟩).map
          (Option.map NativeContextLoader.observe) =
        if (header data).stopped then
          PMF.pure (some (⟨(header data).output,
            tapeOfList (NativeStopGuard.packet true (header data).output (context data)),
            (1 + 2 * (header data).output.length + 1 : ℕ), fun _ => none, memory⟩ :
              Observation P))
        else
          (env ((), encoding data) memory).bind fun (first, next) =>
            let recorded := memory.record ((), encoding data) first next
            let selected := NativeStopGuard.packet false (header data).output (context data) ++
              frame first.word
            (env ((), selected) recorded).map fun (second, last) =>
              some (⟨selected ++ second.word, tapeOfList selected, 0, fun _ => none,
                recorded.record ((), selected) second last⟩ : Observation P) := by
  obtain ⟨scratch, R, hR, loader, hl⟩ :=
    NativeContextLoader.exists_load_then encoding guardedContext guarded_context_computable
  let consumer := NativeStopGuard.machine NativeRuntimeContext.restoringProgram
  let code := (MultiTapePTM.ofDeterministic loader).seq
    (consumer.extendTapes (Fin.castAddEmb scratch))
  refine ⟨scratch, _, inferInstance, code, ?_⟩
  intro P env data memory
  rw [hl, PMF.map_comp]
  trans (NativeUnboundedExecution.terminal consumer env
    (NativeContextLoader.loadedStart consumer (encoding data) (guardedContext data) memory)).map
      (Option.map NativeRuntimeContext.observe)
  · apply congrArg (fun f =>
      (NativeUnboundedExecution.terminal consumer env
        (NativeContextLoader.loadedStart consumer (encoding data)
          (guardedContext data) memory)).map f)
    funext value
    cases value with
    | none => rfl
    | some world => exact congrArg some (NativeContextLoader.observe_extend world)
  · exact NativeStopGuard.runtime_observation env (encoding data) (header data).output
      (context data) (header data).stopped memory

end Cslib.Probability.StochasticOracle.NativeRetention.InitialContext
