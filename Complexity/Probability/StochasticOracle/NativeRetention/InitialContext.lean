/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.NativeRetention.Packets
public import Complexity.Computability.Probabilistic.NativeContextLoader
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Tactic

/-!
# Original-input initialization of native selector context

The actual encoded input contains rational incidence data and startup allowances,
not a precomputed context or native execution witness. Native code constructs the
header, ignores caller-supplied proposals when computing initial completion, and
loads the reserved tape before the existing two-query runtime transport program.
Its supported scheduler still submits raw original/context words: source batch
admission, semantic post-response control updates and repeated selection/stopping
remain open. This is initialization for [Wang2027], model pp. 4--6/Theorem 5 p. 12,
not the complete source upper policy or a conventional external PTM encoding.

## Main definitions

* `Startup`, `encoding`: original instance and runtime startup metadata.
* `initialDecision`, `header`, `context`: computed empty-history initial control data.

## Main results

* `exists_original_input_runtime`: a constructed blank-tape native machine for all inputs.
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

private theorem fields : ComputableInPolyTime
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

private theorem computable_context : ComputableInPolyTime context encoding encBits := by
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
  have hh : ComputableInPolyTime header encoding encHeader := hh0
  have hb : ComputableInPolyTime Header.encode encHeader encBits := .of_eq fun _ => rfl
  exact ComputableInPolyTime.frame.comp (hb.comp hh)

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

end Cslib.Probability.StochasticOracle.NativeRetention.InitialContext
