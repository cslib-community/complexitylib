/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Probabilistic.NativeRuntimeContext
import CslibFrontierTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Real runtime context transport across two correlated native queries

One fixed native program works for every runtime context and every first reply.
The second request is constructed from both, and the same sampled latent value
controls its invoice. These are raw interface transport clients, not certificates
of source batch admission or of a complete adaptive cover selector.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM NativeOpenExecution
open NativeRuntimeContext
namespace CslibFrontierTests.NativeRuntimeContext

private def initial (seed : ℕ) : Memory Unit ℕ := ⟨seed, []⟩

private def firstReply (seed value : ℕ) : Reply :=
  ⟨List.replicate (value + 1) (seed == 0), value + 1, 2⟩

private def secondReply (word : List Bool) (value : ℕ) : Reply :=
  ⟨word.reverse, value + 3, 5⟩

/-- A single oracle for all contexts and both queries. The first latent geometric
sample controls the second bill, and the second visible response depends on its
actual submitted request. No independent resampling occurs. -/
private def environment : Environment Unit ℕ := fun query memory =>
  if memory.events = [] then
    NativeBatchMetadata.metadata.map fun value =>
      (firstReply memory.privateState value, value)
  else PMF.pure (secondReply query.2 memory.privateState, memory.privateState)

private def outcome (request context : List Bool) (seed value : ℕ) : Observation ℕ :=
  let first := firstReply seed value
  let selected := context ++ frame first.word
  let second := secondReply selected value
  ⟨selected ++ second.word, tapeOfList selected, 0, fun _ => none,
    ((initial seed).record ((), request) first value).record ((), selected) second value⟩

/-- Exact actual law for all runtime words, not a context-specific code witness.
The updated context is readable, its head is zero, and the inner marker is erased. -/
private theorem correlated_law (request context : List Bool) (seed : ℕ) :
    (NativeUnboundedExecution.terminal restoringProgram environment
      (restoringEntry request context (initial seed))).map (Option.map observe) =
      NativeBatchMetadata.metadata.map fun value => some (outcome request context seed value) := by
  rw [restoring_program_observation]
  simp only [environment, initial, PMF.bind_map, Memory.record,
    List.cons_ne_self, ↓reduceIte, PMF.pure_map]
  rfl

/-- Every finite first-reply length occurs with positive probability in the same
native program/source. Context transport uses no finite response approximation. -/
example (request context : List Bool) (seed value : ℕ) :
    some (outcome request context seed value) ∈
      ((NativeUnboundedExecution.terminal restoringProgram environment
        (restoringEntry request context (initial seed))).map (Option.map observe)).support := by
  rw [correlated_law]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨value, NativeBatchMetadata.metadata_support value, rfl⟩

private def latestRequest (result : Observation ℕ) : Option (List Bool) :=
  result.memory.events.head?.map Event.request

/-- The second request really depends on the first reply, for one fixed code and
one fixed runtime context. -/
example (context : List Bool) :
    latestRequest (outcome [] context 0 0) ≠
      latestRequest (outcome [] context 0 1) := by
  change some (context ++ frame (firstReply 0 0).word) ≠
    some (context ++ frame (firstReply 0 1).word)
  intro he
  have hl := congrArg List.length (Option.some.inj he)
  simp [firstReply] at hl

/-- Changing the stored original context also changes the actual second request. -/
example : latestRequest (outcome [] [true] 0 0) ≠
    latestRequest (outcome [] [false] 0 0) := by decide

/-- Both correlated resource observations remain on the same actual event ledger. -/
example (request context : List Bool) (seed value : ℕ) :
    ((outcome request context seed value).memory.events.map
      fun event => event.reply.tokens).sum =
        (2 * value + 4 : ℕ) ∧
      ((outcome request context seed value).memory.events.map
        fun event => event.reply.duration).sum =
        7 := by
  simp [outcome, firstReply, secondReply, initial, Memory.record]
  norm_num
  ring

private def emptyEnvironment : Environment Unit Unit := fun _ _ => PMF.pure (⟨[], 0, 0⟩, ())

/-- Empty context, empty first/second replies and zero invoices still execute two
real queries: the second request contains the empty frame, not a fabricated reply. -/
example :
    (NativeUnboundedExecution.terminal restoringProgram emptyEnvironment
      (restoringEntry [] [] ⟨(), []⟩)).map (Option.map observe) =
      PMF.pure (some (⟨[false], tapeOfList [false], 0, fun _ => none,
        ((⟨(), []⟩ : Memory Unit Unit).record ((), []) ⟨[], 0, 0⟩ ()).record
          ((), [false]) ⟨[], 0, 0⟩ ()⟩ : Observation Unit)) := by
  rw [restoring_program_observation]
  simp [emptyEnvironment]

/-- A complete runtime header includes unbounded private/history words and all
budget/availability/stop/output fields, without embedding them in native code. -/
private def header (privateWord : List Bool) : Header :=
  ⟨[true, false], [[false]], [[true]], privateWord, 2, [true, true, false], false, []⟩

example (privateWord reply : List Bool) :
    unframe ((header privateWord).initialWord ++ frame reply) = (header privateWord).encode ∧
      unframe (dropFrame ((header privateWord).initialWord ++ frame reply)) = reply :=
  header_reply_roundtrip _ _

example (a b : List Bool) (h : (header a).encode = (header b).encode) : a = b := by
  have he := Header.encode_injective h
  exact congrArg Header.privateSelector he

/-- Generic transport also preserves nonzero cursors and arbitrary tape functions;
it does not replace the ordinary storage by a blank initial configuration. -/
example {S P : Type} (continuation : MultiTapePTM 2 Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P)
    (tapes : Fin 2 → ℤ → Option Bool) :
    (NativeResponseExecution.localStartFrom continuation request memory reply next
      ⟨tapes, ![-3, 17]⟩).config.tapes.workTapes = tapes ∧
      (NativeResponseExecution.localStartFrom continuation request memory reply next
        ⟨tapes, ![-3, 17]⟩).config.tapes.workTapePos = ![-3, 17] :=
  NativeResponseExecution.localStartFrom_workspace _ _ _ _ _ _

end CslibFrontierTests.NativeRuntimeContext
