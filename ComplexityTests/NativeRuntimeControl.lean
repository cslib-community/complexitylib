/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.NativeRetention.RuntimeControl
import ComplexityTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Native runtime post-response control clients

The same blank-tape code reads actual correlated full reports, updates runtime
history/private storage and budgets, and writes the new guard packet. This is a
single native phase; a computed stop bit is not evidence of an executed restart
or source admission of the raw context request.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM NativeOpenExecution
open StochasticOracle ConcurrentBatch NativeRetention RuntimeControl
namespace ComplexityTests.NativeRuntimeControl

private def startup (turns opportunities : ℕ) : InitialContext.Startup :=
  ⟨⟨[[0], [1]], [1, 1], [1, 1], 1, [[0, 1]]⟩, turns, opportunities, [false, true]⟩
private def state (turns opportunities allotments : ℕ) : State :=
  RuntimeControl.initial (startup turns opportunities) allotments
private def report (success : Bool) (tokens : ℕ) : List Bool :=
  encodeReport (n := 2) fun i =>
    if i = 0 then some (if success then some [true, true] else none, tokens) else none
private def receipt (success : Bool) (tokens : ℕ) : Reply :=
  ⟨report success tokens, tokens, 2⟩
private def environment : Environment Unit (Bool × ℕ) := fun _ memory =>
  NativeBatchMetadata.metadata.map fun value =>
    let tokens := memory.privateState.2 + value
    (receipt memory.privateState.1 tokens, (memory.privateState.1, tokens))
private def memory (success : Bool) (seed : ℕ) : Memory Unit (Bool × ℕ) :=
  ⟨(success, seed), []⟩

/-- A fabricated initial full cover is ignored; the accepted actual report creates
completion, a retained two-candidate mask and updated private/history/counter data. -/
example (tokens : ℕ) :
    let old := state 3 2 4
    let next := afterReply old (report true tokens)
    stopped old = false ∧ stopped next = true ∧ result next = [true, true] ∧
      next.work.history = [report true tokens] ∧
      next.requests = [frame (encoding old)] ∧
      next.privateWord = [false, true] ++ frame (report true tokens) ∧
      next.turns = 2 ∧ next.opportunities = 1 ∧ next.allotments = 3 := by
  dsimp only
  simp only [afterReply, state, RuntimeControl.initial, startup]
  norm_num [stopped, result, Packets.decision, Packets.assemble, report,
    Packets.families_report, proposals, sourceIndices, complete, output, retain,
    ground, covered, population, NativeRetention.step, certified, newly,
    decodeFamily, List.range_succ, List.ofFn_succ, Finset.mem_filter,
    List.filterMap_cons, List.filterMap_nil, NativeRetention.normalize, cost, price]

/-- A cancellation contributes no family even with an unbounded nonzero invoice. -/
example (tokens : ℕ) :
    stopped (afterReply (state 3 2 4) (report false tokens)) = false ∧
      result (afterReply (state 3 2 4) (report false tokens)) = [] := by
  norm_num [stopped, result, afterReply, state, RuntimeControl.initial, startup, Packets.decision,
    Packets.assemble, report, Packets.families_report, proposals, sourceIndices,
    complete, output, retain, ground, covered, population, NativeRetention.step, certified, newly,
    decodeFamily, List.range_succ, List.ofFn_succ, Finset.mem_filter,
    List.filterMap_cons, List.filterMap_nil, NativeRetention.normalize, cost, price]

/-- The phase recomputes a stop flag after a reply on each exhausted counter.
An allotment is a reservation count, not observed oracle latency. -/
example (reply : List Bool) :
    stopped (afterReply (state 1 2 4) reply) = true ∧
      stopped (afterReply (state 3 1 4) reply) = true ∧
      stopped (afterReply (state 3 2 1) reply) = true := by
  simp [stopped, afterReply, state, RuntimeControl.initial, startup]

/-- One actual native program works for all runtime data and hidden correlated
sources. It starts on the original encoded data with all work tapes blank. -/
theorem actual_native_law :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (program : MultiTapePTM ((3 + k) + 2) Bool S Unit),
      ∀ (old : State) (success : Bool) (seed : ℕ),
        (NativeUnboundedExecution.terminal program environment
          ⟨program.initialConfig (frame (encoding old)), memory success seed⟩).map
          (Option.map (NativeReplyContext.observe 0)) =
          NativeBatchMetadata.metadata.map fun value =>
            let tokens := seed + value
            some (⟨tapeOfList (process (old, report success tokens)), [],
              (memory success seed).record ((), frame (encoding old))
                (receipt success tokens) (success, tokens)⟩ :
                  NativeReplyContext.Observation (Bool × ℕ)) := by
  obtain ⟨k, S, hS, program, hp⟩ := exists_native_phase
  refine ⟨k, S, hS, program, ?_⟩
  intro old success seed
  rw [hp, environment, PMF.map_comp]
  rfl

/-- Every geometric invoice length remains positively supported by the same actual
machine. No bounded reply approximation or desired native representation is passed. -/
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM ((3 + k) + 2) Bool S Unit),
    ∀ (old : State) (success : Bool) (seed value : ℕ),
      some (⟨tapeOfList (process (old, report success (seed + value))), [],
        (memory success seed).record ((), frame (encoding old))
          (receipt success (seed + value)) (success, seed + value)⟩ :
            NativeReplyContext.Observation (Bool × ℕ)) ∈
        ((NativeUnboundedExecution.terminal program environment
          ⟨program.initialConfig (frame (encoding old)), memory success seed⟩).map
          (Option.map (NativeReplyContext.observe 0))).support := by
  obtain ⟨k, S, hS, program, hp⟩ := actual_native_law
  refine ⟨k, S, hS, program, ?_⟩
  intro old success seed value
  rw [hp]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨value, NativeBatchMetadata.metadata_support value, rfl⟩

/-- Actual native execution writes the recomputed exhausted-turn flag and records
one call. This checks the phase's stored control; it does not execute a feedback guard. -/
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM ((3 + k) + 2) Bool S Unit), ∀ seed : ℕ,
    ((NativeUnboundedExecution.terminal program environment
      ⟨program.initialConfig (frame (encoding (state 1 2 4))), memory false seed⟩).map
      (Option.map (NativeReplyContext.observe 0))).map
        (Option.map fun result =>
          (result.contextTape 0, result.output, result.memory.events.length)) =
      PMF.pure (some (some true, [], 1)) := by
  obtain ⟨k, S, hS, program, hp⟩ := actual_native_law
  refine ⟨k, S, hS, program, ?_⟩
  intro seed
  rw [hp, PMF.map_comp]
  have he : (Option.map (fun result =>
      (result.contextTape 0, result.output, result.memory.events.length)) ∘
      (fun value => some
        (⟨tapeOfList (process (state 1 2 4, report false (seed + value))), [],
          (memory false seed).record ((), frame (encoding (state 1 2 4)))
            (receipt false (seed + value)) (false, seed + value)⟩ :
              NativeReplyContext.Observation (Bool × ℕ)))) =
      fun _ => some (some true, [], 1) := by
    funext value
    simp [process, packet, NativeStopGuard.packet, stopped, afterReply,
      state, RuntimeControl.initial, startup, tapeOfList_zero, Memory.record, memory]
  rw [he]
  exact PMF.map_const _ _

private def emptySource : Environment Unit Unit :=
  fun _ memory => PMF.pure (⟨[], 0, 0⟩, memory.privateState)

/-- An empty complete reply with zero bill/duration traverses the real reader and
splice, including its final frame delimiter; the new context remains readable. -/
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM ((3 + k) + 2) Bool S Unit), ∀ old : State,
    (NativeUnboundedExecution.terminal program emptySource
      ⟨program.initialConfig (frame (encoding old)), ⟨(), []⟩⟩).map
      (Option.map (NativeReplyContext.observe 0)) =
      PMF.pure (some (⟨tapeOfList (process (old, [])), [],
        (⟨(), []⟩ : Memory Unit Unit).record ((), frame (encoding old)) ⟨[], 0, 0⟩ ()⟩ :
          NativeReplyContext.Observation Unit)) := by
  obtain ⟨k, S, hS, program, hp⟩ := exists_native_phase
  refine ⟨k, S, hS, program, ?_⟩
  intro old
  rw [hp, emptySource, PMF.pure_map]

end ComplexityTests.NativeRuntimeControl
