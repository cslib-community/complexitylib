/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.NativeRetention.GuardedStartup
import ComplexityTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Actual guarded Startup/runtime-State conversion

One finite program handles original inputs with zero/live allowances and empty
or nonempty ground. Stopped inputs never call the environment. Live inputs reach
the same uniform updater with a correlated unbounded reply and authenticated raw
history. The updated guard is executed after this phase; a live branch still terminates
silently rather than executing a feedback/deadline selector.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM NativeOpenExecution
open StochasticOracle NativeRetention ConcurrentBatch
namespace ComplexityTests.NativeGuardedStartup

private def data (turns opportunities allotments : ℕ) : GuardedStartup.Input :=
  ⟨⟨⟨[[0], [1]], [1, 1], [1, 1], 1, [[0, 1]]⟩,
    turns, opportunities, [false, true]⟩, allotments⟩
private def report (success : Bool) (tokens : ℕ) : List Bool :=
  encodeReport (n := 2) fun i =>
    if i = 0 then some (if success then some [true, true] else none, tokens) else none
private def receipt (success : Bool) (tokens : ℕ) : Reply := ⟨report success tokens, tokens, 2⟩
private def memory (success : Bool) (seed : ℕ) : Memory Unit (Bool × ℕ) := ⟨(success, seed), []⟩
private def environment : Environment Unit (Bool × ℕ) := fun _ memory =>
  NativeBatchMetadata.metadata.map fun value =>
    let tokens := memory.privateState.2 + value
    (receipt memory.privateState.1 tokens, (memory.privateState.1, tokens))
private def stoppedOutcome (input : GuardedStartup.Input) (success : Bool) (seed : ℕ) :
    NativeReplyContext.Observation (Bool × ℕ) :=
  ⟨fun _ => none, RuntimeControl.result (GuardedStartup.state input), memory success seed⟩
private def liveOutcome (input : GuardedStartup.Input) (success : Bool) (seed value : ℕ) :
    NativeReplyContext.Observation (Bool × ℕ) :=
  let old := GuardedStartup.state input
  let tokens := seed + value
  let updated := RuntimeControl.afterReply old (report success tokens)
  ⟨tapeOfList (RuntimeControl.process (old, report success tokens)),
    if RuntimeControl.stopped updated then RuntimeControl.result updated else [],
    (memory success seed).record ((), frame (RuntimeControl.encoding old))
      (receipt success tokens) (success, tokens)⟩

/-- No prepared context, State witness or machine-law hypothesis is supplied.
The same actual code branches before querying on every original input. -/
theorem actual_native_law :
    ∃ (width : ℕ) (S : Type) (_ : Finite S)
      (program : MultiTapePTM width Bool S Unit) (context : Fin width),
      ∀ (input : GuardedStartup.Input) (success : Bool) (seed : ℕ),
        (NativeUnboundedExecution.terminal program environment
          ⟨program.initialConfig (GuardedStartup.encoding input), memory success seed⟩).map
          (Option.map (NativeReplyContext.observe context)) =
        if RuntimeControl.stopped (GuardedStartup.state input) then
          PMF.pure (some (stoppedOutcome input success seed))
        else NativeBatchMetadata.metadata.map fun value =>
          some (liveOutcome input success seed value) := by
  obtain ⟨width, S, hS, program, context, hp⟩ := GuardedStartup.exists_guarded_phase
  refine ⟨width, S, hS, program, context, ?_⟩
  intro input success seed
  rw [hp]
  split
  · rfl
  · rw [environment, PMF.map_comp]
    rfl

/-- Exhausted turns, planning opportunities or reservations actually prevent the
first call. A reservation-zero edge is not a physical-clock deadline theorem. -/
example : ∃ (width : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM width Bool S Unit) (context : Fin width),
    ∀ input ∈ [data 0 2 4, data 3 0 4, data 3 2 0], ∀ success seed,
      (NativeUnboundedExecution.terminal program environment
        ⟨program.initialConfig (GuardedStartup.encoding input), memory success seed⟩).map
        (Option.map (NativeReplyContext.observe context)) =
        PMF.pure (some (stoppedOutcome input success seed)) := by
  obtain ⟨width, S, hS, program, context, hp⟩ := actual_native_law
  refine ⟨width, S, hS, program, context, ?_⟩
  intro input hi success seed
  rw [hp]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;>
    simp [GuardedStartup.state, RuntimeControl.initial, RuntimeControl.stopped, data]

private def emptyGround : GuardedStartup.Input :=
  ⟨⟨⟨[[0], [1]], [1, 1], [], 1, [[99]]⟩, 3, 2, [true]⟩, 4⟩

/-- Initial completion returns the genuine two-candidate all-false mask and
preserves memory without sampling a response. -/
example : ∃ (width : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM width Bool S Unit) (context : Fin width), ∀ success seed,
    ((NativeUnboundedExecution.terminal program environment
      ⟨program.initialConfig (GuardedStartup.encoding emptyGround), memory success seed⟩).map
      (Option.map (NativeReplyContext.observe context))).map
      (Option.map fun result => (result.output, result.memory)) =
      PMF.pure (some ([false, false], memory success seed)) := by
  obtain ⟨width, S, hS, program, context, hp⟩ := actual_native_law
  refine ⟨width, S, hS, program, context, ?_⟩
  intro success seed
  rw [hp]
  norm_num [stoppedOutcome, GuardedStartup.state, RuntimeControl.initial,
    RuntimeControl.stopped, RuntimeControl.result, emptyGround, Packets.decision,
    Packets.assemble, complete, output, retain, ground, covered, population]

private theorem live : RuntimeControl.stopped (GuardedStartup.state (data 3 2 4)) = false := by
  norm_num [GuardedStartup.state, RuntimeControl.initial, RuntimeControl.stopped, data,
    Packets.decision, Packets.assemble, complete, output, retain, ground, covered, population]
  exact ⟨0, by decide⟩

/-- All unbounded geometric reports remain supported by the actual native live
branch, on nonempty ground despite fabricated initial proposals. -/
example : ∃ (width : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM width Bool S Unit) (context : Fin width), ∀ success seed value,
      some (liveOutcome (data 3 2 4) success seed value) ∈
        ((NativeUnboundedExecution.terminal program environment
          ⟨program.initialConfig (GuardedStartup.encoding (data 3 2 4)), memory success seed⟩).map
          (Option.map (NativeReplyContext.observe context))).support := by
  obtain ⟨width, S, hS, program, context, hp⟩ := actual_native_law
  refine ⟨width, S, hS, program, context, ?_⟩
  intro success seed value
  rw [hp, live]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨value, NativeBatchMetadata.metadata_support value, rfl⟩

/-- The actual live native readback contains a State whose stored history and
private word match actual oracle events; no decoded/history certificate is supplied. -/
example : ∃ (width : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM width Bool S Unit) (context : Fin width),
    ∀ success seed (observed : NativeReplyContext.Observation (Bool × ℕ)),
      some observed ∈ ((NativeUnboundedExecution.terminal program environment
        ⟨program.initialConfig (GuardedStartup.encoding (data 3 2 4)), memory success seed⟩).map
        (Option.map (NativeReplyContext.observe context))).support →
      ∃ reply : Reply,
        RuntimeControl.HistoryMatches (data 3 2 4).startup.privateSelector
          (RuntimeControl.afterReply (GuardedStartup.state (data 3 2 4)) reply.word)
          observed.memory.events ∧
        observed.contextTape = tapeOfList
          (RuntimeControl.packet
            (RuntimeControl.afterReply (GuardedStartup.state (data 3 2 4)) reply.word)) := by
  obtain ⟨width, S, hS, program, context, hp⟩ := actual_native_law
  refine ⟨width, S, hS, program, context, ?_⟩
  intro success seed observed ho
  rw [hp, live] at ho
  simp only [Bool.false_eq_true, ↓reduceIte] at ho
  rw [PMF.mem_support_map_iff] at ho
  obtain ⟨value, _, hv⟩ := ho
  cases hv
  refine ⟨receipt success (seed + value), ?_, rfl⟩
  exact RuntimeControl.afterReply_history_matches _ _ (memory success seed) _ _
    (RuntimeControl.initial_history_matches _ _)

/-- The integrated entry executes its stopped packet after consuming its last turn,
planning allowance or reservation. The single actual billed event is retained. -/
example : ∃ (width : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM width Bool S Unit) (context : Fin width),
    ∀ input ∈ [data 1 2 4, data 3 1 4, data 3 2 1], ∀ seed,
      ((NativeUnboundedExecution.terminal program environment
        ⟨program.initialConfig (GuardedStartup.encoding input), memory false seed⟩).map
        (Option.map (NativeReplyContext.observe context))).map
        (Option.map fun result =>
          (result.contextTape 0, result.memory.events.length)) =
        PMF.pure (some (some true, 1)) := by
  obtain ⟨width, S, hS, program, context, hp⟩ := actual_native_law
  refine ⟨width, S, hS, program, context, ?_⟩
  intro input hi seed
  have hl : RuntimeControl.stopped (GuardedStartup.state input) = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      norm_num [GuardedStartup.state, RuntimeControl.initial, RuntimeControl.stopped, data,
        Packets.decision, Packets.assemble, complete, output, retain, ground, covered, population]
    all_goals exact ⟨0, by decide⟩
  rw [hp, hl]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.map_comp]
  have he : (Option.map (fun result : NativeReplyContext.Observation (Bool × ℕ) =>
      (result.contextTape 0, result.memory.events.length)) ∘
      (fun value => some (liveOutcome input false seed value))) =
      fun _ => some (some true, 1) := by
    funext value
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [liveOutcome, RuntimeControl.process, RuntimeControl.packet, NativeStopGuard.packet,
        RuntimeControl.stopped, RuntimeControl.afterReply, GuardedStartup.state,
        RuntimeControl.initial, data, tapeOfList_zero, Memory.record, memory]
  rw [he]
  exact PMF.map_const _ _

private theorem success_dispatch (tokens : ℕ) :
    (if RuntimeControl.stopped (RuntimeControl.afterReply
        (GuardedStartup.state (data 3 2 4)) (report true tokens)) then
      RuntimeControl.result (RuntimeControl.afterReply
        (GuardedStartup.state (data 3 2 4)) (report true tokens)) else []) = [true, true] := by
  norm_num [RuntimeControl.stopped, RuntimeControl.result, RuntimeControl.afterReply,
    GuardedStartup.state, RuntimeControl.initial, data, Packets.decision, Packets.assemble,
    report, Packets.families_report, proposals, sourceIndices, complete, output, retain,
    ground, covered, population, NativeRetention.step, certified, newly, decodeFamily,
    List.range_succ, List.ofFn_succ, Finset.mem_filter, List.filterMap_cons,
    List.filterMap_nil, NativeRetention.normalize, cost, price]

private theorem cancel_dispatch (tokens : ℕ) :
    (if RuntimeControl.stopped (RuntimeControl.afterReply
        (GuardedStartup.state (data 3 2 4)) (report false tokens)) then
      RuntimeControl.result (RuntimeControl.afterReply
        (GuardedStartup.state (data 3 2 4)) (report false tokens)) else []) = [] := by
  norm_num [RuntimeControl.stopped, RuntimeControl.result, RuntimeControl.afterReply,
    GuardedStartup.state, RuntimeControl.initial, data, Packets.decision, Packets.assemble,
    report, Packets.families_report, proposals, sourceIndices, complete, output, retain,
    ground, covered, population]
  intro _
  exact ⟨0, by decide⟩

private theorem live_output (success : Bool) (seed value : ℕ) :
    (liveOutcome (data 3 2 4) success seed value).output =
      if success then [true, true] else [] := by
  dsimp only [liveOutcome]
  cases success
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact cancel_dispatch (seed + value)
  · simp only [↓reduceIte]
    exact success_dispatch (seed + value)

private theorem project_live (input : GuardedStartup.Input) (success : Bool) (seed value : ℕ) :
    Option.map (fun observed : NativeReplyContext.Observation (Bool × ℕ) =>
      (observed.output, observed.memory.events.length))
        (some (liveOutcome input success seed value)) =
      some ((liveOutcome input success seed value).output, (1 : ℕ)) := rfl

/-- The same blank-tape machine actually emits the locally retained full-cover mask
on success and no mask on cancellation. Its single event keeps the correlated
unbounded invoice and duration jointly; private context bytes are not output. -/
example : ∃ (width : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM width Bool S Unit) (context : Fin width), ∀ (success : Bool) (seed : ℕ),
      ((NativeUnboundedExecution.terminal program environment
        ⟨program.initialConfig (GuardedStartup.encoding (data 3 2 4)), memory success seed⟩).map
        (Option.map (NativeReplyContext.observe context))).map
        (Option.map fun observed : NativeReplyContext.Observation (Bool × ℕ) =>
          (observed.output, observed.memory.events.length)) =
      NativeBatchMetadata.metadata.map fun _ =>
        some (if success then [true, true] else [], (1 : ℕ)) := by
  obtain ⟨width, S, hS, program, context, hp⟩ := actual_native_law
  refine ⟨width, S, hS, program, context, ?_⟩
  intro success seed
  rw [hp, live]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.map_comp]
  apply congrArg (fun f : ℕ → Option (List Bool × ℕ) => NativeBatchMetadata.metadata.map f)
  funext value
  rw [Function.comp_apply, project_live, live_output]

private def emptySource : Environment Unit Unit :=
  fun _ memory => PMF.pure (⟨[], 0, 0⟩, memory.privateState)

/-- Empty zero-invoice reports traverse the integrated original-input loader,
virtual-input reader and updater, retaining the genuine single event. -/
example : ∃ (width : ℕ) (S : Type) (_ : Finite S)
    (program : MultiTapePTM width Bool S Unit) (context : Fin width),
    (NativeUnboundedExecution.terminal program emptySource
      ⟨program.initialConfig (GuardedStartup.encoding (data 3 2 4)), ⟨(), []⟩⟩).map
      (Option.map (NativeReplyContext.observe context)) =
      PMF.pure (some (⟨tapeOfList
        (RuntimeControl.process (GuardedStartup.state (data 3 2 4), [])),
        if RuntimeControl.stopped
            (RuntimeControl.afterReply (GuardedStartup.state (data 3 2 4)) []) then
          RuntimeControl.result
            (RuntimeControl.afterReply (GuardedStartup.state (data 3 2 4)) []) else [],
        (⟨(), []⟩ : Memory Unit Unit).record
          ((), frame (RuntimeControl.encoding (GuardedStartup.state (data 3 2 4))))
          ⟨[], 0, 0⟩ ()⟩ : NativeReplyContext.Observation Unit)) := by
  obtain ⟨width, S, hS, program, context, hp⟩ := GuardedStartup.exists_guarded_phase
  refine ⟨width, S, hS, program, context, ?_⟩
  rw [hp, live]
  simp only [Bool.false_eq_true, ↓reduceIte, emptySource, PMF.pure_map]

end ComplexityTests.NativeGuardedStartup
