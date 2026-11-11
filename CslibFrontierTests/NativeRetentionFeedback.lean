/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.Feedback
import CslibFrontierTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Actual repeated native runtime feedback

One blank-tape program handles all original inputs and one consistent hidden-state
source. A canceled first response is followed by a request containing its actual
history/private word and the original instance; a successful second response stops
before the third allowed query. No contexts are compiled or supplied between turns.
The raw-State requests are not source-admitted concurrent batches, and reservation
exhaustion is not a measured deadline theorem.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM NativeOpenExecution
open StochasticOracle NativeRetention ConcurrentBatch
namespace CslibFrontierTests.NativeRetentionFeedback

private def data (turns allotments : ℕ) : GuardedStartup.Input :=
  ⟨⟨⟨[[0], [1]], [1, 1], [1, 1], 1, [[0, 1]]⟩, turns, 3, [false, true]⟩, allotments⟩
private def initial : RuntimeControl.State := GuardedStartup.state (data 3 4)
private def report (success : Bool) (tokens : ℕ) : List Bool :=
  encodeReport (n := 3) fun i =>
    if i = 0 then some (if success then some [true, true] else none, tokens) else none
private def receipt (success : Bool) (tokens : ℕ) : Reply := ⟨report success tokens, tokens, 2⟩
private def memory (stage seed : ℕ) : Memory Unit (ℕ × ℕ) := ⟨(stage, seed), []⟩
private def environment : Environment Unit (ℕ × ℕ) := fun _ memory =>
  NativeBatchMetadata.metadata.map fun value =>
    let tokens := memory.privateState.2 + value
    (receipt (decide (0 < memory.privateState.1)) tokens, (memory.privateState.1 + 1, tokens))
private def state1 (tokens : ℕ) := RuntimeControl.afterReply initial (report false tokens)
private def state2 (first second : ℕ) :=
  RuntimeControl.afterReply (state1 first) (report true second)
private def ledger1 (seed tokens : ℕ) : Memory Unit (ℕ × ℕ) :=
  (memory 0 seed).record ((), frame (RuntimeControl.encoding initial))
    (receipt false tokens) (1, tokens)
private def ledger2 (seed first second : ℕ) : Memory Unit (ℕ × ℕ) :=
  (ledger1 seed first).record ((), frame (RuntimeControl.encoding (state1 first)))
    (receipt true second) (2, second)

private theorem initial_live : RuntimeControl.stopped initial = false := by
  norm_num [RuntimeControl.stopped, initial, GuardedStartup.state, RuntimeControl.initial,
    data, Packets.decision, Packets.assemble, complete, output, retain, ground, covered, population]
  exact ⟨0, by decide⟩

private theorem cancellation_live (tokens : ℕ) :
    RuntimeControl.stopped (state1 tokens) = false := by
  norm_num [RuntimeControl.stopped, RuntimeControl.afterReply, state1, initial,
    GuardedStartup.state, RuntimeControl.initial, data, Packets.decision, Packets.assemble,
    report, Packets.families_report, proposals, sourceIndices, complete, output, retain,
    ground, covered, population]
  exact ⟨0, by decide⟩

private theorem cover_stops (first second : ℕ) :
    RuntimeControl.stopped (state2 first second) = true ∧
      RuntimeControl.result (state2 first second) = [true, true] := by
  norm_num [RuntimeControl.stopped, RuntimeControl.result, RuntimeControl.afterReply,
    state2, state1, initial, GuardedStartup.state, RuntimeControl.initial, data,
    Packets.decision, Packets.assemble, report, Packets.families_report, proposals, sourceIndices,
    complete, output, retain, ground, covered, population, NativeRetention.step, certified, newly,
    decodeFamily, List.range_succ, List.ofFn_succ, Finset.mem_filter, List.filterMap_cons,
    List.filterMap_nil, NativeRetention.normalize, cost, price]

private theorem two_turn_kernel (seed : ℕ) :
    Feedback.run environment 3 initial (fun _ => ⟨[], [], 0⟩) (memory 0 seed) =
      NativeBatchMetadata.metadata.bind fun first =>
        NativeBatchMetadata.metadata.map fun second =>
          let tokens1 := seed + first
          let tokens2 := tokens1 + second
          (⟨state2 tokens1 tokens2, ledger2 seed tokens1 tokens2,
            (NativeQueryAll.finish (k := 0) ()
              (frame (RuntimeControl.encoding (state1 tokens1))) (ledger1 seed tokens1)
                (receipt true tokens2) (2, tokens2)).config.channels⟩ :
                  Feedback.Outcome (ℕ × ℕ)) := by
  rw [Feedback.run, initial_live]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind]
  rw [environment, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro first _
  dsimp only [Function.comp_apply]
  change Feedback.run environment 2 (state1 (seed + first)) _ (ledger1 seed (seed + first)) = _
  rw [Feedback.run, cancellation_live]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind]
  rw [environment, PMF.bind_map]
  conv_rhs => rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro second _
  dsimp only [Function.comp_apply]
  change Feedback.run environment 1 (state2 (seed + first) (seed + first + second)) _
    (ledger2 seed (seed + first) (seed + first + second)) = _
  rw [Feedback.run, (cover_stops _ _).1]
  rfl

/-- This is the law of one actual native program, with two full correlated replies
and exact original-context-dependent second request. All allowances still permit
another call after the successful second response, but the computed guard stops. -/
theorem two_turn_native_law : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit) (context : Fin width), ∀ seed,
    (NativeUnboundedExecution.terminal program environment
      ⟨program.initialConfig (GuardedStartup.encoding (data 3 4)), memory 0 seed⟩).map
      (Option.map (NativeReplyContext.observe context)) =
      NativeBatchMetadata.metadata.bind fun first =>
        NativeBatchMetadata.metadata.map fun second =>
          let tokens1 := seed + first
          let tokens2 := tokens1 + second
          some (⟨tapeOfList (RuntimeControl.packet (state2 tokens1 tokens2)), [true, true],
            ledger2 seed tokens1 tokens2⟩ : NativeReplyContext.Observation (ℕ × ℕ)) := by
  obtain ⟨width, R, hR, program, context, hp⟩ := Feedback.exists_native_controller
  refine ⟨width, R, hR, program, context, ?_⟩
  intro seed
  rw [hp]
  change (Feedback.run environment 3 initial _ _).map _ = _
  rw [two_turn_kernel, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro first _
  rw [PMF.map_comp]
  apply congrArg (fun f => NativeBatchMetadata.metadata.map f)
  funext second
  dsimp only [Function.comp_apply]
  rw [(cover_stops _ _).2]

/-- The actual second request authenticates both replies, the initial private word
and the original instance; no fabricated initial proposal becomes history. -/
example (seed first second : ℕ) :
    RuntimeControl.HistoryMatches [false, true] (state2 first second)
      (ledger2 seed first second).events ∧
    (state2 first second).work.system = (data 3 4).startup.system ∧
    (ledger2 seed first second).events.length = 2 := by
  refine ⟨?_, rfl, rfl⟩
  exact RuntimeControl.afterReply_history_matches [false, true] (state1 first)
    (ledger1 seed first) (receipt true second) (2, second)
    (RuntimeControl.afterReply_history_matches [false, true] initial (memory 0 seed)
      (receipt false first) (1, first) (RuntimeControl.initial_history_matches _ _))

private theorem first_cover_stops (tokens : ℕ) :
    RuntimeControl.stopped (RuntimeControl.afterReply initial (report true tokens)) = true ∧
      RuntimeControl.result (RuntimeControl.afterReply initial (report true tokens)) =
        [true, true] := by
  norm_num [RuntimeControl.stopped, RuntimeControl.result, RuntimeControl.afterReply,
    initial, GuardedStartup.state, RuntimeControl.initial, data, Packets.decision, Packets.assemble,
    report, Packets.families_report, proposals, sourceIndices, complete, output, retain,
    ground, covered, population, NativeRetention.step, certified, newly, decodeFamily,
    List.range_succ, List.ofFn_succ, Finset.mem_filter, List.filterMap_cons,
    List.filterMap_nil, NativeRetention.normalize, cost, price]

/-- The same code stops after its first accepted full cover even though all
scalar allowances remain live; its hidden-state source is unchanged. -/
example : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit) (context : Fin width), ∀ seed,
    (NativeUnboundedExecution.terminal program environment
      ⟨program.initialConfig (GuardedStartup.encoding (data 3 4)), memory 1 seed⟩).map
      (Option.map (NativeReplyContext.observe context)) =
      NativeBatchMetadata.metadata.map fun value =>
        let tokens := seed + value
        some (⟨tapeOfList (RuntimeControl.packet
          (RuntimeControl.afterReply initial (report true tokens))), [true, true],
          (memory 1 seed).record ((), frame (RuntimeControl.encoding initial))
            (receipt true tokens) (2, tokens)⟩ : NativeReplyContext.Observation (ℕ × ℕ)) := by
  obtain ⟨width, R, hR, program, context, hp⟩ := Feedback.exists_native_controller
  refine ⟨width, R, hR, program, context, ?_⟩
  intro seed
  rw [hp]
  change (Feedback.run environment 3 initial _ _).map _ = _
  rw [Feedback.run, initial_live]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind, PMF.map_bind]
  rw [environment, PMF.bind_map]
  conv_rhs => rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro value _
  dsimp only [Function.comp_apply]
  change (Feedback.run environment 2 (RuntimeControl.afterReply initial
    (report true (seed + value))) _ _).map _ = _
  rw [Feedback.run_of_stopped _ _ _ _ _ (first_cover_stops _).1, PMF.pure_map]
  dsimp only
  rw [(first_cover_stops _).2]
  rfl

private theorem live_data (turns allotments : ℕ) :
    RuntimeControl.stopped (GuardedStartup.state (data (turns + 1) (allotments + 1))) = false := by
  norm_num [RuntimeControl.stopped, GuardedStartup.state, RuntimeControl.initial,
    data, Packets.decision, Packets.assemble, complete, output, retain, ground, covered, population]
  exact ⟨0, by decide⟩

/-- Arbitrarily many available turns do not bypass reservation exhaustion. A
canceled first reply consumes the last reservation and the same code makes no
second call. This counter test does not assert a measured physical deadline. -/
example : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit) (context : Fin width), ∀ turns seed,
    ((NativeUnboundedExecution.terminal program environment
      ⟨program.initialConfig (GuardedStartup.encoding (data (turns + 1) 1)), memory 0 seed⟩).map
      (Option.map (NativeReplyContext.observe context))).map
        (Option.map fun observed => observed.memory.events.length) = PMF.pure (some 1) := by
  obtain ⟨width, R, hR, program, context, hp⟩ := Feedback.exists_native_controller
  refine ⟨width, R, hR, program, context, ?_⟩
  intro turns seed
  rw [hp]
  change ((Feedback.run environment (turns + 1)
    (GuardedStartup.state (data (turns + 1) 1)) _ _).map _).map _ = _
  rw [Feedback.run, live_data turns 0]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind,
    PMF.map_bind, PMF.map_comp]
  rw [environment, PMF.bind_map]
  trans NativeBatchMetadata.metadata.bind (fun _ => PMF.pure (some 1))
  · apply PMF.bind_congr_on_support
    intro value _
    dsimp only [Function.comp_apply]
    have hs : RuntimeControl.stopped (RuntimeControl.afterReply
        (GuardedStartup.state (data (turns + 1) 1)) (report false (seed + value))) = true := by
      simp [RuntimeControl.stopped, RuntimeControl.afterReply, GuardedStartup.state,
        RuntimeControl.initial, data]
    change (Feedback.run environment turns
      (RuntimeControl.afterReply (GuardedStartup.state (data (turns + 1) 1))
        (report false (seed + value))) _ _).map _ = _
    rw [Feedback.run_of_stopped _ _ _ _ _ hs, PMF.pure_map]
    rfl
  · exact PMF.bind_const _ _

private def emptySource : Environment Unit Unit :=
  fun _ memory => PMF.pure (⟨[], 0, 0⟩, memory.privateState)

/-- An empty zero-bill/zero-duration reply passes both real buffer cleanup layers
and stops on its single turn budget, rather than leaving a marker for a later call. -/
example : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit) (context : Fin width),
    ((NativeUnboundedExecution.terminal program emptySource
      ⟨program.initialConfig (GuardedStartup.encoding (data 1 4)), ⟨(), []⟩⟩).map
      (Option.map (NativeReplyContext.observe context))).map
        (Option.map fun observed => observed.memory.events.length) = PMF.pure (some 1) := by
  obtain ⟨width, R, hR, program, context, hp⟩ := Feedback.exists_native_controller
  refine ⟨width, R, hR, program, context, ?_⟩
  rw [hp]
  change ((Feedback.run emptySource 1 (GuardedStartup.state (data 1 4)) _ _).map _).map _ = _
  rw [Feedback.run, live_data 0 3]
  simp only [Bool.false_eq_true, ↓reduceIte, emptySource, PMF.monad_bind_eq_bind, PMF.pure_bind,
    Feedback.run, PMF.pure_map]
  rfl

/-- The original zero-turn guard prevents even the first query for every hidden
source and every prior memory ledger. -/
example : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit) (context : Fin width),
    ∀ (P : Type) (env : Environment Unit P) (memory : Memory Unit P),
    ((NativeUnboundedExecution.terminal program env
      ⟨program.initialConfig (GuardedStartup.encoding (data 0 4)), memory⟩).map
      (Option.map (NativeReplyContext.observe context))).map
        (Option.map fun observed => observed.memory) = PMF.pure (some memory) := by
  obtain ⟨width, R, hR, program, context, hp⟩ := Feedback.exists_native_controller
  refine ⟨width, R, hR, program, context, ?_⟩
  intro P env memory
  rw [hp]
  change ((Feedback.run env 0 _ _ _).map _).map _ = _
  rw [Feedback.run, PMF.pure_map, PMF.pure_map]
  rfl

private def emptyGround : GuardedStartup.Input :=
  ⟨⟨⟨[[0], [1]], [1, 1], [], 1, [[99]]⟩, 3, 3, [true]⟩, 4⟩

/-- Initial completion emits the all-false mask of the original two-candidate
instance without making any call, even with fabricated initial proposals. -/
example : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit) (context : Fin width),
    ∀ (P : Type) (env : Environment Unit P) (memory : Memory Unit P),
    ((NativeUnboundedExecution.terminal program env
      ⟨program.initialConfig (GuardedStartup.encoding emptyGround), memory⟩).map
      (Option.map (NativeReplyContext.observe context))).map
        (Option.map fun observed => (observed.output, observed.memory)) =
        PMF.pure (some ([false, false], memory)) := by
  obtain ⟨width, R, hR, program, context, hp⟩ := Feedback.exists_native_controller
  refine ⟨width, R, hR, program, context, ?_⟩
  intro P env memory
  rw [hp]
  dsimp only
  have hs : RuntimeControl.stopped (GuardedStartup.state emptyGround) = true := by
    norm_num [RuntimeControl.stopped, GuardedStartup.state, RuntimeControl.initial, emptyGround,
      Packets.decision, Packets.assemble, complete, output, retain, ground, covered, population]
  rw [Feedback.run_of_stopped _ _ _ _ _ hs, PMF.pure_map, PMF.pure_map]
  norm_num [RuntimeControl.result, GuardedStartup.state, RuntimeControl.initial, emptyGround,
    Packets.decision, Packets.assemble, complete, output, retain, ground, covered, population]

/-- Turn-bounded native feedback terminates almost surely even when full response
lengths have no common bound. This follows from the actual native law, not a
termination hypothesis or an instruction-level timeout. -/
example : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit),
    ∀ (P : Type) (env : Environment Unit P) (data : GuardedStartup.Input)
      (memory : Memory Unit P),
      none ∉ (NativeUnboundedExecution.terminal program env
        ⟨program.initialConfig (GuardedStartup.encoding data), memory⟩).support := by
  obtain ⟨width, R, hR, program, context, hp⟩ := Feedback.exists_native_controller
  refine ⟨width, R, hR, program, ?_⟩
  intro P env data memory hn
  have ho : none ∈ ((NativeUnboundedExecution.terminal program env
      ⟨program.initialConfig (GuardedStartup.encoding data), memory⟩).map
      (Option.map (NativeReplyContext.observe context))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
  rw [hp] at ho
  dsimp only at ho
  rw [PMF.mem_support_map_iff] at ho
  obtain ⟨outcome, _, ho⟩ := ho
  cases ho

/-- Every pair of unbounded geometric invoice indices is supported by the same
actual native machine. The second invoice is correlated with the first through
the retained hidden seed, rather than replaced by a bounded reply alphabet. -/
example : ∃ (width : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM width Bool R Unit) (context : Fin width), ∀ seed first second,
    some (⟨tapeOfList (RuntimeControl.packet
      (state2 (seed + first) (seed + first + second))), [true, true],
      ledger2 seed (seed + first) (seed + first + second)⟩ :
        NativeReplyContext.Observation (ℕ × ℕ)) ∈
      ((NativeUnboundedExecution.terminal program environment
        ⟨program.initialConfig (GuardedStartup.encoding (data 3 4)), memory 0 seed⟩).map
          (Option.map (NativeReplyContext.observe context))).support := by
  obtain ⟨width, R, hR, program, context, hp⟩ := two_turn_native_law
  refine ⟨width, R, hR, program, context, ?_⟩
  intro seed first second
  rw [hp, PMF.mem_support_bind_iff]
  refine ⟨first, NativeBatchMetadata.metadata_support first, ?_⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨second, NativeBatchMetadata.metadata_support second, rfl⟩

/-- The observed two-event ledger retains both invoices and sequential durations;
all allowances still permit a third turn, which completion prevents. -/
example (seed first second : ℕ) :
    tokenBill (ledger2 seed first second).events = first + second ∧
    elapsed (ledger2 seed first second).events = 4 ∧
    (state2 first second).turns = 1 ∧ (state2 first second).opportunities = 1 ∧
      (state2 first second).allotments = 2 := by
  norm_num [tokenBill, elapsed, ledger2, ledger1, memory, Memory.record, receipt, state2, state1,
    initial, GuardedStartup.state, RuntimeControl.initial, RuntimeControl.afterReply, data,
    add_comm]

end CslibFrontierTests.NativeRetentionFeedback
