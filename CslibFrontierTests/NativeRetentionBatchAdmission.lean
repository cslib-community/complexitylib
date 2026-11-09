/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchUpper
import CslibFrontierTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Admitted concurrent batches in actual same-code native retention

The first pair of opportunities returns a partial cover and a charged cancellation.
The second fresh pair completes the cover. One hidden-state source shares an
unbounded invoice across each concurrent pair and carries it into the next batch.
The actual native controller starts with original input, rather than prepared State.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution
open StochasticOracle NativeRetention ConcurrentBatch
open scoped NNReal
namespace CslibFrontierTests.NativeRetentionBatchAdmission

private def data (turns : ℕ) : GuardedStartup.Input :=
  ⟨⟨⟨[[0], [1]], [1, 1], [1, 1], 1, [[0, 1]]⟩, turns, 6, [false, true]⟩, 3⟩
private def initial : RuntimeControl.State := GuardedStartup.state (data 3)
private def limits : Limits 6 := ⟨fun _ => 1, by intro _; norm_num, 3, 3⟩
private def start (seed : ℕ) : Memory Unit (ServerState 6 ℕ) := ⟨ConcurrentBatch.initial seed, []⟩
private def paths (word : Word) (tokens : ℕ) (i : Fin 6) : CallTrace :=
  ⟨if i.val % 2 = 0 then some (1, word) else none, fun _ => tokens,
    by intro _ _ _; exact le_rfl⟩
private def sample (coverFirst : Bool) : Sampler 6 ℕ := fun state _ =>
  CslibFrontierTests.NativeBatchMetadata.metadata.map fun value =>
    let tokens := state.privateState + value + 1
    let word := if state.history = [] then
      (if coverFirst then [true, true] else [true, false]) else [false, true]
    (paths word tokens, tokens)
private def batch0 : Batch 6 :=
  ⟨BatchPlanner.slots 6 2 initial, BatchPlanner.nonempty 6 2 initial (by decide) (by decide)⟩
private def exchange1 (seed first : ℕ) : Exchange 6 :=
  observe limits (limits.deadline - (start seed).privateState.elapsed) batch0
    (paths [true, false] (seed + first + 1))
private def memory1 (seed first : ℕ) : Memory Unit (ServerState 6 ℕ) :=
  (start seed).record ((), BatchPlanner.request 6 2 initial) (replyOf (exchange1 seed first))
    (commit (start seed).privateState (exchange1 seed first) (seed + first + 1))
private def state1 (seed first : ℕ) : RuntimeControl.State :=
  RuntimeControl.afterReply initial (replyOf (exchange1 seed first)).word
private def batch1 (seed first : ℕ) : Batch 6 :=
  ⟨BatchPlanner.slots 6 2 (state1 seed first),
    BatchPlanner.nonempty 6 2 _ (by decide) (by change 1 * 2 < 6; decide)⟩
private def exchange2 (seed first second : ℕ) : Exchange 6 :=
  observe limits (limits.deadline - (memory1 seed first).privateState.elapsed)
    (batch1 seed first) (paths [false, true] (seed + first + 1 + second + 1))
private def memory2 (seed first second : ℕ) : Memory Unit (ServerState 6 ℕ) :=
  (memory1 seed first).record ((), BatchPlanner.request 6 2 (state1 seed first))
    (replyOf (exchange2 seed first second))
    (commit (memory1 seed first).privateState (exchange2 seed first second)
      (seed + first + 1 + second + 1))
private def state2 (seed first second : ℕ) :=
  RuntimeControl.afterReply (state1 seed first) (replyOf (exchange2 seed first second)).word

private theorem memory1_private (seed first : ℕ) : (memory1 seed first).privateState =
    commit (start seed).privateState (exchange1 seed first) (seed + first + 1) := rfl
private theorem memory2_private (seed first second : ℕ) : (memory2 seed first second).privateState =
    commit (memory1 seed first).privateState (exchange2 seed first second)
      (seed + first + 1 + second + 1) := rfl

private theorem initial_aligned (seed : ℕ) :
    BatchAdmission.Aligned limits 2 3 1 initial (start seed) :=
  BatchAdmission.initial_aligned limits 2 1 (data 3) seed rfl

private theorem initial_live : RuntimeControl.stopped initial = false := by
  norm_num [RuntimeControl.stopped, initial, GuardedStartup.state, RuntimeControl.initial,
    data, Packets.decision, Packets.assemble, complete, output, retain, ground, covered, population]
  exact ⟨0, by decide⟩

private theorem initial_admit (seed : ℕ) :
    admit limits (start seed).privateState (BatchPlanner.request 6 2 initial) = some batch0 := by
  obtain ⟨batch, hs, ha⟩ := BatchAdmission.admit_request limits 2 3 1 (by decide) (by decide)
    (by decide) (by norm_num) (by norm_num [limits]) initial (start seed)
    (initial_aligned seed) initial_live
  have hb : batch = batch0 := by
    rcases batch with ⟨slots, hn⟩
    change slots = BatchPlanner.slots 6 2 initial at hs
    subst slots
    rfl
  subst batch
  exact ha

private theorem first_supported (seed first : ℕ) :
    (replyOf (exchange1 seed first), (memory1 seed first).privateState) ∈
      (environment limits (sample false) ((), BatchPlanner.request 6 2 initial)
        (start seed)).support := by
  have ha := initial_admit seed
  simp only [ConcurrentBatch.environment]
  rw [serve_accepted _ _ _ _ _ ha, PMF.mem_support_map_iff]
  refine ⟨(paths [true, false] (seed + first + 1), seed + first + 1), ?_, rfl⟩
  simp only [sample, start, ConcurrentBatch.initial, Bool.false_eq_true, ↓reduceIte]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨first, CslibFrontierTests.NativeBatchMetadata.metadata_support first, rfl⟩

private theorem first_aligned (seed first : ℕ) :
    BatchAdmission.Aligned limits 2 3 1 (state1 seed first) (memory1 seed first) := by
  have h := BatchAdmission.after_reply_aligned limits (sample false) 2 3 1
    (by decide) (by decide) (by decide) (by norm_num)
    (by intro _; norm_num [limits]) (by norm_num [limits])
    initial (start seed) (initial_aligned seed) initial_live _ _ (first_supported seed first)
  simpa only [state1, memory1, Memory.record] using h

private theorem first_report (seed first : ℕ) :
    (exchange1 seed first).report = fun i : Fin 6 =>
      if i = 0 then some (some [true, false], seed + first + 1)
      else if i = 1 then some (none, seed + first + 1) else none := by
  funext i
  fin_cases i <;>
    norm_num [exchange1, observe, batch0, BatchPlanner.slots, BatchPlanner.stage,
      initial, GuardedStartup.state, RuntimeControl.initial, data, paths, CallTrace.report,
      CallTrace.response, CallTrace.stop, limits, start, ConcurrentBatch.initial]

private theorem first_live (seed first : ℕ) :
    RuntimeControl.stopped (state1 seed first) = false := by
  norm_num [RuntimeControl.stopped, RuntimeControl.afterReply, state1, initial,
    GuardedStartup.state, RuntimeControl.initial, data, Packets.decision, Packets.assemble,
    replyOf, first_report, Packets.families_report, proposals, sourceIndices, complete, output,
    retain, ground, covered, population, NativeRetention.step, certified, newly, decodeFamily,
    List.ofFn_succ, List.range_succ,
    NativeRetention.normalize, cost, price, Finset.mem_filter, List.filterMap_cons,
    List.filterMap_nil]

private theorem second_supported (seed first second : ℕ) :
    (replyOf (exchange2 seed first second), (memory2 seed first second).privateState) ∈
      (environment limits (sample false) ((), BatchPlanner.request 6 2 (state1 seed first))
        (memory1 seed first)).support := by
  obtain ⟨batch, hs, ha⟩ := BatchAdmission.admit_request limits 2 3 1 (by decide) (by decide)
    (by decide) (by norm_num) (by norm_num [limits]) _ _ (first_aligned seed first)
    (first_live seed first)
  have hb : batch = batch1 seed first := by
    rcases batch with ⟨slots, hn⟩
    change slots = BatchPlanner.slots 6 2 (state1 seed first) at hs
    subst slots
    rfl
  subst batch
  simp only [ConcurrentBatch.environment]
  rw [serve_accepted _ _ _ _ _ ha, PMF.mem_support_map_iff]
  refine ⟨(paths [false, true] (seed + first + 1 + second + 1),
    seed + first + 1 + second + 1), ?_, rfl⟩
  simp only [sample, memory1, Memory.record, commit, List.cons_ne_nil, ↓reduceIte]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨second, CslibFrontierTests.NativeBatchMetadata.metadata_support second, rfl⟩

private theorem first_active : active batch0.slots = {0, 1} := by decide

private theorem first_duration (seed first : ℕ) : (exchange1 seed first).duration = 1 := by
  unfold exchange1 Exchange.duration
  change (active batch0.slots).sup _ = 1
  rw [first_active]
  norm_num [observe, batch0, BatchPlanner.slots, BatchPlanner.stage, initial,
    GuardedStartup.state, RuntimeControl.initial, data, paths, CallTrace.stop,
    limits, start, ConcurrentBatch.initial]

private theorem second_remaining (seed first : ℕ) :
    limits.deadline - (memory1 seed first).privateState.elapsed = 2 := by
  norm_num [memory1, Memory.record, commit, start, ConcurrentBatch.initial, limits, first_duration]
  exact (tsub_eq_iff_eq_add_of_le (by norm_num : (1 : ℝ≥0) ≤ 3)).2 (by norm_num)

private theorem second_report (seed first second : ℕ) :
    (exchange2 seed first second).report = fun i : Fin 6 =>
      if i = 2 then some (some [false, true], seed + first + 1 + second + 1)
      else if i = 3 then some (none, seed + first + 1 + second + 1) else none := by
  unfold exchange2
  rw [second_remaining]
  funext i
  fin_cases i <;>
    norm_num [observe, batch1, BatchPlanner.slots, BatchPlanner.stage,
      state1, RuntimeControl.afterReply, initial, GuardedStartup.state, RuntimeControl.initial,
      data, paths, CallTrace.report, CallTrace.response, CallTrace.stop, limits]

/-- Nontrivial partial cover then a complementary cover, from the actual source reports. -/
private theorem cover_stops (seed first second : ℕ) :
    RuntimeControl.result (state2 seed first second) = [true, true] ∧
      RuntimeControl.stopped (state2 seed first second) = true := by
  norm_num [RuntimeControl.result, RuntimeControl.stopped, state2, state1,
    RuntimeControl.afterReply, initial, GuardedStartup.state, RuntimeControl.initial, data,
    Packets.decision, Packets.assemble, replyOf, first_report, second_report,
    Packets.families_report, proposals, sourceIndices, complete, output, retain, ground,
    covered, population, NativeRetention.step, certified, newly, decodeFamily,
    List.ofFn_succ, List.range_succ, NativeRetention.normalize, cost, price,
    Finset.mem_filter, List.filterMap_cons, List.filterMap_nil]

private theorem support_step {P : Type} (env : Environment Unit P) (fuel : ℕ)
    (state : RuntimeControl.State) (channels : Unit → Channel Bool) (memory : Memory Unit P)
    (request : RuntimeControl.State → Word) (predicate : Feedback.Outcome P → Prop)
    (hs : RuntimeControl.stopped state = false) (reply : Reply) (next : P)
    (hr : (reply, next) ∈ (env ((), request state) memory).support)
    (ho : ∃ outcome ∈ (Feedback.run env fuel (RuntimeControl.afterReply state reply.word)
      (NativeQueryAll.finish (k := 0) () (request state) memory reply next).config.channels
      (memory.record ((), request state) reply next) request).support, predicate outcome) :
    ∃ outcome ∈ (Feedback.run env (fuel + 1) state channels memory request).support,
      predicate outcome := by
  obtain ⟨outcome, ho, hp⟩ := ho
  refine ⟨outcome, ?_, hp⟩
  rw [Feedback.run, hs]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
  exact ⟨(reply, next), hr, ho⟩

/-- Every unbounded pair of latent invoices occurs in the actual admitted run. -/
private theorem kernel_supported (seed first second : ℕ) :
    ∃ outcome ∈ (Feedback.run (environment limits (sample false)) 3 initial
      (fun _ => ⟨[], [], 0⟩) (start seed) (BatchPlanner.request 6 2)).support,
      outcome.state = state2 seed first second ∧ outcome.memory = memory2 seed first second := by
  apply support_step _ 2 _ _ _ _ _ initial_live _ _ (first_supported seed first)
  rw [memory1_private, ← memory1, ← state1]
  apply support_step _ 1 _ _ _ _ _ (first_live seed first) _ _
    (second_supported seed first second)
  rw [memory2_private, ← memory2, ← state2]
  rw [Feedback.run, (cover_stops seed first second).2]
  simp only [↓reduceIte, PMF.mem_support_pure_iff]
  exact ⟨_, rfl, rfl, rfl⟩

/-- One native program, fixed before the original input and latent invoices,
executes both fresh concurrent batches with the actual final resource-bearing ledger. -/
theorem native_correlated_batches : ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM tapes Bool R Unit) (context : Fin tapes), ∀ seed first second,
    some (⟨tapeOfList (RuntimeControl.packet (state2 seed first second)),
      RuntimeControl.result (state2 seed first second), memory2 seed first second⟩ :
        NativeReplyContext.Observation (ServerState 6 ℕ)) ∈
      ((NativeUnboundedExecution.terminal program (environment limits (sample false))
        ⟨program.initialConfig (GuardedStartup.encoding (data 3)), start seed⟩).map
          (Option.map (NativeReplyContext.observe context))).support := by
  obtain ⟨tapes, R, hR, program, context, hlaw⟩ := BatchPlanner.exists_native_controller 6 2
  refine ⟨tapes, R, hR, program, context, ?_⟩
  intro seed first second
  have h := hlaw (ServerState 6 ℕ) (environment limits (sample false)) (data 3) (start seed)
  dsimp only at h
  rw [show GuardedStartup.state (data 3) = initial from rfl] at h
  rw [show initial.turns = 3 from rfl] at h
  rw [h, PMF.mem_support_map_iff]
  obtain ⟨outcome, ho, hs, hm⟩ := kernel_supported seed first second
  exact ⟨outcome, ho, by rw [hs, hm]⟩

/-- Both real source batches are accepted, including the canceled calls' consumed
labels and actual per-batch maximum, rather than a sum of concurrent durations. -/
example (seed first second : ℕ) :
    BatchAdmission.Aligned limits 2 3 1 (state2 seed first second) (memory2 seed first second) := by
  have h := BatchAdmission.after_reply_aligned limits (sample false) 2 3 1
    (by decide) (by decide) (by decide) (by norm_num)
    (by intro _; norm_num [limits]) (by norm_num [limits]) _ _
    (first_aligned seed first) (first_live seed first) _ _ (second_supported seed first second)
  simpa only [state2, memory2, Memory.record] using h

/-- Cancellation is charged through the same source receipt: both selected
opportunities pay the shared unbounded invoice, while concurrent duration is one. -/
example (seed first : ℕ) :
    (exchange1 seed first).report 1 = some (none, seed + first + 1) ∧
      (exchange1 seed first).tokens = 2 * (seed + first + 1) ∧
      (exchange1 seed first).duration = 1 := by
  refine ⟨by rw [first_report]; simp, ?_, first_duration seed first⟩
  unfold Exchange.tokens
  change (∑ i ∈ active batch0.slots,
    (((exchange1 seed first).report i).getD (none, 0)).2) = _
  rw [first_active, first_report]
  simp
  omega

/-- Zero original turn budget never forms a batch or samples the shared source. -/
example (env : Environment Unit ℕ) (fuel : ℕ) (memory : Memory Unit ℕ) :
    Feedback.run env fuel (GuardedStartup.state (data 0)) (fun _ => ⟨[], [], 0⟩)
      memory (BatchPlanner.request 6 2) =
      PMF.pure ⟨GuardedStartup.state (data 0), memory, fun _ => ⟨[], [], 0⟩⟩ := by
  cases fuel <;> simp [Feedback.run, RuntimeControl.stopped, GuardedStartup.state,
    RuntimeControl.initial, data]

/-- An empty opportunity interface is not an issued source batch. -/
example (state : RuntimeControl.State) (width : ℕ) :
    decodeBatch 0 (BatchPlanner.request 0 width state) = none := by
  simp [BatchPlanner.request, encodeSlots, decodeBatch, decodeSlots, active]

private theorem original_valid : Valid (data 3).startup.system := by
  constructor
  · intro j
    rcases j with _ | (_ | j) <;> norm_num [data]
  · intro e
    rcases e with _ | (_ | e) <;> norm_num [data]
  · intro j
    rcases j with _ | (_ | j) <;>
      norm_num [data, elements, ground, List.range_succ]

/-- The concrete nonempty-cover input satisfies every source admission premise
of the actual every-prefix native `SelectionOnly` endpoint. -/
theorem native_selectionOnly : ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM tapes Bool R Unit), ∀ seed,
      NativeUnboundedExecution.SelectionOnly program (environment limits (sample false))
        (NativeBatch.candidateParser (n := 6) 2) (decodeFamily 2) (fun _ => true)
        ⟨program.initialConfig (GuardedStartup.encoding (data 3)), start seed⟩ := by
  obtain ⟨tapes, R, hR, program, hp⟩ :=
    BatchAdmission.exists_selectionOnly_controller (n := 6) 2
  refine ⟨tapes, R, hR, program, ?_⟩
  intro seed
  exact hp ℕ limits (sample false) (data 3) seed 1 rfl (by decide) (by decide)
    (by decide) (by norm_num) (by intro _; norm_num [limits]) (by norm_num [data, limits])
    original_valid

private def fullExchange (seed first : ℕ) : Exchange 6 :=
  observe limits (limits.deadline - (start seed).privateState.elapsed) batch0
    (paths [true, true] (seed + first + 1))
private def fullState (seed first : ℕ) :=
  RuntimeControl.afterReply initial (replyOf (fullExchange seed first)).word
private def fullMemory (seed first : ℕ) :=
  (start seed).record ((), BatchPlanner.request 6 2 initial) (replyOf (fullExchange seed first))
    (commit (start seed).privateState (fullExchange seed first) (seed + first + 1))

private theorem full_report (seed first : ℕ) :
    (fullExchange seed first).report = fun i : Fin 6 =>
      if i = 0 then some (some [true, true], seed + first + 1)
      else if i = 1 then some (none, seed + first + 1) else none := by
  funext i
  fin_cases i <;>
    norm_num [fullExchange, observe, batch0, BatchPlanner.slots, BatchPlanner.stage,
      initial, GuardedStartup.state, RuntimeControl.initial, data, paths, CallTrace.report,
      CallTrace.response, CallTrace.stop, limits, start, ConcurrentBatch.initial]

private theorem full_stops (seed first : ℕ) :
    RuntimeControl.stopped (fullState seed first) = true ∧
      RuntimeControl.result (fullState seed first) = [true, true] := by
  norm_num [RuntimeControl.stopped, RuntimeControl.result, fullState, RuntimeControl.afterReply,
    initial, GuardedStartup.state, RuntimeControl.initial, data, Packets.decision, Packets.assemble,
    replyOf, full_report, Packets.families_report, proposals, sourceIndices, complete, output,
    retain, ground, covered, population, NativeRetention.step, certified, newly, decodeFamily,
    List.ofFn_succ, List.range_succ, NativeRetention.normalize, cost, price,
    Finset.mem_filter, List.filterMap_cons, List.filterMap_nil]

private theorem full_supported (seed first : ℕ) :
    (replyOf (fullExchange seed first), (fullMemory seed first).privateState) ∈
      (environment limits (sample true) ((), BatchPlanner.request 6 2 initial)
        (start seed)).support := by
  simp only [ConcurrentBatch.environment]
  rw [serve_accepted _ _ _ _ _ (initial_admit seed), PMF.mem_support_map_iff]
  refine ⟨(paths [true, true] (seed + first + 1), seed + first + 1), ?_, rfl⟩
  simp only [sample, start, ConcurrentBatch.initial, ↓reduceIte]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨first, CslibFrontierTests.NativeBatchMetadata.metadata_support first, rfl⟩

/-- Completion after the first actual source batch stops while two turns and
fresh later blocks remain. The raw native loop cannot issue an unconditional second query. -/
example (seed first : ℕ) :
    ∃ outcome ∈ (Feedback.run (environment limits (sample true)) 3 initial
      (fun _ => ⟨[], [], 0⟩) (start seed) (BatchPlanner.request 6 2)).support,
      outcome.memory.events.length = 1 ∧ RuntimeControl.result outcome.state = [true, true] := by
  apply support_step _ 2 _ _ _ _ _ initial_live _ _ (full_supported seed first)
  rw [← fullState, Feedback.run, (full_stops seed first).1]
  simp only [↓reduceIte, PMF.mem_support_pure_iff]
  refine ⟨_, rfl, rfl, ?_⟩
  exact (full_stops seed first).2

/-- Four labeled opportunities, rather than two scalar block allowances, are
actually consumed. The two selected batches are disjoint before responses arrive. -/
example (seed first : ℕ) :
    active batch0.slots = {0, 1} ∧ active (batch1 seed first).slots = {2, 3} ∧
      Disjoint (active batch0.slots) (active (batch1 seed first).slots) := by
  have h0 : active batch0.slots = {0, 1} := by decide
  have h1 : active (batch1 seed first).slots = {2, 3} := by
    rw [show (batch1 seed first).slots = BatchPlanner.slots 6 2 (state1 seed first) from rfl,
      BatchPlanner.active_slots]
    change Finset.univ.filter (fun i : Fin 6 => i.val / 2 = 1) = {2, 3}
    decide
  rw [h0, h1]
  decide

/-- The second batch payload contains the first actual reply and the original
instance; source request bytes are not confused with the cached State frames. -/
example (seed first : ℕ) :
    (batch1 seed first).slots 2 = some (frame (RuntimeControl.encoding (state1 seed first))) ∧
    (state1 seed first).work.system = (data 3).startup.system ∧
    (state1 seed first).work.history = [(replyOf (exchange1 seed first)).word] := by
  exact ⟨rfl, rfl, rfl⟩

/-- The correlated first receipt is genuinely incomplete under the abstract local
retention test as well as under the executed native guard. -/
example (seed first : ℕ) :
    let state := state1 seed first
    let hx : Valid state.work.system := original_valid
    (instanceOf state.work.system hx).covered
      (AdaptiveSelection.selected (instanceOf state.work.system hx) state.work.system.rho
        (BatchStopping.proposal state.work) state.work.history) ≠
          (instanceOf state.work.system hx).ground :=
  ((BatchStopping.live_iff (state1 seed first) original_valid).mp
    (first_live seed first)).2.2.2

/-- Exact counters are checked on the same correlated two-batch execution used by
its native-law client, including the cancellation invoices. -/
example (seed first second : ℕ) :
    ∃ outcome ∈ (Feedback.run (environment limits (sample false)) 3 initial
        (fun _ => ⟨[], [], 0⟩) (start seed) (BatchPlanner.request 6 2)).support,
      outcome.state.turns = 1 ∧ outcome.state.opportunities = 4 ∧
        outcome.state.allotments = 1 := by
  obtain ⟨outcome, ho, hs, hm⟩ := kernel_supported seed first second
  refine ⟨outcome, ho, ?_⟩
  have hb := Feedback.run_allowances _ _ _ _ _ _ outcome ho
  rw [hm] at hb
  have hlen : (memory2 seed first second).events.length = 2 := rfl
  rw [hlen] at hb
  change outcome.state.turns + 2 = 3 ∧ outcome.state.opportunities + 2 = 6 ∧
    outcome.state.allotments + 2 = 3 at hb
  omega

/-- A single actual full response supplies the nonzero productive-count threshold;
the generic count theorem returns both the cover and its dual certificate. -/
example (seed first : ℕ) :
    let state := fullState seed first
    let hx : Valid state.work.system := original_valid
    let I := instanceOf state.work.system hx
    I.covered ((outputFamily (Packets.assemble state.work)).image Fin.val) = I.ground ∧
      I.cost ((outputFamily (Packets.assemble state.work)).image Fin.val) ≤
        (state.work.system.rho : ℝ) * ∑ e ∈ I.ground, I.dual e := by
  let state := fullState seed first
  have hx : Valid state.work.system := original_valid
  let I := instanceOf state.work.system hx
  have hd : (Packets.decision state.work).1 = true := by
    by_contra h
    have hz : RuntimeControl.result state = [] := by
      simp only [RuntimeControl.result, h, ↓reduceIte]
    have hf := (full_stops seed first).2
    rw [hf] at hz
    have hl := congrArg List.length hz
    norm_num at hl
  have hg := (BatchStopping.completion_iff state.work hx).mp hd
  change I.covered (AdaptiveSelection.selected I state.work.system.rho
    (BatchStopping.proposal state.work) state.work.history) = I.ground at hg
  have hr : AdaptiveSelection.residual I state.work.system.rho
      (BatchStopping.proposal state.work) state.work.history = 0 := by
    simp only [AdaptiveSelection.residual, hg, Finset.sdiff_self, Finset.card_empty]
  have hcard : I.ground.card = 2 := by
    norm_num [I, instanceOf, ground, state, fullState, RuntimeControl.afterReply,
      initial, GuardedStartup.state, RuntimeControl.initial, data, List.range_succ]
  have hc : I.ground.card ≤ 2 * AdaptiveSelection.count
      (AdaptiveSelection.productive I state.work.system.rho
        (BatchStopping.proposal state.work) 2) state.work.history := by
    rw [hcard]
    change 2 ≤ 2 * (0 + if AdaptiveSelection.productive I state.work.system.rho
      (BatchStopping.proposal state.work) 2 []
        (replyOf (fullExchange seed first)).word then 1 else 0)
    have hp : AdaptiveSelection.productive I state.work.system.rho
        (BatchStopping.proposal state.work) 2 []
          (replyOf (fullExchange seed first)).word = true := by
      change decide (AdaptiveSelection.residual I state.work.system.rho
        (BatchStopping.proposal state.work) state.work.history ≤ _) = true
      rw [hr]
      simp
    rw [hp]
    decide
  exact (BatchStopping.count_completed state hx 2 hc).2.2

/-- An exhausted reservation really can stop before a cover: the allowance
hypothesis in the horizon theorem cannot be dropped. -/
example :
    RuntimeControl.stopped { initial with allotments := 0 } = true ∧
      (Packets.decision { initial.work with history := [] }).1 = false := by
  refine ⟨by simp [RuntimeControl.stopped], ?_⟩
  have hd := (Bool.or_eq_false_iff.mp initial_live).2
  exact hd

/-- The first actual concurrent receipt has one returned proposal and one canceled
call. Natural row indices agree with the source finite mask, in actual order. -/
example (seed first : ℕ) :
    BatchReceipts.proposal (data 3).startup.system [] (some (exchange1 seed first)) = [{0}] := by
  rw [BatchReceipts.proposal_eq]
  dsimp only [Option.elim_some]
  rw [first_report]
  norm_num [data, proposals, List.ofFn_succ, decodeFamily, List.filterMap_cons]
  decide

/-- Exact authenticated receipt completion, rather than a union-of-provenance
approximation, remains false after the first real partial-cover batch. -/
example (seed first : ℕ) :
    NativeBatch.Retained.complete (instanceOf (data 3).startup.system original_valid) 1
      (BatchReceipts.proposal (data 3).startup.system)
      ((memory1 seed first).privateState.history.map some) = false := by
  have hc := BatchReceipts.aligned_completion_eq limits 2 3 1
    (state1 seed first) (memory1 seed first) (first_aligned seed first) original_valid
  rw [(Bool.or_eq_false_iff.mp (first_live seed first)).2] at hc
  simpa only [state1, RuntimeControl.afterReply, initial, GuardedStartup.state,
    RuntimeControl.initial, data, Rat.cast_one] using hc.symm

/-- The constructed native controller's actual selected epochs stop precisely at
computed completion, for the same correlated, unbounded-metadata source. -/
theorem native_epoch_stopping : ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM tapes Bool R Unit), ∀ seed t, t < 3 →
      ∀ o ∈ ((NativeBatch.Quantitative.select limits (sample false) program
        (NativeBatch.Trace.law limits (sample false) program t
          ⟨program.initialConfig (GuardedStartup.encoding (data 3)), start seed⟩)).map
            (NativeBatch.Quantitative.observe limits)).support,
      (o.issued = true → NativeBatch.Retained.complete
        (instanceOf (data 3).startup.system original_valid) 1
        (BatchReceipts.proposal (data 3).startup.system) o.history = false) ∧
      (o.issued = false → NativeBatch.Retained.complete
        (instanceOf (data 3).startup.system original_valid) 1
        (BatchReceipts.proposal (data 3).startup.system) o.history = true) := by
  obtain ⟨tapes, R, hR, program, hp⟩ :=
    BatchUpper.exists_native_stopping_controller (n := 6) 2
  refine ⟨tapes, R, hR, program, ?_⟩
  intro seed t ht o ho
  have hrho : ((data 3).startup.system.rho : ℝ) = 1 := by norm_num [data]
  simpa only [hrho] using hp ℕ limits (sample false) (data 3) seed 1 rfl (by decide)
    (by decide)
    (by norm_num) (by intro _; norm_num [limits]) (by norm_num [data, limits])
    rfl (by decide) original_valid t ht o ho

end CslibFrontierTests.NativeRetentionBatchAdmission
