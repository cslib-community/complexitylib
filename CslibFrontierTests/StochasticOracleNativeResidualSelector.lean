/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualEncoding
import CslibFrontierTests.StochasticOracleResidualCover
import CslibFrontier.Computability.Probabilistic.NativeBatch
import Mathlib.Tactic

/-!
# Native residual-directed two-turn execution

Three disjoint three-point X3C inputs have a triple and a whole-block fallback.
The hidden missing component determines both correlated answers. The same native
program starts from binary incidence input without a cover witness, asks the near
cover, computes its actual residual and queries only the matching specialist.
Actual source admission, global opportunity nonreuse, native output and joint
bill/oracle duration are checked, not supplied as a realization contract.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualSelector
open Cslib Cslib.Probability StochasticOracle NativeRetention ConcurrentBatch
open NativeResidualSelector Turing Turing.MultiTapeTM NativeOpenExecution
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

private def original : SourceEncoding.Input :=
  ⟨[[true, true, true, false, false, false, false, false, false],
    [true, true, true, false, false, false, false, false, false],
    [false, false, false, true, true, true, false, false, false],
    [false, false, false, true, true, true, false, false, false],
    [false, false, false, false, false, false, true, true, true],
    [false, false, false, false, false, false, true, true, true]],
    [1/3, 2/3, 1/3, 2/3, 1/3, 2/3], List.replicate 9 (1/9), 1⟩

private theorem original_valid : SourceEncoding.Valid original := by
  constructor
  · rfl
  · intro j hj
    change j < 6 at hj
    interval_cases j <;> decide +kernel
  · intro e he
    change e < 9 at he
    interval_cases e <;> decide +kernel
  · intro j hj
    change j < 6 at hj
    interval_cases j <;> decide +kernel

private def start : RuntimeControl.State := NativeResidualSelector.initial 3 original
private def mask (j : Fin 3) (near : Bool) : Word :=
  (List.range 6).map fun c => decide (c % 2 = 0) &&
    if near then decide (c / 2 ≠ j.val) else decide (c / 2 = j.val)
private def limits : Limits 4 := ⟨fun _ => 1, by intro _; norm_num, 2, 2⟩
private def expectedQuery (j : Fin 3) : Word :=
  queryEncoding ⟨SourceEncoding.toNative original, List.range' (3 * j.val) 3⟩

-- Source roles are indexed in increasing recovered-component order. A specialist
-- accepts only its original labeled WSC subinstance; a wrong query is canceled.
private def paths (missing : Fin 3) (batch : ConcurrentBatch.Batch 4) (i : Fin 4) : CallTrace :=
  if i.val = 0 then
    ⟨some (1, mask missing true), fun _ => 3, by intro _ _ _; rfl⟩
  else if h : i.val - 1 < 3 then
    let j : Fin 3 := ⟨i.val - 1, h⟩
    if batch.slots i = some (expectedQuery j) then
      ⟨some (1, mask j false), fun _ => 2, by intro _ _ _; rfl⟩
    else ⟨none, fun _ => 2, by intro _ _ _; rfl⟩
  else ⟨none, fun _ => 0, by intro _ _ _; rfl⟩
private def sample : Sampler 4 (Fin 3) :=
  fun state batch => PMF.pure (paths state.privateState batch, state.privateState)

private theorem start_interface : start.work.opportunities = 4 := rfl
attribute [local simp] start_interface

private theorem first_nonempty : (active (slots start)).Nonempty := by
  refine ⟨(0 : Fin 4), ?_⟩
  simp [active, slots, selected, start, NativeResidualSelector.initial]
private def firstBatch : ConcurrentBatch.Batch 4 := ⟨slots start, first_nonempty⟩
private def firstReceipt (j : Fin 3) : Exchange 4 :=
  observe limits 2 firstBatch (paths j firstBatch)
private def second (j : Fin 3) : RuntimeControl.State :=
  RuntimeControl.afterReply start (replyOf (firstReceipt j)).word

private theorem second_interface (j : Fin 3) : (second j).work.opportunities = 4 := rfl
attribute [local simp] second_interface

private def nearReport (j : Fin 3) : Report 4 :=
  fun i => if i.val = 0 then some (some (mask j true), 3) else none
private theorem first_report (j : Fin 3) : (firstReceipt j).report = nearReport j := by
  funext i
  fin_cases i <;> norm_num [firstReceipt, observe, firstBatch, slots, selected,
    start, NativeResidualSelector.initial, paths, nearReport, limits,
    CallTrace.report, CallTrace.response, CallTrace.stop, second_interface]
private theorem first_word (j : Fin 3) : (replyOf (firstReceipt j)).word =
    encodeReport (nearReport j) := congrArg encodeReport (first_report j)

private def nearFamily (j : Fin 3) : List ℕ :=
  ((List.range 3).filter fun k => decide (k ≠ j.val)).map (2 * ·)
private theorem near_families (j : Fin 3) :
    Packets.families 4 6 (encodeReport (nearReport j)) = [nearFamily j] := by
  rw [Packets.families_report]
  fin_cases j <;> norm_num [proposals, nearReport, mask, nearFamily, decodeFamily,
    sourceIndices, List.ofFn_succ, List.finRange_succ, List.finRange_zero,
    List.filterMap_cons, List.filterMap_nil, Finset.univ_unique] <;> decide

private theorem second_assemble (j : Fin 3) : Packets.assemble (second j).work =
    { SourceEncoding.toNative original with proposals := [nearFamily j] } := by
  unfold second
  rw [first_word]
  change { SourceEncoding.toNative original with proposals :=
    (([encodeReport (nearReport j)] : List Word).reverse.flatMap (Packets.families 4 6)) } = _
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, near_families]

-- Component recovery is computed from the original rows, with no encoded partition.
example : representatives (SourceEncoding.toNative original) = [0, 3, 6] := by decide

private theorem target_second (j : Fin 3) : target (second j) = 3 * j.val := by
  unfold target NativeResidualSelector.residual
  rw [second_assemble]
  fin_cases j <;> decide +kernel
private theorem second_points (j : Fin 3) :
    (query (second j)).points = List.range' (3 * j.val) 3 := by
  simp only [query, show (second j).turns = 1 from rfl]
  unfold NativeResidualSelector.residual
  rw [second_assemble]
  fin_cases j <;> decide +kernel

private theorem second_slots (j : Fin 3) : slots (second j) =
    fun i : Fin 4 => if i.val = j.val + 1 then some (expectedQuery j) else none := by
  have ht : (second j).turns = 1 := rfl
  have hs : (second j).work.system = SourceEncoding.toNative original := rfl
  have hq : query (second j) = ⟨SourceEncoding.toNative original,
      List.range' (3 * j.val) 3⟩ := by
    have heta : ∀ q : Query, q = ⟨q.system, q.points⟩ := by intro q; cases q; rfl
    rw [heta (query (second j)), second_points]
    rfl
  funext i
  simp only [slots, selected, ht, hs, hq, target_second]
  have hr : representatives (SourceEncoding.toNative original) = [0, 3, 6] := by decide
  rw [hr]
  fin_cases j <;> fin_cases i <;> norm_num [expectedQuery]

private theorem second_nonempty (j : Fin 3) : (active (slots (second j))).Nonempty := by
  refine ⟨(⟨j.val + 1, by omega⟩ : Fin 4), ?_⟩
  simp [active, second_slots]
private def secondBatch (j : Fin 3) : ConcurrentBatch.Batch 4 :=
  ⟨slots (second j), second_nonempty j⟩
private def secondReceipt (j : Fin 3) : Exchange 4 :=
  observe limits 1 (secondBatch j) (paths j (secondBatch j))
private def done (j : Fin 3) : RuntimeControl.State :=
  RuntimeControl.afterReply (second j) (replyOf (secondReceipt j)).word
private def mem0 (j : Fin 3) : Memory Unit (ServerState 4 (Fin 3)) :=
  ⟨ConcurrentBatch.initial j, []⟩
private def mem1 (j : Fin 3) : Memory Unit (ServerState 4 (Fin 3)) :=
  (mem0 j).record ((), request start) (replyOf (firstReceipt j))
    (commit (ConcurrentBatch.initial j) (firstReceipt j) j)
private def mem2 (j : Fin 3) : Memory Unit (ServerState 4 (Fin 3)) :=
  (mem1 j).record ((), request (second j)) (replyOf (secondReceipt j))
    (commit (mem1 j).privateState (secondReceipt j) j)

private theorem first_admit (j : Fin 3) :
    admit limits (mem0 j).privateState (request start) = some firstBatch := by
  rw [request_eq]
  change admit limits (ConcurrentBatch.initial j) (encodeBatch firstBatch) = _
  rw [admit, decodeBatch_encode]
  simp [limits, ConcurrentBatch.initial]

private theorem first_active : active firstBatch.slots = {(0 : Fin 4)} := by
  ext i
  simp [active, firstBatch, slots, selected, start, NativeResidualSelector.initial]

private theorem first_time (j : Fin 3) : (firstReceipt j).duration = 1 := by
  change (active firstBatch.slots).sup _ = _
  rw [first_active, Finset.sup_singleton]
  change (observe limits 2 firstBatch (paths j firstBatch)).time 0 = 1
  norm_num [observe, firstBatch, slots, selected, start, NativeResidualSelector.initial,
    limits, paths, CallTrace.stop, second_interface]

private theorem first_tokens (j : Fin 3) : (firstReceipt j).tokens = 3 := by
  change (observe limits 2 firstBatch _).tokens = _
  rw [observe_tokens, first_active, Finset.sum_singleton]
  simp [paths]

private theorem second_admit (j : Fin 3) :
    admit limits (mem1 j).privateState (request (second j)) = some (secondBatch j) := by
  rw [request_eq]
  change admit limits (mem1 j).privateState (encodeBatch (secondBatch j)) = _
  simp only [admit, decodeBatch_encode]
  have hd : Disjoint (active (slots (second j))) (active (slots start)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hf
    have he : i.val = 0 := by
      have hf' : i ∈ active firstBatch.slots := hf
      rw [first_active] at hf'
      have hi0 : i = (0 : Fin 4) := Finset.mem_singleton.mp hf'
      exact congrArg Fin.val hi0
    have hn : i.val = j.val + 1 := by simpa [active, second_slots] using hi
    omega
  have he : (mem1 j).privateState.elapsed = (firstReceipt j).duration := by
    simp [mem1, mem0, Memory.record, commit, ConcurrentBatch.initial]
  have hu : (mem1 j).privateState.used = active (slots start) := by
    simp [mem1, mem0, Memory.record, commit, ConcurrentBatch.initial, firstReceipt,
      observe, firstBatch]
  have ht : (mem1 j).privateState.history.length = 1 := rfl
  rw [ite_eq_left]
  exact ⟨by rw [he, first_time]; norm_num [limits],
    by rw [ht]; norm_num [limits], by simpa only [secondBatch, hu] using hd⟩

private theorem source_first (j : Fin 3) :
    environment limits sample ((), request start) (mem0 j) =
      PMF.pure (replyOf (firstReceipt j), (mem1 j).privateState) := by
  change serve limits sample (request start) (mem0 j).privateState = _
  rw [serve_accepted _ _ _ _ _ (first_admit j)]
  simp only [sample, PMF.pure_map]
  simp [mem0, mem1, Memory.record, limits, ConcurrentBatch.initial, firstReceipt]
private theorem source_second (j : Fin 3) :
    environment limits sample ((), request (second j)) (mem1 j) =
      PMF.pure (replyOf (secondReceipt j), (mem2 j).privateState) := by
  change serve limits sample (request (second j)) (mem1 j).privateState = _
  rw [serve_accepted _ _ _ _ _ (second_admit j)]
  simp only [sample, PMF.pure_map]
  have hr : observe limits (limits.deadline - (mem1 j).privateState.elapsed)
      (secondBatch j) (paths (mem1 j).privateState.privateState (secondBatch j)) =
      secondReceipt j := by
    change observe limits (2 - (0 + (firstReceipt j).duration)) _ _ = _
    rw [first_time]
    rw [zero_add, show (2 : ℝ≥0) - 1 = 1 from tsub_eq_of_eq_add (by norm_num)]
    rfl
  rw [hr]
  rfl

private theorem start_live : RuntimeControl.stopped start = false := by decide
private theorem second_live (j : Fin 3) : RuntimeControl.stopped (second j) = false := by
  have ht : (second j).turns = 1 := rfl
  have ho : (second j).opportunities = 3 := rfl
  have ha : (second j).allotments = 1 := rfl
  simp only [RuntimeControl.stopped, ht, ho, ha,
    Packets.decision, second_assemble]
  fin_cases j <;> decide +kernel
private def specialistReport (j : Fin 3) : Report 4 :=
  fun i => if i.val = j.val + 1 then some (some (mask j false), 2) else none
private theorem second_report (j : Fin 3) : (secondReceipt j).report = specialistReport j := by
  funext i
  fin_cases j <;> fin_cases i <;>
    norm_num [secondReceipt, observe, secondBatch, second_slots, specialistReport, paths,
      limits, CallTrace.report, CallTrace.response, CallTrace.stop, second_interface]
private theorem second_word (j : Fin 3) : (replyOf (secondReceipt j)).word =
    encodeReport (specialistReport j) := congrArg encodeReport (second_report j)
private theorem specialist_families (j : Fin 3) :
    Packets.families 4 6 (encodeReport (specialistReport j)) = [[2 * j.val]] := by
  rw [Packets.families_report]
  fin_cases j <;> norm_num [proposals, specialistReport, mask, decodeFamily,
    sourceIndices, List.ofFn_succ, List.finRange_succ, List.finRange_zero,
    List.filterMap_cons, List.filterMap_nil, Finset.univ_unique]

private theorem done_assemble (j : Fin 3) : Packets.assemble (done j).work =
    { SourceEncoding.toNative original with proposals := [nearFamily j, [2 * j.val]] } := by
  unfold done second
  rw [second_word, first_word]
  change { SourceEncoding.toNative original with proposals :=
    (([encodeReport (specialistReport j), encodeReport (nearReport j)] : List Word).reverse.flatMap
      (Packets.families 4 6)) } = _
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, near_families, specialist_families,
    List.singleton_append]

private theorem done_output (j : Fin 3) : RuntimeControl.result (done j) =
    [true, false, true, false, true, false] := by
  simp only [RuntimeControl.result, Packets.decision, done_assemble]
  fin_cases j <;> decide +kernel

private theorem final_valid (j : Fin 3) : Valid (Packets.assemble (done j).work) := by
  obtain ⟨hw, hd, hf⟩ := SourceEncoding.valid_toNative original original_valid
  rw [done_assemble]
  exact ⟨hw, hd, hf⟩

-- Certification of the very family computed from the two actual source replies.
-- Feasibility of the dual and the completion decision are both derived here.
example (j : Fin 3) :
    let data := Packets.assemble (done j).work
    let I := instanceOf data (final_valid j)
    I.covered ((outputFamily data).image Fin.val) = I.ground ∧
      I.cost ((outputFamily data).image Fin.val) ≤
        (data.rho : ℝ) * ∑ e ∈ I.ground, I.dual e := by
  dsimp only
  apply completed_output
  rw [done_assemble]
  fin_cases j <;> decide +kernel

private theorem second_active (j : Fin 3) : active (secondBatch j).slots =
    {(⟨j.val + 1, by omega⟩ : Fin 4)} := by
  ext i
  simp [active, secondBatch, second_slots, Fin.ext_iff]
private theorem second_time (j : Fin 3) : (secondReceipt j).duration = 1 := by
  change (active (secondBatch j).slots).sup _ = _
  rw [second_active, Finset.sup_singleton]
  change (observe limits 1 (secondBatch j) (paths j (secondBatch j))).time _ = 1
  fin_cases j <;> norm_num [observe, secondBatch, second_slots, paths, limits,
    CallTrace.stop, second_interface]
private theorem second_tokens (j : Fin 3) : (secondReceipt j).tokens = 2 := by
  change (observe limits 1 (secondBatch j) _).tokens = _
  rw [observe_tokens, second_active, Finset.sum_singleton]
  fin_cases j <;> simp [paths, secondBatch, second_slots]
private theorem resources (j : Fin 3) :
    tokenBill (mem2 j).events = 5 ∧ elapsed (mem2 j).events = 2 ∧
      (mem2 j).privateState.used = Finset.univ.filter (fun i => i.val = 0 ∨ i.val = j.val + 1) := by
  have hu : (mem2 j).privateState.used =
      active (secondBatch j).slots ∪ active firstBatch.slots := by
    simp [mem2, mem1, mem0, Memory.record, commit, ConcurrentBatch.initial,
      firstReceipt, secondReceipt, observe]
  refine ⟨?_, ?_, ?_⟩
  · simp only [mem2, mem1, mem0, Memory.record, tokenBill, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, replyOf, first_tokens, second_tokens]
    norm_num
  · simp only [mem2, mem1, mem0, Memory.record, elapsed, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, replyOf, first_time, second_time]
    norm_num
  · rw [hu, first_active, second_active]
    ext i
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.ext_iff, Fin.val_zero]
    tauto

private theorem feedback_law (j : Fin 3) :
    (Feedback.run (environment limits sample) 2 start (fun _ => ⟨[], [], 0⟩)
      (mem0 j) request).map (fun outcome =>
        (RuntimeControl.result outcome.state, outcome.memory)) =
      PMF.pure ([true, false, true, false, true, false], mem2 j) := by
  have hsecond (channels : Unit → Turing.MultiTapeMachine.Channel Bool) :
      (Feedback.run (environment limits sample) 1 (second j) channels (mem1 j)
        request).map (fun outcome =>
          (RuntimeControl.result outcome.state, outcome.memory)) =
          PMF.pure ([true, false, true, false, true, false], mem2 j) := by
    simp only [Feedback.run, second_live, Bool.false_eq_true, ite_false, source_second,
      bind, PMF.pure_bind, PMF.pure_map]
    change PMF.pure (RuntimeControl.result (done j), mem2 j) = _
    rw [done_output]
  simp only [Feedback.run, start_live, Bool.false_eq_true, ite_false, source_first, bind,
    PMF.pure_bind]
  exact hsecond _

-- Actual decoded machine tape output, not merely a host-side mathematical policy.
private theorem native_law (j : Fin 3) :
    ((NativeUnboundedExecution.terminal controller.program (environment limits sample)
      ⟨controller.program.initialConfig (startupEncoding (original, 3)), mem0 j⟩).map
        (Option.map (NativeReplyContext.observe controller.context))).map
          (fun outcome => outcome.map (fun final => (final.output, final.memory))) =
      PMF.pure (some ([true, false, true, false, true, false], mem2 j)) := by
  rw [controller_law]
  simp only [PMF.map_comp, Function.comp_def]
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some, PMF.pure_map, start] using
    congrArg (PMF.map some) (feedback_law j)

-- Joint native output, bill and duration, with the source seed kept hidden from
-- the program's original input. No separate cost or deadline law is assumed.
private theorem native_joint (j : Fin 3) :
    ((NativeUnboundedExecution.terminal controller.program (environment limits sample)
      ⟨controller.program.initialConfig (startupEncoding (original, 3)), mem0 j⟩).map
        (Option.map (NativeReplyContext.observe controller.context))).map
          (fun outcome => outcome.map (fun final =>
            (final.output, tokenBill final.memory.events, elapsed final.memory.events))) =
      PMF.pure (some ([true, false, true, false, true, false], (5 : ℝ≥0), (2 : ℝ≥0))) := by
  obtain ⟨hb, ht, _⟩ := resources j
  have h := congrArg (PMF.map (fun outcome => outcome.map
    (fun (word, memory) => (word, tokenBill memory.events, elapsed memory.events)))) (native_law j)
  simpa only [PMF.map_comp, Function.comp_def, PMF.pure_map, Option.map_map,
    Option.map_some, hb, ht] using h

example :
    (do
      let j ← PMF.uniformOfFintype (Fin 3)
      ((NativeUnboundedExecution.terminal controller.program (environment limits sample)
        ⟨controller.program.initialConfig (startupEncoding (original, 3)), mem0 j⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).map
            (fun outcome => outcome.map (fun final =>
              (final.output, tokenBill final.memory.events, elapsed final.memory.events)))) =
      PMF.pure (some ([true, false, true, false, true, false], (5 : ℝ≥0), (2 : ℝ≥0))) := by
  simp only [native_joint, bind, PMF.bind_const]

-- The named controller's general protocol endpoint also bounds actual native
-- outcomes by the configured deadline, without an assumed execution invariant.
example (j : Fin 3)
    (outcome : Option (NativeReplyContext.Observation (ServerState 4 (Fin 3))))
    (ho : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample)
        ⟨controller.program.initialConfig (startupEncoding (original, 3)), mem0 j⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧ elapsed final.memory.events ≤ 2 := by
  obtain ⟨final, he, hinv⟩ := controller_protocol 3 original limits sample j outcome ho
  obtain ⟨hw, _, htime, _⟩ := hinv
  obtain ⟨_, _, hd, _, _⟩ := hw
  refine ⟨final, he, ?_⟩
  rw [htime]
  exact hd

-- Nontrivial positive-cost oracle time and the global no-reuse ledger are derived.
example (j : Fin 3) : tokenBill (mem2 j).events = 5 ∧ elapsed (mem2 j).events = 2 ∧
    (mem2 j).events.length = 2 := by
  exact ⟨(resources j).1, (resources j).2.1, rfl⟩

-- The actual hidden source state may be sampled once with full support. The
-- same fixed source sampler then preserves it across both queries; no independent
-- resampling of the specialist response or host-supplied continuation is used.
example :
    (do
      let j ← PMF.uniformOfFintype (Fin 3)
      ((NativeUnboundedExecution.terminal controller.program (environment limits sample)
        ⟨controller.program.initialConfig (startupEncoding (original, 3)), mem0 j⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).map
            (fun outcome => outcome.map (fun final => (final.output, final.memory)))) =
      (PMF.uniformOfFintype (Fin 3)).map fun j =>
        some ([true, false, true, false, true, false], mem2 j) := by
  simp only [native_law, bind]
  exact PMF.bind_pure_comp _ _

-- The reported mask is an actual weight-one cover of the nonempty source WSC.
example : complete { SourceEncoding.toNative original with proposals := [[0, 2, 4]] } = true ∧
    cost (SourceEncoding.toNative original) [0, 2, 4] = 1 := by decide +kernel

-- The requested residual keeps its original row labels and local subinstance.
example (j : Fin 3) : (query (second j)).candidates = [2 * j.val, 2 * j.val + 1] := by
  have heta : ∀ q : Query, q = ⟨q.system, q.points⟩ := by intro q; cases q; rfl
  rw [heta (query (second j)), second_points]
  change (Query.mk (SourceEncoding.toNative original) _).candidates = _
  fin_cases j <;> decide +kernel

-- Empty original input stops on computed completion before any source query,
-- for every runtime role count and every correlated environment.
example {P : Type} (z : ℕ) (env : Environment Unit P) (memory : Memory Unit P) :
    let empty : SourceEncoding.Input := ⟨[], [], [], 1⟩
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (startupEncoding (empty, z)), memory⟩).map
        (Option.map (NativeReplyContext.observe controller.context)) =
      PMF.pure (some (⟨tapeOfList (RuntimeControl.packet (NativeResidualSelector.initial z empty)),
        [], memory⟩ : NativeReplyContext.Observation P)) := by
  dsimp only
  rw [controller_law]
  have hd : (Packets.decision
      (NativeResidualSelector.initial z ⟨[], [], [], 1⟩).work).1 = true := rfl
  have hs : RuntimeControl.stopped
      (NativeResidualSelector.initial z ⟨[], [], [], 1⟩) = true := by
    simp only [RuntimeControl.stopped, hd, Bool.or_true]
  rw [Feedback.run]
  simp only [hs, ↓reduceIte, PMF.pure_map]
  rfl

-- The generic codec is also instantiated on the existing five six-point X3C
-- blocks with overlapping unused triples, not just this three-block execution.
private def largerSource : SourceEncoding.Input :=
  NativeResidualEncoding.source StochasticOracleResidualCover.blocks
    (Fintype.equivFin _).symm (Fintype.equivFin _).symm

example : largerSource.dual.length = 30 := by
  rw [largerSource, NativeResidualEncoding.ground_length]
  rw [ResidualCover.universe_card]
  norm_num [StochasticOracleResidualCover.blocks, StochasticOracleResidualCover.block]

example (e f : ResidualCover.Point StochasticOracleResidualCover.blocks) :
    (Fintype.equivFin _ e).val ∈ NativeResidualSelector.region
        (SourceEncoding.toNative largerSource) (Fintype.equivFin _ f).val ↔ e.1 = f.1 := by
  simpa only [largerSource, Equiv.symm_apply_apply] using
    NativeResidualEncoding.region StochasticOracleResidualCover.blocks
      (Fintype.equivFin _).symm (Fintype.equivFin _).symm
      (Fintype.equivFin _ f) (Fintype.equivFin _ e)

-- The larger overlapping X3C input acquires its validity from the source
-- construction, rather than an independently supplied rational certificate.
example : SourceEncoding.Valid largerSource :=
  NativeResidualEncoding.source_valid StochasticOracleResidualCover.blocks
    (Fintype.equivFin _).symm (Fintype.equivFin _).symm (by norm_num)

private def largerNative : PartialCover.Instance ℕ ℕ :=
  NativeResidualEncoding.nativeInstance StochasticOracleResidualCover.blocks
    (Fintype.equivFin _).symm (Fintype.equivFin _).symm (by norm_num)

private def largerFamily : Finset ℕ :=
  (ResidualCover.payload StochasticOracleResidualCover.blocks Finset.univ).map
    (NativeResidualEncoding.candidateLabel StochasticOracleResidualCover.blocks
      (Fintype.equivFin _).symm)

-- The actual decoded native WSC has a thirty-element ground, a weight-one
-- integral cover, and a lower bound against every native candidate family,
-- including arbitrary out-of-range labels. No optimum is an input.
example : largerNative.ground.card = 30 ∧
    largerNative.covered largerFamily = largerNative.ground ∧
    largerNative.cost largerFamily = 1 ∧
    ∀ F, largerNative.covered F = largerNative.ground → 1 ≤ largerNative.cost F := by
  have hg : largerNative.ground.card = 30 := by
    rw [largerNative, NativeResidualEncoding.ground_label, Finset.card_map,
      Finset.card_univ, ResidualCover.universe_card]
    norm_num [StochasticOracleResidualCover.blocks, StochasticOracleResidualCover.block]
  exact ⟨hg, NativeResidualEncoding.native_primal_optimum
    StochasticOracleResidualCover.blocks (Fintype.equivFin _).symm
      (Fintype.equivFin _).symm (by norm_num)⟩

-- All five hidden missing blocks give their own nonempty residual and both
-- source responses pass the interpreted native local test at rho=1.
example (j : Fin 5) :
    let label := NativeResidualEncoding.candidateLabel StochasticOracleResidualCover.blocks
      (Fintype.equivFin _).symm
    let near := (ResidualCover.payload StochasticOracleResidualCover.blocks
      (Finset.univ.erase j)).map label
    let specialist := (ResidualCover.specialist StochasticOracleResidualCover.blocks j).map label
    largerNative.Certified 1 ∅ near ∧ largerNative.Certified 1 near specialist ∧
      (largerNative.ground \ largerNative.covered near).card = 6 := by
  dsimp only
  have hc := NativeResidualEncoding.native_responses_certified
    StochasticOracleResidualCover.blocks (Fintype.equivFin _).symm
      (Fintype.equivFin _).symm (by norm_num) j
  refine ⟨hc.1, hc.2, ?_⟩
  rw [largerNative, NativeResidualEncoding.native_near_residual, Finset.card_map]
  simp [ResidualCover.groundBlock, StochasticOracleResidualCover.blocks,
    StochasticOracleResidualCover.block]

end CslibFrontierTests.StochasticOracleNativeResidualSelector
