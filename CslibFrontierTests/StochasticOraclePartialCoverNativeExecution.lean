/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverNativeExecution
import Mathlib.Tactic

/-!
# Actual native greedy batch on a correlated oracle

One original oracle covers the singleton ground. The program derives two calls
from q=1/2 and δ=1/4. Its two reports are positively correlated: the first succeeds
on two of four equiprobable worlds and the second on three, with both succeeding
on two. After a first failure the second still succeeds with probability one half.
The same compiled program's actual tape output succeeds with probability 3/4.
Both actual invoices and oracle time are charged; the hidden next state is kept.
-/

noncomputable section
open Cslib Cslib.Probability StochasticOracle PartialCover NativeExecution
open NativeRetention ConcurrentBatch Turing Turing.MultiTapeTM NativeOpenExecution
open scoped NNReal ENNReal

private def input : NativeExecution.Input :=
  ⟨⟨⟨1, [⟨99, [true], 1⟩], ⟨1 / 2, 1 / 4⟩⟩, by
    constructor
    · norm_num
    · constructor <;> norm_num⟩, ⟨[[0]], [1], [1], 1, []⟩, rfl⟩

private theorem count_two : GreedyNative.count input.planner = 2 := by
  let t := GreedyNative.thresholdInput input.planner
  have hlo := (Instance.pow_le_iff_rationalRepetitions_le t.val.q t.val.budget
    t.property.q_pos t.property.q_lt_one t.property.budget_pos 2).mp
      (by norm_num [t, GreedyNative.thresholdInput, GreedyNative.scaled, input])
  have hhi := (Instance.pow_le_iff_rationalRepetitions_le t.val.q t.val.budget
    t.property.q_pos t.property.q_lt_one t.property.budget_pos 1).not.mp
      (by norm_num [t, GreedyNative.thresholdInput, GreedyNative.scaled, input])
  change GreedyNative.count input.planner ≤ 2 at hlo
  change ¬GreedyNative.count input.planner ≤ 1 at hhi
  omega

private theorem labels_two : GreedyNative.labels input.planner = [0, 0] := by
  rw [GreedyNative.labels, GreedyNative.plan, count_two]
  norm_num [Algorithms.Lean.Multicover.Native.batch, Algorithms.Lean.Multicover.Native.initial,
    Algorithms.Lean.Multicover.Native.advance, Algorithms.Lean.Multicover.Native.select,
    Algorithms.Lean.Multicover.Native.consider, Algorithms.Lean.Multicover.Native.gain,
    Algorithms.Lean.Multicover.Native.ratio, Algorithms.Lean.Multicover.Native.decrement,
    GreedyNative.numberedRows, input, Function.iterate_succ_apply', List.range_succ]

private theorem live : RuntimeControl.stopped (NativeExecution.initial input) = false := by
  rw [RuntimeControl.stopped]
  simp only [NativeExecution.initial, labels_two, List.length_cons, List.length_nil]
  norm_num [input,
    Packets.decision, Packets.assemble, complete, covered, ground, retain, List.range_succ]

private def limits : Limits (GreedyNative.labels input.planner).length :=
  ⟨fun _ => 1, by intro _; norm_num, 1, 1⟩
private def good (a : Fin 4) (i : ℕ) : Bool := if i = 0 then decide (a.val < 2)
  else decide (a.val < 3)
private def path (a : Fin 4) (i : ℕ) : CallTrace :=
  ⟨some (1, [good a i]), fun _ => 1, by intro _ _ _; rfl⟩
private def sample : Sampler (GreedyNative.labels input.planner).length (Fin 4) :=
  fun _ _ => (PMF.uniformOfFintype (Fin 4)).map fun a => (fun i => path a i.val, a)
private def receipt (a : Fin 4) :=
  ConcurrentBatch.observe limits 1 (batch input (live_nonempty input live)) (fun i => path a i.val)
private def memory : Memory Unit (ServerState (GreedyNative.labels input.planner).length (Fin 4)) :=
  ⟨ConcurrentBatch.initial 0, []⟩

private theorem word (a : Fin 4) :
    (finished input memory (replyOf (receipt a))
      (commit (ConcurrentBatch.initial 0) (receipt a) a)).output =
      if a.val < 3 then [true] else [] := by
  have hn : (GreedyNative.labels input.planner).length = 2 := by rw [labels_two]; rfl
  have hp : Packets.families (GreedyNative.labels input.planner).length 1
      (replyOf (receipt a)).word =
      [if good a 0 then [0] else [], if good a 1 then [0] else []] := by
    simp only [replyOf, Packets.families_report]
    fin_cases a <;>
      norm_num [receipt, ConcurrentBatch.observe, batch, slots, path, good, limits,
        CallTrace.report, CallTrace.response, hn, List.ofFn_succ, proposals, decodeFamily,
        sourceIndices, List.filterMap_cons, List.filterMap_nil, Finset.univ_unique,
        List.finRange_succ, List.finRange_zero]
  unfold finished RuntimeControl.result RuntimeControl.afterReply NativeExecution.initial
  simp only [Packets.decision, Packets.assemble, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (if complete (⟨[[0]], [1], [1], 1,
      Packets.families (GreedyNative.labels input.planner).length 1 (replyOf (receipt a)).word⟩ :
        NativeRetention.Input) then output ⟨[[0]], [1], [1], 1,
      Packets.families (GreedyNative.labels input.planner).length 1 (replyOf (receipt a)).word⟩
    else []) = _
  rw [hp]
  fin_cases a <;>
    norm_num [good, complete, output, retain, NativeRetention.step, NativeRetention.certified,
      NativeRetention.normalize, newly, covered, ground, population, cost, price, List.range_succ]


-- The wire packet decodes to a nonempty preformed two-call batch. No retry label is reused.
example : admit limits (ConcurrentBatch.initial (0 : Fin 4)) (requests input) =
    some (batch input (live_nonempty input live)) :=
  admit_requests input _ limits 0 (by norm_num [limits]) (by norm_num [limits])

-- This equality concerns the actual machine's emitted word.
private theorem actual_words :
    (NativeUnboundedExecution.terminal controller.program (environment limits sample)
      ⟨controller.program.initialConfig (encoding input), memory⟩).map
      (Option.map fun world => world.config.tapes.output) =
      (PMF.uniformOfFintype (Fin 4)).map
        (fun a => some (if a.val < 3 then [true] else [])) := by
  have h := congrArg (PMF.map (Option.map NativeReplyContext.Observation.output))
    (source_law input limits sample 0 live (by norm_num [limits]) (by norm_num [limits]))
  simp only [PMF.map_comp, Option.map_map, Function.comp_def, NativeReplyContext.observe] at h
  change (NativeUnboundedExecution.terminal controller.program (environment limits sample)
    ⟨controller.program.initialConfig (encoding input), memory⟩).map _ = _ at h
  rw [h]
  simp only [sample, PMF.map_comp, ConcurrentBatch.initial]
  congr 1
  funext a
  exact congrArg some (word a)

example (a : Fin 4) : (receipt a).tokens = 2 ∧ (receipt a).duration = 1 := by
  have hn : (GreedyNative.labels input.planner).length = 2 := by rw [labels_two]; rfl
  have hne : (Finset.univ : Finset (Fin (GreedyNative.labels input.planner).length)).Nonempty :=
    ⟨⟨0, by rw [labels_two]; decide⟩, Finset.mem_univ _⟩
  norm_num [receipt, Exchange.tokens, Exchange.duration, ConcurrentBatch.observe, active_slots,
    batch, slots, active, path, limits, CallTrace.report, CallTrace.stop, hn, Finset.univ_fin2,
    Finset.sup_const hne]

-- Genuine correlation: P(A)=1/2, P(B)=3/4, P(A and B)=1/2 != 3/8.
example :
    ((PMF.uniformOfFintype (Fin 4)).map (fun a => good a 0)) true = 1 / 2 ∧
    ((PMF.uniformOfFintype (Fin 4)).map (fun a => good a 1)) true = 3 / 4 ∧
    ((PMF.uniformOfFintype (Fin 4)).map (fun a => good a 0 && good a 1)) true = 1 / 2 := by
  constructor
  · norm_num [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, good, PMF.uniformOfFintype_apply]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]
  · constructor <;>
      norm_num [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, good, PMF.uniformOfFintype_apply]
    all_goals
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

private theorem success_mass : ((PMF.uniformOfFintype (Fin 4)).map
    (fun a => some (if a.val < 3 then [true] else []))) (some [true]) = 3 / 4 := by
  norm_num [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, PMF.uniformOfFintype_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

example :
    ((NativeUnboundedExecution.terminal controller.program (environment limits sample)
      ⟨controller.program.initialConfig (encoding input), memory⟩).map
      (Option.map fun world => world.config.tapes.output)) (some [true]) = 3 / 4 := by
  rw [actual_words]
  exact success_mass

-- Arbitrary finite reply lengths go through the full reader, with their actual invoice and memory.
example (reply : Word) :
    let env : Environment Unit Unit := fun _ _ => PMF.pure (⟨reply, 17, 3⟩, ())
    let mem : Memory Unit Unit := ⟨(), []⟩
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (encoding input), mem⟩).map
      (Option.map (NativeReplyContext.observe controller.context)) =
      PMF.pure (some (finished input mem ⟨reply, 17, 3⟩ ())) := by
  dsimp only
  rw [live_law _ _ _ live, PMF.pure_map]

-- The same native initializer, on an empty plan, exits without querying even a stateful oracle.
example {P : Type} (env : Environment Unit P) (mem : Memory Unit P) :
    let empty : NativeExecution.Input :=
      ⟨⟨{ input.planner.val with rows := [] },
        ⟨input.planner.property.ground_pos, input.planner.property.parameters_valid⟩⟩,
        input.system, input.ground_eq⟩
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (encoding empty), mem⟩).map
      (Option.map (NativeReplyContext.observe controller.context)) =
      PMF.pure (some (⟨tapeOfList (RuntimeControl.packet (NativeExecution.initial empty)),
        RuntimeControl.result (NativeExecution.initial empty), mem⟩ :
          NativeReplyContext.Observation P)) := by
  dsimp only
  apply stopped_law
  have he : GreedyNative.labels
      (⟨{ input.planner.val with rows := [] },
        ⟨input.planner.property.ground_pos, input.planner.property.parameters_valid⟩⟩ :
          GreedyNative.Input) = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun j hj => Nat.not_lt_zero j (GreedyNative.labels_lt _ hj)
  simp [RuntimeControl.stopped, NativeExecution.initial, he]

private theorem invoice_cap (a : Fin 4)
    (i : Fin (GreedyNative.labels input.planner).length) :
    ((path a i.val).accrued (limits.cutoff i) : ℝ) ≤
      (GreedyNative.oracleAt input.planner.val
        ((GreedyNative.labels input.planner).get i)).cost := by
  have he : (GreedyNative.labels input.planner).get i = 0 := by
    have hm := List.get_mem (GreedyNative.labels input.planner) i
    simpa only [labels_two, List.mem_cons, List.not_mem_nil, or_false, or_self] using hm
  rw [he]
  norm_num [path, limits, GreedyNative.oracleAt, input,
    Algorithms.Lean.Multicover.Native.interpret]

-- Per-call accrued bounds instantiate the general native-receipt resource theorem.
example (a : Fin 4) :
    ((receipt a).tokens : ℝ) ≤
      (Algorithms.Lean.Multicover.bill
        ((GreedyNative.labels input.planner).map (GreedyNative.oracleAt input.planner.val)) : ℝ) ∧
      (receipt a).duration ≤ limits.deadline := by
  apply receipt_resources input (live_nonempty input live) limits (fun i => path a i.val)
  exact invoice_cap a

-- The same actual terminal law carries the whole native bill/deadline/source invariant.
example (outcome : Option (NativeReplyContext.Observation
      (ServerState (GreedyNative.labels input.planner).length (Fin 4))))
    (h : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample) ⟨controller.program.initialConfig (encoding input), memory⟩).map
        (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧ (tokenBill final.memory.events : ℝ) ≤ 2 ∧
      elapsed final.memory.events ≤ 1 ∧ final.memory.events.length = 1 := by
  obtain ⟨final, he, hb, hd, _, ht⟩ := native_resources input limits sample 0 live
    (by norm_num [limits]) (by norm_num [limits]) (by
      intro pair hp i
      obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      exact invoice_cap a i) outcome h
  refine ⟨final, he, ?_, hd, ht⟩
  have hbill : (Algorithms.Lean.Multicover.bill
      ((GreedyNative.labels input.planner).map (GreedyNative.oracleAt input.planner.val)) : ℝ) =
        2 := by
    rw [labels_two]
    norm_num [Algorithms.Lean.Multicover.bill, GreedyNative.oracleAt, input,
      Algorithms.Lean.Multicover.Native.interpret]
  rw [hbill] at hb
  exact hb

-- A canceled first call still has an invoice; its later completed peer is processed.
example :
    let report : Report 2 := fun i => if i.val = 0 then some (none, 1)
      else some (some [true], 1)
    Packets.families 2 1 (encodeReport report) = [[0]] := by
  dsimp only
  rw [Packets.families_report]
  norm_num [proposals, List.ofFn_succ, decodeFamily, sourceIndices,
    List.filterMap_cons, List.filterMap_nil, Finset.univ_unique,
    List.finRange_succ, List.finRange_zero]
