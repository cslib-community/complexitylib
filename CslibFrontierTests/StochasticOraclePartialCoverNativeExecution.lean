/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverNativeRisk
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


private theorem valid : Valid input.system := by
  constructor
  · intro j; cases j <;> norm_num [input]
  · intro e; cases e <;> norm_num [input]
  · intro j; cases j <;> norm_num [elements, ground, input]

private theorem eligibility : ∀ e : Fin input.planner.val.ground,
    ∃ row ∈ input.planner.val.rows, row.mask[e.val]?.getD false = true := by
  intro e
  have he : e.val = 0 := by have := e.isLt; change e.val < 1 at this; omega
  exact ⟨⟨99, [true], 1⟩, by simp [input], by simp [he]⟩

-- The source optimum is finite here: two calls have risk 1/4 and total cost two.
-- The finite oracle dimension is computed from a semireducible input encoding.
set_option backward.isDefEq.respectTransparency false in
example : riskOptimum input ≤ 2 := by
  let row := GreedyNative.oracleAt input.planner.val 0
  have hb : Benchmark input [row, row] := by
    constructor
    · intro r hr
      have : r = row := by simpa using hr
      subst r
      simpa only [row, GreedyNative.oracleAt, input, List.getD, List.getElem?_cons_zero,
        Option.getD_some, List.map_cons, List.map_nil] using
          (List.mem_singleton_self
            (Algorithms.Lean.Multicover.Native.interpret 1 ⟨99, [true], 1⟩))
    · have hc := computed_risk input valid eligibility
      simpa only [labels_two, List.map_cons, List.map_nil] using hc
  exact (iInf_le_of_le ⟨[row, row], hb⟩ (by
    norm_num [row, Algorithms.Lean.Multicover.bill, GreedyNative.oracleAt, input,
      Algorithms.Lean.Multicover.Native.interpret]))

-- The combined native bill/factor/OPT conclusion is for the actual correlated
-- terminal law already shown above to emit the singleton mask with probability 3/4.
example (outcome : Option (NativeReplyContext.Observation
      (ServerState (GreedyNative.labels input.planner).length (Fin 4))))
    (h : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample) ⟨controller.program.initialConfig (encoding input), memory⟩).map
        (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧
      (tokenBill final.memory.events : ℝ≥0∞) ≤
        ENNReal.ofReal (Asymptotics.factor (1 / 2) (1 / 4) 1) * riskOptimum input ∧
      elapsed final.memory.events ≤ 1 := by
  simpa only [input, limits, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    native_bill_le_riskOptimum input valid eligibility
    (by intro row hr; simp only [input, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst row; norm_num)
    (by norm_num [input]) limits sample 0 (by norm_num [limits])
    (by norm_num [limits]) (by
      intro pair hp i
      obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      exact invoice_cap a i) outcome h

private def draw (a : Fin 4) : Draw input (Fin 4) := (fun i => path a i.val, a)
private def joint := sample (ConcurrentBatch.initial 0) (batch input (live_nonempty input live))
private def responses : ℕ → Draw input (Fin 4) → Finset (Fin 1) :=
  NativeExecution.response input limits live
private def kernel := Disintegration.kernel joint responses

-- Normalize the runtime-dependent finite response dimension before reading its mask.
set_option backward.isDefEq.respectTransparency false in
private theorem response_at (k : Fin 2) (a : Fin 4) :
    responses k.val (draw a) = if good a k.val then {0} else ∅ := by
  have hn : (GreedyNative.labels input.planner).length = 2 := by rw [labels_two]; rfl
  simp only [responses, NativeExecution.response, dite_eq_left (show k.val <
    (GreedyNative.labels input.planner).length by omega)]
  fin_cases k <;> fin_cases a
  all_goals
    ext i
    change Fin 1 at i
    fin_cases i
    norm_num [NativeExecution.jointReceipt,
      NativeExecution.family, draw, ConcurrentBatch.observe, batch, slots, path,
      limits, CallTrace.report, CallTrace.response, hn, good, decodeFamily,
      List.finRange_succ, List.finRange_zero, Finset.univ_unique, input]

private theorem singleton_families (P : Finset (Fin 1)) :
    P = ∅ ∨ P = {0} := by
  by_cases h : 0 ∈ P
  · right; ext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i; simpa using h
  · left; ext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i; simpa using h

private theorem posterior_mass (h : List (Finset (Fin 1)))
    (hh : h = [] ∨ h = [∅]) : (kernel h).weight {0} = 1 / 2 := by
  classical
  have hf := PMF.posterior_map_factor joint (Disintegration.history responses h.length)
    (responses h.length) h ({0} : Finset (Fin 1))
  have hr := congrArg ENNReal.toReal hf
  have h0 (a : Fin 4) := response_at 0 a
  have h1 (a : Fin 4) := response_at 1 a
  change ∀ a, responses 0 (fun i => path a i.val, a) = _ at h0
  change ∀ a, responses 1 (fun i => path a i.val, a) = _ at h1
  have hl : (joint.map (Disintegration.history responses h.length) h).toReal =
      if h = [] then 1 else 1 / 2 := by
    obtain rfl | rfl := hh <;>
      norm_num [joint, sample, PMF.map_comp, Disintegration.history,
        h0,
        draw, PMF.map_apply, tsum_fintype, Fin.sum_univ_succ,
        PMF.uniformOfFintype_apply, ENNReal.toReal_add, ENNReal.toReal_inv, good]
  have hj : ((joint.map fun a =>
      (Disintegration.history responses h.length a, responses h.length a)) (h, {0})).toReal =
      if h = [] then 1 / 2 else 1 / 4 := by
    obtain rfl | rfl := hh <;>
      norm_num [joint, sample, PMF.map_comp, Disintegration.history,
        h0,
        h1,
        draw, PMF.map_apply, tsum_fintype, Fin.sum_univ_succ,
        PMF.uniformOfFintype_apply, ENNReal.toReal_add, ENNReal.toReal_inv, good]
  rw [ENNReal.toReal_mul, hl, hj] at hr
  change (((PMF.posterior joint (Disintegration.history responses h.length) h).map
    (responses h.length)) {0}).toReal = _
  obtain rfl | rfl := hh <;> norm_num at hr ⊢ <;> linarith


-- Normalize the concrete source instance through its computed finite dimension.
set_option backward.isDefEq.respectTransparency false in
private theorem source_envelopes : (sourceInstance input valid).Admissible 1 (1 / 2)
    kernel [] ∅ (eligible input) := by
  classical
  have he : eligible input = [{0}, {0}] := by
    rw [eligible, labels_two]
    norm_num [GreedyNative.oracleAt, input, Algorithms.Lean.Multicover.Native.interpret,
      Finset.univ_unique]
    rfl
  rw [he]
  have event (h : List (Finset (Fin 1))) (hh : h = [] ∨ h = [∅]) :
      Instance.event (kernel h) (fun P => (sourceInstance input valid).Certified 1 ∅ P ∧
        0 ∈ (sourceInstance input valid).covered P) = 1 / 2 := by
    unfold Instance.event Cslib.Optimization.OneConstraint.Distribution.mean
    calc
      _ = ∑ P, (kernel h).weight P * (if P = {0} then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro P _
        obtain rfl | rfl := singleton_families P <;>
          norm_num [sourceInstance, Instance.reindex, instanceOf, Instance.Certified,
            Instance.covered, Instance.cost, elements, ground, input]
      _ = (kernel h).weight {0} := by simp
      _ = 1 / 2 := posterior_mass h hh
  constructor
  · intro e he _
    have : e = 0 := by simpa using he
    subst e
    exact (event [] (Or.inl rfl)).ge
  · intro P _
    obtain rfl | rfl := singleton_families P
    · constructor
      · intro e he _
        have : e = 0 := by simpa using he
        subst e
        have hz : (sourceInstance input valid).step 1 ∅ ∅ = ∅ := by
          simp [Instance.step, Instance.Certified, Instance.covered]
        erw [hz]
        exact (event [∅] (Or.inr rfl)).ge
      · intro _ _; trivial
    · constructor
      · intro e he hn
        have : e = 0 := by simpa using he
        subst e
        norm_num [Instance.step, sourceInstance, Instance.reindex, instanceOf,
          Instance.Certified, Instance.covered, Instance.cost, elements, ground, input] at hn
      · intro _ _; trivial

-- The posterior-envelope premise is proved for this actual correlated sampler.
-- This applies the source success theorem to the compiled controller's tape event.
example : (3 / 4 : ℝ) ≤
    ((((NativeUnboundedExecution.terminal controller.program (environment limits sample)
      ⟨controller.program.initialConfig (encoding input), memory⟩).map
        (Option.map (NativeReplyContext.observe controller.context))).map
          (NativeExecution.certified input valid 1)) true).toReal := by
  have hq : 1 - (input.planner.val.parameters.q : ℝ) = 1 / 2 := by norm_num [input]
  have hρ : (input.system.rho : ℝ) = 1 := by norm_num [input]
  have h := native_success input valid eligibility (by norm_num [input]) limits sample 0
    (by norm_num [limits]) (by norm_num [limits]) (by
      rw [hq, hρ]
      change (sourceInstance input valid).Admissible 1 (1 / 2) kernel [] ∅ (eligible input)
      exact source_envelopes)
  convert h using 1 <;> norm_num [input, limits, memory]
