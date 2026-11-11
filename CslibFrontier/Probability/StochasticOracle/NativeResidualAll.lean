/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualAttainment
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual native all-specialist strategy

[Wang2027], Theorem 6, PDF p. 13. All specialist requests are preformed from
the known runtime role subuniverses. The hidden covers are obtained only through
the source report and are locally certified by the same native retention code.

## Main definitions

* `batch`, `receipt`, `finished`, `memory`: actual concurrent source transaction and update.

## Main results

* `native_law`, `native_resources`: original-input compiled output and joint resources.
* `native_certified`, `native_selectionOnly`: actual success and selection-only admission.
* `native_expected_cost`, `native_cost_mem`, `native_upper`: exact attained bill
  and native upper bound.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualAll
open Turing Turing.MultiTapeTM NativeOpenExecution Finset NativeRetention ResidualCover
open NativeResidualEncoding ConcurrentBatch NativeResidualRouting NativeResidualAttainment
open Cslib.Optimization.OneConstraint
open scoped NNReal ENNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

private theorem roleAt (i : Fin (z + 1)) :
    NativeResidualSelector.queryEncoding
      ⟨SourceEncoding.toNative (source T points candidates), (universes T points).getD i.val []⟩ =
      NativeResidualOracle.query T points candidates i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [universes, NativeResidualOracle.query]
  · simp [universes, NativeResidualOracle.query, List.getD_eq_getElem?_getD]

private theorem all_slots :
    slots (NativeResidualRouting.initial false (input T points candidates)) =
    fun i : Fin (z + 1) => if 0 < i.val then
      some (NativeResidualOracle.query T points candidates i) else none := by
  have ht : (NativeResidualRouting.initial false (input T points candidates)).turns = 1 := rfl
  have hh : (NativeResidualRouting.initial false (input T points candidates)).work.history.isEmpty =
      true := rfl
  have hx : (NativeResidualRouting.initial false (input T points candidates)).work.system =
      SourceEncoding.toNative (source T points candidates) := rfl
  funext (i : Fin (z + 1))
  simp only [slots, selected, ht, Nat.reduceEqDiff, ite_false, decide_true,
    Bool.true_and, hh, Bool.true_or, Bool.and_true, roles_initial T points candidates false, hx,
    roleAt T points candidates i, decide_eq_true_eq]

/-- All specialist queries, fixed before any source response; the near role is absent. -/
@[expose] def batch (hz : 0 < z) : ConcurrentBatch.Batch (z + 1) :=
  ⟨fun i => if 0 < i.val then some (NativeResidualOracle.query T points candidates i) else none,
    ⟨(⟨0, hz⟩ : Fin z).succ, by
      simp only [active, mem_filter, mem_univ, true_and]
      change (if 0 < 1 then some _ else (none : Option Word)).isSome = true
      rfl⟩⟩

private theorem active_batch (hz : 0 < z) :
    active (batch T points candidates hz).slots = univ.erase 0 := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp [active, batch]
  · have hn : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
    apply iff_of_true
    · apply Finset.mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      change (if 0 < i.val then some (NativeResidualOracle.query T points candidates i)
        else (none : Option Word)).isSome = true
      rw [ite_eq_left hn]
      rfl
    · exact Finset.mem_erase.mpr ⟨hi, mem_univ _⟩

private theorem calls_batch (hz : 0 < z) :
    NativeResidualOracle.calls (batch T points candidates hz) = specialistBatch := by
  rw [NativeResidualOracle.calls, active_batch]
  ext i
  simp [specialistBatch]

private theorem request_batch (hz : 0 < z) :
    request (NativeResidualRouting.initial false (input T points candidates)) =
      encodeBatch (batch T points candidates hz) := by
  rw [request_eq, all_slots]
  rfl

/-- Complete unit-latency receipt of the actual concurrent specialist batch. -/
@[expose] def receipt (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) : Exchange (z + 1) :=
  observe limits 1 (batch T points candidates hz)
    (NativeResidualOracle.paths T points candidates invoice (batch T points candidates hz) none)

private def answers (invoice : Fin (z + 1) → ℕ) : NativeResidualReplies.Answers T (z + 1) :=
  Fin.cases none (fun j => some (some (specialist T j), invoice j.succ))

private theorem report_eq (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) :
    (receipt T points candidates invoice hz).report = NativeResidualReplies.report T candidates
      (answers T invoice) := by
  have hp : NativeResidualOracle.paths T points candidates invoice (batch T points candidates hz)
      none = fun i => NativeResidualReplies.path T candidates
        (NativeResidualOracle.families T points candidates (batch T points candidates hz) none i)
        (invoice i) := rfl
  rw [receipt, hp, NativeResidualReplies.observe_report T candidates limits 1
    (batch T points candidates hz) _ invoice (fun _ => rfl) le_rfl]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [NativeResidualReplies.report, NativeResidualReplies.answersFor, answers, batch]
  · simp [NativeResidualReplies.report, NativeResidualReplies.answersFor, answers, batch,
      NativeResidualOracle.families, NativeResidualOracle.answer]

private theorem returned_eq (invoice : Fin (z + 1) → ℕ) :
    NativeResidualReplies.returned T (answers T invoice) = List.ofFn (specialist T) := by
  simp [NativeResidualReplies.returned, answers, List.ofFn_succ, List.ofFn_eq_map,
    List.filterMap_map]

/-- Runtime state after the one actual complete source report. -/
@[expose] def finished (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) : RuntimeControl.State :=
  RuntimeControl.afterReply (NativeResidualRouting.initial false (input T points candidates))
    (replyOf (receipt T points candidates invoice hz)).word

/-- Complete actual source memory, retaining every specialist invoice. -/
@[expose] def memory (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) :
    Memory Unit (ServerState (z + 1) Unit) :=
  initialMemory.record ((), encodeBatch (batch T points candidates hz))
    (replyOf (receipt T points candidates invoice hz))
    (commit (ConcurrentBatch.initial ()) (receipt T points candidates invoice hz) ())

private theorem resources (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) :
    (receipt T points candidates invoice hz).tokens = ∑ j : Fin z, invoice j.succ ∧
      (receipt T points candidates invoice hz).duration = 1 := by
  have h := NativeResidualReplies.observed_resources T candidates limits 1
    (batch T points candidates hz)
    (NativeResidualOracle.families T points candidates (batch T points candidates hz) none)
    invoice (fun _ => rfl) le_rfl
  have hp : NativeResidualOracle.paths T points candidates invoice (batch T points candidates hz)
      none = fun i => NativeResidualReplies.path T candidates
        (NativeResidualOracle.families T points candidates (batch T points candidates hz) none i)
        (invoice i) := rfl
  rw [receipt, hp]
  refine ⟨?_, h.2⟩
  rw [h.1, active_batch]
  have hs := Finset.sum_erase_add univ invoice (mem_univ (0 : Fin (z + 1)))
  rw [Fin.sum_univ_succ] at hs
  omega

private theorem completed_retained (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) :
    (coverInstance T hz).retain 1 ∅
      ([answers T invoice].reverse.flatMap (NativeResidualReplies.returned T)) =
        payload T univ := by
  have h := retain_specialists T hz (List.ofFn (id : Fin z → Fin z))
    (by rw [List.nodup_ofFn]; exact Function.injective_id) ∅ (by simp)
  have hu : (List.ofFn (id : Fin z → Fin z)).toFinset = univ := by ext i; simp
  simp only [List.map_ofFn, Function.comp_def, id_eq, hu, empty_union] at h
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, returned_eq T invoice, payload, biUnion_empty] using h

/-- The same source interface at a specified turn budget, with deadline two
and unit per-opportunity cutoffs. -/
@[expose] def config (budget : ℕ) : Limits (z + 1) :=
  ⟨fun _ => 1, by intro _; norm_num, 2, budget⟩

private theorem source (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 0 < z) (budget : ℕ) (hb : 0 < budget) :
    environment (config budget) (NativeResidualOracle.sample T points candidates P invoice)
      ((), request (NativeResidualRouting.initial false (input T points candidates)))
      initialMemory = PMF.pure (replyOf (receipt T points candidates invoice hz),
        (memory T points candidates invoice hz).privateState) := by
  have ha : admit (config budget) (ConcurrentBatch.initial ())
      (encodeBatch (batch T points candidates hz)) = some (batch T points candidates hz) := by
    simp [admit, decodeBatch_encode, config, ConcurrentBatch.initial, hb]
  change serve _ _ _ (ConcurrentBatch.initial ()) = _
  rw [request_batch T points candidates hz, serve_accepted _ _ _ _ _ ha]
  have hc : none ∉ (specialistBatch : ResidualCover.Batch z) := by simp [specialistBatch]
  simp only [NativeResidualOracle.sample, calls_batch T points candidates hz, reply, hc, ite_false,
    Distribution.toPMF_pure, PMF.pure_map]
  have hr : observe (config budget) ((config (z := z) budget).deadline -
      (ConcurrentBatch.initial (n := z + 1) ()).elapsed) (batch T points candidates hz)
      (NativeResidualOracle.paths T points candidates invoice (batch T points candidates hz) none) =
        receipt T points candidates invoice hz := by
    simp only [observe, config, ConcurrentBatch.initial, tsub_zero, receipt,
      NativeResidualAttainment.limits, min_self]
    norm_num
  rw [hr]
  rfl

private theorem state_work (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) :
    (finished T points candidates invoice hz).work =
      NativeResidualReplies.work T points candidates [answers T invoice] := by
  unfold finished
  change { (NativeResidualRouting.initial false (input T points candidates)).work with history :=
    (replyOf (receipt T points candidates invoice hz)).word :: [] } = _
  change { (NativeResidualRouting.initial false (input T points candidates)).work with history :=
    (encodeReport (receipt T points candidates invoice hz).report) :: [] } = _
  rw [report_eq]
  rfl

/-- Source certification and mask readback are derived for the actual complete
concurrent report, including arbitrary hidden exact covers and candidate labels. -/
theorem completed (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) :
    ∃ C, decodeFamily (input T points candidates).startup.system.rows.length
        (RuntimeControl.result (finished T points candidates invoice hz)) = some C ∧
      (nativeInstance T points candidates hz).covered (C.image Fin.val) =
        (nativeInstance T points candidates hz).ground ∧
      (nativeInstance T points candidates hz).cost (C.image Fin.val) = 1 := by
  let state := finished T points candidates invoice hz
  have hw := state_work T points candidates invoice hz
  have hret := NativeResidualReplies.retained T points candidates hz [answers T invoice]
  rw [completed_retained] at hret
  have hcover := (native_primal_optimum T points candidates hz).1
  have hcost := (native_primal_optimum T points candidates hz).2.1
  have hc : (Packets.decision state.work).1 = true := by
    rw [hw]
    exact (NativeResidualReplies.completion T points candidates hz _).mpr
      (by rw [completed_retained]; exact (primal_optimum T hz).1)
  let data := Packets.assemble state.work
  refine ⟨outputFamily data, ?_, ?_, ?_⟩
  · change decodeFamily data.rows.length (RuntimeControl.result state) = _
    simp only [RuntimeControl.result, hc, ite_true]
    exact decode_output data
  · change (nativeInstance T points candidates hz).covered
      ((outputFamily data).image (fun i : Fin data.rows.length => i.val)) = _
    rw [outputFamily_image]
    rw [show data = Packets.assemble
      (NativeResidualReplies.work T points candidates [answers T invoice]) from by rw [← hw]]
    rw [hret]
    exact hcover
  · change (nativeInstance T points candidates hz).cost
      ((outputFamily data).image (fun i : Fin data.rows.length => i.val)) = _
    rw [outputFamily_image]
    rw [show data = Packets.assemble
      (NativeResidualReplies.work T points candidates [answers T invoice]) from by rw [← hw]]
    rw [hret]
    exact hcost

/-- Full actual native one-batch output and source-memory law on the same input
and sampler, valid with either the one- or two-turn budget. -/
theorem native_law (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (budget : ℕ) (hb : 0 < budget) :
    (NativeUnboundedExecution.terminal (controller false).program
      (environment (config budget) (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(controller false).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
          (Option.map fun next => (next.config.tapes.output, next.memory)) =
      PMF.pure (some (RuntimeControl.result (finished T points candidates invoice (by omega)),
        memory T points candidates invoice (by omega))) := by
  have hl := congrArg (PMF.map (Option.map fun o : NativeReplyContext.Observation
      (ServerState (z + 1) Unit) => (o.output, o.memory)))
    (controller_law false _
      (environment (config budget) (NativeResidualOracle.sample T points candidates P invoice))
      (input T points candidates) initialMemory)
  simp only [PMF.map_comp, Function.comp_def, Option.map_map,
    NativeReplyContext.observe, Bool.false_eq_true, ite_false] at hl
  rw [hl]
  rw [Feedback.run, NativeResidualAttainment.initial_live T points candidates false hz]
  simp only [Bool.false_eq_true, ite_false, PMF.monad_bind_eq_bind,
    source T points candidates P invoice (by omega) budget hb, PMF.pure_bind,
    Feedback.run, PMF.pure_map, Option.map_some]
  rw [request_batch T points candidates (by omega)]
  rfl


private theorem memory_resources (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) :
    tokenBill (memory T points candidates invoice hz).events =
        (∑ j : Fin z, invoice j.succ : ℕ) ∧
      elapsed (memory T points candidates invoice hz).events = 1 := by
  obtain ⟨hb, ht⟩ := resources T points candidates invoice hz
  simp only [memory, initialMemory, Memory.record, tokenBill, elapsed,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, replyOf, add_zero, hb, ht]
  trivial

private theorem output_provenance (invoice : Fin (z + 1) → ℕ) (hz : 0 < z)
    (C : Finset (Fin (input T points candidates).startup.system.rows.length))
    (hc : decodeFamily (input T points candidates).startup.system.rows.length
      (RuntimeControl.result (finished T points candidates invoice hz)) = some C) :
    C ⊆ NativeBatch.nativeAvailable (n := z + 1)
      (input T points candidates).startup.system.rows.length
      (memory T points candidates invoice hz).events := by
  let state := finished T points candidates invoice hz
  have hx : Valid state.work.system := NativeResidualAttainment.valid T points candidates hz
  have hopps : state.work.opportunities = z + 1 := rfl
  have hhistory : state.work.history =
      (memory T points candidates invoice hz).events.map (fun e => e.reply.word) := rfl
  apply RuntimeProvenance.result_available state _ hx hopps hhistory _ C hc
  intro word hw
  change word ∈ [_] at hw
  obtain rfl := List.mem_singleton.mp hw
  exact (Packets.families_report _).trans (by simp only [replyOf, parseProposals_report])

/-- The actual all-specialist program has native selection-only admission, not
an assumed behavioral-policy representation or supplied success contract. -/
theorem native_selectionOnly (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (budget : ℕ) (hb : 0 < budget)
    (accept : Finset (Fin (input T points candidates).startup.system.rows.length) → Bool) :
    NativeUnboundedExecution.SelectionOnly (controller false).program
      (environment (config budget) (NativeResidualOracle.sample T points candidates P invoice))
      (NativeBatch.candidateParser (n := z + 1)
        (input T points candidates).startup.system.rows.length)
      (decodeFamily (input T points candidates).startup.system.rows.length) accept
      ⟨(controller false).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ := by
  intro fuel next hn C hc _
  have hh : NativeUnboundedExecution.halted next := by
    unfold NativeOpenSelection.result at hc
    split_ifs at hc with h
    exact Option.isNone_iff_eq_none.mp h
  have hs := (NativeUnboundedExecution.terminal_support _ _ _ _).mpr ⟨hh, fuel, hn⟩
  have hm : some (next.config.tapes.output, next.memory) ∈
      ((NativeUnboundedExecution.terminal (controller false).program
        (environment (config budget) (NativeResidualOracle.sample T points candidates P invoice))
        ⟨(controller false).program.initialConfig
          (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
          (Option.map fun next => (next.config.tapes.output, next.memory))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨some next, hs, rfl⟩
  rw [native_law T points candidates P invoice hz budget hb, PMF.mem_support_pure_iff] at hm
  obtain ⟨ho, hm⟩ := Prod.mk.inj (Option.some.inj hm)
  have hdecode : decodeFamily (input T points candidates).startup.system.rows.length
      (RuntimeControl.result (finished T points candidates invoice (by omega))) = some C := by
    have hhalt : next.config.tapes.state = none := hh
    simpa only [NativeOpenSelection.result, hhalt, Option.isNone_none, ite_true, ho] using hc
  rw [NativeBatch.candidateParser_proposals, hm]
  exact output_provenance T points candidates invoice (by omega) C hdecode

/-- The actual compiled all-specialist output is certified by the source deadline,
with probability one, on the same oracle used by all native competitors. -/
theorem native_certified (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (budget : ℕ) (hb : 0 < budget) :
    ((NativeUnboundedExecution.terminal (controller false).program
      (environment (config budget) (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(controller false).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
      (BatchOutput.certified (config budget) (input T points candidates).startup.system
        (NativeResidualAttainment.valid T points candidates (by omega)))) true = 1 := by
  classical
  let μ := NativeUnboundedExecution.terminal (controller false).program
    (environment (config budget) (NativeResidualOracle.sample T points candidates P invoice))
    (⟨(controller false).program.initialConfig
      (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ :
        World (controller false).tapes (controller false).Controls Unit
          (ServerState (z + 1) Unit) (GuardedStartup.encoding (input T points candidates)))
  have hgood : ∀ result ∈ μ.support, BatchOutput.certified (config budget)
      (input T points candidates).startup.system
      (NativeResidualAttainment.valid T points candidates (by omega)) result = true := by
    intro result hs
    have hm : result.map (fun next => (next.config.tapes.output, next.memory)) ∈
        (μ.map (Option.map fun next => (next.config.tapes.output, next.memory))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨result, hs, rfl⟩
    rw [native_law T points candidates P invoice hz budget hb, PMF.mem_support_pure_iff] at hm
    cases result with
    | none => cases hm
    | some next =>
      obtain ⟨ho, hm⟩ := Prod.mk.inj (Option.some.inj hm)
      have hh : next.config.tapes.state = none :=
        ((NativeUnboundedExecution.terminal_support _ _ _ _).mp hs).1
      have hinv := NativeBatch.terminal_invariant (config budget)
        (NativeResidualOracle.sample T points candidates P invoice) (controller false).program
        ⟨(controller false).program.initialConfig
          (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ next
        (NativeBatch.initial_invariant (config budget) ()) hs
      obtain ⟨C, hc, hcover, hcost⟩ := completed T points candidates invoice (by omega)
      have hdecode : NativeOpenSelection.result
          (decodeFamily (input T points candidates).startup.system.rows.length) next = some C := by
        simp only [NativeOpenSelection.result, hh, Option.isNone_none, ite_true, ho]
        exact hc
      have hI : instanceOf (input T points candidates).startup.system
          (NativeResidualAttainment.valid T points candidates (by omega)) =
          nativeInstance T points candidates (by omega) := rfl
      have hrho : (input T points candidates).startup.system.rho = 1 := rfl
      have ht : next.memory.privateState.elapsed ≤ (config (z := z) budget).deadline :=
        hinv.1.2.2.1
      simp only [BatchOutput.certified, Option.any_some, hdecode, BatchOutput.accept,
        hI, hrho, Rat.cast_one, one_mul, native_dual_objective]
      simp only [ht, decide_true, Bool.and_true]
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hcover, decide_eq_true hcost.le⟩
  have he : μ.map (BatchOutput.certified (config budget) (input T points candidates).startup.system
      (NativeResidualAttainment.valid T points candidates (by omega))) = PMF.pure true := by
    calc
      _ = μ.map (fun _ => true) := by
        apply PMF.bind_congr_on_support
        intro result hs
        simp only [Function.comp_def, hgood result hs]
      _ = PMF.pure true := PMF.map_const _ _
  simpa only [PMF.pure_apply, ite_true] using congrArg (fun law => law true) he

/-- Joint actual terminal invoice and concurrent duration; issuing z specialists
costs their sum, while concurrent source time is one, rather than z. -/
theorem native_resources (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (budget : ℕ) (hb : 0 < budget) :
    (NativeUnboundedExecution.terminal (controller false).program
      (environment (config budget) (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(controller false).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
        (Option.map fun next => (tokenBill next.memory.events, elapsed next.memory.events)) =
      PMF.pure (some (((∑ j : Fin z, invoice j.succ : ℕ) : ℝ≥0), (1 : ℝ≥0))) := by
  have h := congrArg (PMF.map (Option.map fun pair : Word ×
      Memory Unit (ServerState (z + 1) Unit) =>
        (tokenBill pair.2.events, elapsed pair.2.events)))
    (native_law T points candidates P invoice hz budget hb)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map, PMF.pure_map, Option.map_some,
    (memory_resources T points candidates invoice (by omega)).1,
    (memory_resources T points candidates invoice (by omega)).2] using h

/-- Exact accrued native expected bill, with almost-sure termination derived
from the concrete one-batch execution. No integrability or total-bill bound is assumed. -/
theorem native_expected_cost (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (budget : ℕ) (hb : 0 < budget)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    NativeBatch.Quantitative.expected (config budget)
      (NativeResidualOracle.sample T points candidates P invoice) (controller false).program
      NativeBatch.Trace.charge (budget + 1)
      ⟨(controller false).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ =
      ENNReal.ofReal (∑ j, P.specialistCost j) := by
  let program := (controller false).program
  let env := environment (config budget) (NativeResidualOracle.sample T points candidates P invoice)
  let world := (⟨program.initialConfig (GuardedStartup.encoding (input T points candidates)),
    initialMemory⟩ : World (controller false).tapes (controller false).Controls Unit
      (ServerState (z + 1) Unit) (GuardedStartup.encoding (input T points candidates)))
  let μ := NativeUnboundedExecution.terminal program env world
  have hlaw := native_resources T points candidates P invoice hz budget hb
  have hterm : μ none = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hn
    have hm : none ∈ (μ.map (Option.map fun next =>
        (tokenBill next.memory.events, elapsed next.memory.events))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
    rw [hlaw, PMF.mem_support_pure_iff] at hm
    cases hm
  have he := NativeBatch.Quantitative.expected_charge_eq_terminal (config budget)
    (NativeResidualOracle.sample T points candidates P invoice) program world
    (NativeBatch.initial_invariant (config budget) ()) rfl hterm
  change NativeBatch.Quantitative.expected (config budget) _ program NativeBatch.Trace.charge
    ((config (z := z) budget).turns + 1) world = _
  rw [he]
  have hm := PMF.tsum_map_mul μ (Option.map fun next =>
    (tokenBill next.memory.events, elapsed next.memory.events))
    (fun result => result.elim 0 (fun pair => (pair.1 : ℝ≥0∞)))
  simp only [Option.elim_map, Function.comp_def] at hm
  change (∑' result, μ result * result.elim 0
    (fun next => (tokenBill next.memory.events : ℝ≥0∞))) = _
  rw [← hm, hlaw]
  have hspec (j : Fin z) : (invoice j.succ : ℝ) = P.specialistCost j := by
    simpa using hprice j.succ
  have hsum : (∑ j : Fin z, invoice j.succ : ℕ) = (∑ j, P.specialistCost j : ℝ) := by
    simp [Nat.cast_sum, hspec]
  simpa [PMF.pure_apply, ENNReal.ofReal_sum_of_nonneg, ENNReal.ofReal_natCast] using
    congrArg ENNReal.ofReal hsum

/-- The all-specialist actual cost is attained in the same Theorem 5 native
competitor class for either a one-turn or a two-turn source budget. -/
theorem native_cost_mem (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (budget : ℕ) (hb : 0 < budget)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    ENNReal.ofReal (∑ j, P.specialistCost j) ∈
      BatchOptimum.costs (config budget) (NativeResidualOracle.sample T points candidates P invoice)
        (input T points candidates) ()
        (NativeResidualAttainment.valid T points candidates (by omega)) 1 := by
  have hm : NativeBatch.Quantitative.expected (config budget)
      (NativeResidualOracle.sample T points candidates P invoice) (controller false).program
      NativeBatch.Trace.charge (budget + 1)
      ⟨(controller false).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ ∈
      BatchOptimum.costs (config budget) (NativeResidualOracle.sample T points candidates P invoice)
        (input T points candidates) ()
        (NativeResidualAttainment.valid T points candidates (by omega)) 1 := by
    refine ⟨(controller false).tapes, (controller false).Controls, (controller false).finite,
      (controller false).program, native_selectionOnly T points candidates P invoice hz budget hb _,
      (native_certified T points candidates P invoice hz budget hb).ge, rfl⟩
  rwa [native_expected_cost T points candidates P invoice hz budget hb hprice] at hm

/-- Matching all-specialist upper bound on the original native optimum. -/
theorem native_upper (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (budget : ℕ) (hb : 0 < budget)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    BatchOptimum.optimum (config budget) (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) ()
        (NativeResidualAttainment.valid T points candidates (by omega)) 1 ≤
      ENNReal.ofReal (∑ j, P.specialistCost j) :=
  sInf_le (native_cost_mem T points candidates P invoice hz budget hb hprice)

end Cslib.Probability.StochasticOracle.NativeResidualAll
