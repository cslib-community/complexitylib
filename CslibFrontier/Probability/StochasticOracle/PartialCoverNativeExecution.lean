/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCoverGreedyNative
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchAdmission
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Tactic

/-!
# Native execution of the runtime greedy batch

[Wang2027], Theorem 4, PDF pp. 10–11. A single native program computes the
threshold and complete greedy plan from original input, forms one concurrent
packet before seeing any reply, reads the unbounded full response and performs
rational local certification/retention. The opportunity count is computed from
the runtime plan, not fixed in the program or passed as an execution witness.

Addresses in each call word are computed original-table indices, followed by the
original rational WSC input. The concurrent transport assigns one fresh opportunity to
each occurrence, so repeated calls to an underlying oracle remain distinct.
The theorem preserves the actual joint hidden state, raw report, bill and oracle
duration. Local instructions are excluded from the source deadline (PDF p. 5).
This codec does not claim universality for arbitrary external PTM/query encodings.
General source conditional-success transfer from per-response reached-history
envelopes is still separate from this execution law and its concrete correlated client.

## Main definitions

* `Input`, `encoding`: original planning and rational local-certification data.
* `requests`, `initial`: the computed preformed packet and fresh runtime State.
* `controller`: one implementation shared by all execution conclusions.

## Main results

* `requests_encode`: the computed packet is the exact source batch codec.
* `admit_requests`: initial source admission without an admission premise.
* `source_law`: actual native execution of the admitted batch on one correlated oracle.
* `completed_decodes`, `completed_certificate`: actual output readback and local certificate.
* `native_resources`: derived terminal bill/deadline/source-feasibility bounds for the same code.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.NativeExecution
open Turing Turing.MultiTapeTM NativeOpenExecution ConcurrentBatch NativeRetention

/-- Original runtime inputs; no precomputed plan, contexts or histories. -/
structure Input where
  /-- Eligibility/cost metadata and rational probability/budget. -/
  planner : GreedyNative.Input
  /-- Original rational WSC rows, weights and dual certificate. -/
  system : NativeRetention.Input
  /-- Both parts refer to the same ground prefix; no extra runtime proof bits. -/
  ground_eq : planner.val.ground = system.dual.length

/-- Framed planning input, then rational WSC data. The ground-agreement proof is erased. -/
@[expose] def encoding : Input ↪ List Bool :=
  ⟨fun x => encPair GreedyNative.encoding encInput (x.planner, x.system), by
    intro x y h
    have he := (encPair GreedyNative.encoding encInput).injective h
    cases x; cases y; cases he; rfl⟩

private theorem input_fields : ComputableInPolyTime
    (fun x : Input => (x.planner, x.system)) encoding
    (encPair GreedyNative.encoding encInput) := .of_eq fun _ => rfl

/-- Native readback of original planning data; proof erasure changes no bytes. -/
theorem computable_planner : ComputableInPolyTime Input.planner encoding
    GreedyNative.encoding := input_fields.fst'

/-- Native readback of the original WSC system sharing the planning ground. -/
theorem computable_system : ComputableInPolyTime Input.system encoding encInput :=
  input_fields.snd' 

/-- One addressed source query contains a binary oracle index and original WSC data.
The index is framed and the WSC word occupies the remaining suffix. -/
@[expose] def callWord (x : Input) (j : ℕ) : Word :=
  encPair encNat encBits (j, encInput x.system)

/-- Actual variable-size batch bytes, with every call formed before the response. -/
@[expose] def requests (x : Input) : Word :=
  (GreedyNative.labels x.planner).flatMap fun j =>
    true :: Kolmogorov.selfDelimitingCode (callWord x j)

/-- Distinct opportunities for all occurrences in the actual runtime plan. -/
@[expose] def slots (x : Input) : Fin (GreedyNative.labels x.planner).length → Option Word :=
  fun i => some (callWord x ((GreedyNative.labels x.planner).get i))

private theorem encode_list (xs : List ℕ) (query : ℕ → Word) :
    encodeSlots xs.length (fun i => some (query (xs.get i))) =
      xs.flatMap (fun j => true :: Kolmogorov.selfDelimitingCode (query j)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [encodeSlots, List.length_cons, List.get_eq_getElem,
      Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
      List.flatMap_cons, List.cons_append] using
      (congrArg (fun tail => true :: (Kolmogorov.selfDelimitingCode (query a) ++ tail)) ih)

/-- Exact source batch framing, derived from the actual dynamically computed plan. -/
theorem requests_encode (x : Input) : requests x = encodeSlots _ (slots x) :=
  (encode_list _ (callWord x)).symm

/-- Every selected label comes from the original table, including repeated calls. -/
theorem source_label (x : Input) (i : Fin (GreedyNative.labels x.planner).length) :
    (GreedyNative.labels x.planner).get i < x.planner.val.rows.length :=
  GreedyNative.labels_lt _ (List.get_mem _ _)

/-- The entire original system is retained separately from the wire request.
A single turn processes all completed proposals, including after cancellations. -/
@[expose] def initial (x : Input) : RuntimeControl.State :=
  ⟨⟨x.system, (GreedyNative.labels x.planner).length, []⟩, [], requests x,
    1, (GreedyNative.labels x.planner).length, 1⟩

/-- The selected packet is read from the reserved runtime field. It is not rebuilt
using a response-dependent or externally supplied continuation. -/
@[expose] def query (state : RuntimeControl.State) : Word := state.privateWord

private theorem computable_query : ComputableInPolyTime query
    (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBits :=
  RuntimeControl.computable_privateWord.comp RuntimeControl.computable_unframe

/-- Intermediate input to the native packet/State assembler, including the whole
runtime plan; these bytes are computed by the planner, not original input fields. -/
private abbrev preparedEncoding := encPair encoding (encList encNat)

private def prepare (p : Input × List ℕ) : RuntimeControl.State :=
  ⟨⟨p.1.system, p.2.length, []⟩, [],
    p.2.flatMap (fun j => true :: Kolmogorov.selfDelimitingCode (callWord p.1 j)),
    1, p.2.length, 1⟩

private theorem prepare_computable : ComputableInPolyTime prepare preparedEncoding
    RuntimeControl.encoding := by
  have hx := ComputableInPolyTime.fst encoding (encList encNat)
  have hl := ComputableInPolyTime.snd encoding (encList encNat)
  have hs := computable_system.comp hx
  have hn := (ComputableInPolyTime.length_list encNat).comp hl
  have hw : ComputableInPolyTime (fun p : Input × List ℕ => encInput p.1.system)
      preparedEncoding encBits :=
    (show ComputableInPolyTime (fun s : NativeRetention.Input => encInput s)
      encInput encBits from .of_eq fun _ => rfl).comp hs
  have hreq : ComputableInPolyTime (fun p : Input × List ℕ => p.2.flatMap
      (fun j => true :: Kolmogorov.selfDelimitingCode (callWord p.1 j)))
      preparedEncoding encBits := by
    have hc := (ComputableInPolyTime.snd preparedEncoding encNat).prod
      (hw.comp (ComputableInPolyTime.fst preparedEncoding encNat))
    have he : ComputableInPolyTime (fun q : ℕ × Word => encPair encNat encBits q)
        (encPair encNat encBits) encBits := .of_eq fun _ => rfl
    exact (ComputableInPolyTime.flatMapToBitsWithInput hl
      (ComputableInPolyTime.bitsCons (.const true)
        (ComputableInPolyTime.selfDelimitingCode.comp (he.comp hc)))).of_enc_eq fun _ => rfl
  have hwork : ComputableInPolyTime
      (fun p : Input × List ℕ => (⟨p.1.system, p.2.length, []⟩ : Packets.Work))
      preparedEncoding Packets.encWork :=
    (hs.prod (hn.prod (ComputableInPolyTime.const ([] : List Word)))).of_enc_eq fun _ => rfl
  exact (hwork.prod ((ComputableInPolyTime.const ([] : List Word)).prod
    (hreq.prod ((ComputableInPolyTime.const 1).prod
      (hn.prod (ComputableInPolyTime.const 1)))))).of_enc_eq fun _ => rfl

/-- The runtime plan and initializer are computed by native code. Their termination
is derived from the planner and assembler certificates, not an input promise. -/
theorem initial_computable : ∃ T S : Input → ℕ,
    ComputableInTimeAndSpace initial encoding RuntimeControl.encoding T S := by
  obtain ⟨T, S, _, _, hl⟩ := GreedyNative.uniform_plan
  have hp := computable_planner
  obtain ⟨tp, sp, _, _, hpo⟩ := hp.exists_computableInO
  have hlo : ComputableInO GreedyNative.labels GreedyNative.encoding (encList encNat) T
      (fun x => S x + T x) :=
    .of_bounds hl 1 (fun _ => by omega) (fun _ => by omega) fun x => by
      have := hl.length_le x
      omega
  have hlabels := hlo.comp hpo
  have hid : ComputableInO (fun x : Input => x) encoding encoding
      (fun x => (encoding x).length) (fun x => (encoding x).length) := .of_eq fun _ => rfl
  obtain ⟨_, _, _, _, ha⟩ := prepare_computable.exists_computableInO
  have ho : ComputableInO initial encoding RuntimeControl.encoding _ _ :=
    (ha.comp (hid.prod hlabels)).of_enc_eq fun _ => rfl
  obtain ⟨c, hc, _⟩ := ho
  exact ⟨_, _, hc⟩

/-- One fixed finite-control native implementation, independent of input size,
response length, oracle hidden memory or the subsequent quantitative hypotheses. -/
structure Controller where
  /-- Number of native work tapes. -/
  tapes : ℕ
  /-- Native control state type. -/
  Control : Type
  /-- Finiteness of native control. -/
  finite : Finite Control
  /-- Actual source-query program. -/
  program : MultiTapePTM tapes Bool Control Unit
  /-- Reserved runtime State tape. -/
  context : Fin tapes
  /-- Derived joint law from original input and blank tapes. -/
  law : ∀ (P : Type) (env : Environment Unit P) (x : Input) (memory : Memory Unit P),
    (NativeUnboundedExecution.terminal program env
      ⟨program.initialConfig (encoding x), memory⟩).map
      (Option.map (NativeReplyContext.observe context)) =
      (Feedback.run env 1 (initial x) (fun _ => ⟨[], [], 0⟩) memory query).map fun result =>
        some (⟨tapeOfList (RuntimeControl.packet result.state),
          RuntimeControl.result result.state, result.memory⟩ : NativeReplyContext.Observation P)

private theorem controller_nonempty : Nonempty Controller := by
  obtain ⟨T, S, hi⟩ := initial_computable
  obtain ⟨tapes, Control, hf, program, context, hl⟩ :=
    Feedback.exists_native_controller_from_state encoding initial T S hi query computable_query
  exact ⟨⟨tapes, Control, hf, program, context, hl⟩⟩

/-- The same implementation is used in every execution and source-admission theorem. -/
def controller : Controller := Classical.choice controller_nonempty

/-- Actual unbounded native execution, including decoded final tape output and
the unchanged correlated oracle's complete resource-bearing memory. -/
theorem controller_law (P : Type) (env : Environment Unit P) (x : Input)
    (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (encoding x), memory⟩).map
      (Option.map (NativeReplyContext.observe controller.context)) =
      (Feedback.run env 1 (initial x) (fun _ => ⟨[], [], 0⟩) memory query).map fun result =>
        some (⟨tapeOfList (RuntimeControl.packet result.state),
          RuntimeControl.result result.state, result.memory⟩ : NativeReplyContext.Observation P) :=
  controller.law P env x memory

/-- All runtime plan occurrences are preformed calls, with distinct opportunity labels. -/
theorem active_slots (x : Input) : active (slots x) = Finset.univ := by
  simp [active, slots]

/-- A live initial controller has a genuinely nonempty runtime batch. -/
theorem live_nonempty (x : Input) (h : RuntimeControl.stopped (initial x) = false) :
    0 < (GreedyNative.labels x.planner).length := by
  by_contra hn
  have hz : (GreedyNative.labels x.planner).length = 0 := by omega
  simp [RuntimeControl.stopped, initial, hz] at h

/-- The source batch is constructed from the computed runtime plan. -/
def batch (x : Input) (hn : 0 < (GreedyNative.labels x.planner).length) :
    Batch (GreedyNative.labels x.planner).length :=
  ⟨slots x, by rw [active_slots]; exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩⟩

/-- Concrete bytes pass the source's initial nonempty/turn/deadline/nonreuse guard.
No admission/representation promise is an input to this theorem. -/
theorem admit_requests (x : Input) (hn : 0 < (GreedyNative.labels x.planner).length)
    (limits : Limits (GreedyNative.labels x.planner).length) {P : Type} (seed : P)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns) :
    admit limits (ConcurrentBatch.initial seed) (requests x) = some (batch x hn) := by
  have he : requests x = encodeBatch (batch x hn) := requests_encode x
  rw [admit, he, decodeBatch_encode]
  simp [ConcurrentBatch.initial, hd, ht]

/-- Readback after the actual full reply, with local tests and stop/output recomputed. -/
@[expose] def responseInput (x : Input) (reply : Word) : NativeRetention.Input :=
  Packets.assemble ⟨x.system, (GreedyNative.labels x.planner).length, [reply]⟩

/-- Actual tape/context/resource observation after the one issued native batch. -/
@[expose] def finished {P : Type} (x : Input) (memory : Memory Unit P)
    (reply : Reply) (next : P) : NativeReplyContext.Observation P :=
  let state := RuntimeControl.afterReply (initial x) reply.word
  ⟨tapeOfList (RuntimeControl.packet state), RuntimeControl.result state,
    memory.record ((), requests x) reply next⟩

/-- The named native code issues exactly one precomputed packet on a live input,
reads its complete unbounded reply, then emits its computed final mask or failure.
All raw events, hidden state, invoices and duration are from that same query. -/
theorem live_law {P : Type} (env : Environment Unit P) (x : Input)
    (memory : Memory Unit P) (hs : RuntimeControl.stopped (initial x) = false) :
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (encoding x), memory⟩).map
      (Option.map (NativeReplyContext.observe controller.context)) =
      (env ((), requests x) memory).map
        (fun (reply, next) => some (finished x memory reply next)) := by
  rw [controller_law]
  simp only [Feedback.run, hs, Bool.false_eq_true, ite_false,
    PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map]
  rfl

/-- Computed initial completion or an empty plan stops before any query and
preserves the entire existing oracle state and resource ledger. -/
theorem stopped_law {P : Type} (env : Environment Unit P) (x : Input)
    (memory : Memory Unit P) (hs : RuntimeControl.stopped (initial x) = true) :
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (encoding x), memory⟩).map
      (Option.map (NativeReplyContext.observe controller.context)) =
      PMF.pure (some (⟨tapeOfList (RuntimeControl.packet (initial x)),
        RuntimeControl.result (initial x), memory⟩ : NativeReplyContext.Observation P)) := by
  rw [controller_law]
  simp [Feedback.run, hs]

/-- End-to-end native source law from original input, with the whole correlated
trajectory sample preserved. There is no finite alphabet replacement or separately
compiled per-reply phase. Source cutoffs/cancellation feed the actual receipt. -/
theorem source_law {P : Type} (x : Input)
    (limits : Limits (GreedyNative.labels x.planner).length)
    (sample : Sampler (GreedyNative.labels x.planner).length P) (seed : P)
    (hs : RuntimeControl.stopped (initial x) = false)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns) :
    let memory : Memory Unit (ServerState (GreedyNative.labels x.planner).length P) :=
      ⟨ConcurrentBatch.initial seed, []⟩
    (NativeUnboundedExecution.terminal controller.program (environment limits sample)
      ⟨controller.program.initialConfig (encoding x), memory⟩).map
      (Option.map (NativeReplyContext.observe controller.context)) =
      (sample (ConcurrentBatch.initial seed) (batch x (live_nonempty x hs))).map
        fun (paths, next) =>
          let receipt := observe limits limits.deadline (batch x (live_nonempty x hs)) paths
          some (finished x memory (replyOf receipt)
            (commit (ConcurrentBatch.initial seed) receipt next)) := by
  dsimp only
  rw [live_law _ _ _ hs]
  have ha := admit_requests x (live_nonempty x hs) limits seed hd ht
  have he := serve_accepted limits sample (requests x) (ConcurrentBatch.initial seed)
    (batch x (live_nonempty x hs)) ha
  have he' : environment limits sample ((), requests x)
      (⟨ConcurrentBatch.initial seed, []⟩ : Memory Unit _) =
      (sample (ConcurrentBatch.initial seed) (batch x (live_nonempty x hs))).map
        (fun (paths, next) =>
          let receipt := observe limits limits.deadline (batch x (live_nonempty x hs)) paths
          (replyOf receipt, commit (ConcurrentBatch.initial seed) receipt next)) := by
    simpa only [environment, ConcurrentBatch.initial, tsub_zero] using he
  rw [he', PMF.map_comp]
  rfl

/-- The computed final output is decoded as the retained original family. A
completion flag is the executed local test, not an assumed success probability. -/
theorem completed_decodes (x : Input) (reply : Reply)
    (hc : complete (responseInput x reply.word) = true) {P : Type}
    (memory : Memory Unit P) (next : P) :
    decodeFamily x.system.rows.length (finished x memory reply next).output =
      some (outputFamily (responseInput x reply.word)) := by
  have hr : (finished x memory reply next).output = output (responseInput x reply.word) := by
    change (if complete (responseInput x reply.word) then output (responseInput x reply.word)
      else []) = output (responseInput x reply.word)
    rw [hc, ite_eq_left rfl]
  rw [hr]
  exact decode_output _

/-- Source certification and provenance for the actual raw report's retained family.
Only original WSC/dual validity and a positive computed completion flag are required. -/
theorem completed_certificate (x : Input) (reply : Word) (hx : Valid x.system)
    (hc : complete (responseInput x reply) = true) :
    let C := (outputFamily (responseInput x reply)).image Fin.val
    (instanceOf x.system hx).covered C = (instanceOf x.system hx).ground ∧
      (instanceOf x.system hx).cost C ≤ (x.system.rho : ℝ) *
        ∑ e ∈ (instanceOf x.system hx).ground, (instanceOf x.system hx).dual e := by
  have hv : Valid (responseInput x reply) :=
    ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  exact completed_output (responseInput x reply) hv hc

/-- Local retention cannot invent a candidate: every retained original label is
present in an actual completed (not canceled) call of the canonical raw report. -/
theorem report_provenance (system : NativeRetention.Input) (hx : Valid system) (n : ℕ)
    (report : Report n) :
    outputFamily (Packets.assemble ⟨system, n, [encodeReport report]⟩) ⊆
      (proposals system.rows.length report).foldr (· ∪ ·) ∅ := by
  let state : Selector.State := ⟨[encodeReport report], false, [], []⟩
  have hp : [encodeReport report].reverse.flatMap (Packets.families n system.rows.length) =
      ([encodeReport report].reverse.flatMap (parseProposals n system.rows.length)).map
        sourceIndices := by
    simp only [List.reverse_singleton, List.flatMap_singleton, Packets.families_report,
      parseProposals_report]
  dsimp only [Packets.assemble]
  rw [hp]
  have h := Selector.provenance n system hx state
  dsimp only [Selector.data] at h
  -- Only proposals changed; unfold the dependent Finset instance through the unchanged row field.
  set_option backward.isDefEq.respectTransparency false in
    simpa only [state, Selector.available, parseProposals_report, Finset.union_empty] using h


/-- The actual parallel receipt is bounded by the sum of original per-call caps
and by the oracle deadline. Per-call bounds include query/hidden/cancellation
charges; neither a bounded total bill nor integrability is assumed. -/
theorem receipt_resources (x : Input) (hn : 0 < (GreedyNative.labels x.planner).length)
    (limits : Limits (GreedyNative.labels x.planner).length)
    (paths : Fin (GreedyNative.labels x.planner).length → CallTrace)
    (hcap : ∀ i, ((paths i).accrued (limits.cutoff i) : ℝ) ≤
      (GreedyNative.oracleAt x.planner.val ((GreedyNative.labels x.planner).get i)).cost) :
    let receipt := observe limits limits.deadline (batch x hn) paths
    (receipt.tokens : ℝ) ≤ (Cslib.Algorithms.Lean.Multicover.bill
      ((GreedyNative.labels x.planner).map (GreedyNative.oracleAt x.planner.val)) : ℝ) ∧
      receipt.duration ≤ limits.deadline := by
  dsimp only
  refine ⟨?_, observe_duration_le _ _ _ _⟩
  rw [observe_tokens]
  have he : active (batch x hn).slots = Finset.univ := active_slots x
  rw [he, Nat.cast_sum]
  calc
    _ ≤ ∑ i, ((GreedyNative.oracleAt x.planner.val
        ((GreedyNative.labels x.planner).get i)).cost : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ((paths i).accrued (limits.cutoff i) : ℝ) := by
          exact_mod_cast (paths i).monotone
            (((paths i).stop_le _).trans (min_le_left (limits.cutoff i) limits.deadline))
        _ ≤ _ := hcap i
    _ = _ := by
      rw [← List.sum_ofFn]
      have h := List.ofFn_getElem_eq_map (GreedyNative.labels x.planner)
        (fun j => ((GreedyNative.oracleAt x.planner.val j).cost : ℝ))
      simpa only [List.get_eq_getElem, Cslib.Algorithms.Lean.Multicover.bill,
        Rat.cast_list_sum, List.map_map, Function.comp_def] using congrArg List.sum h


/-- The actual named native program terminates after one source-admitted batch,
with its complete terminal bill and oracle duration bounded from per-call accrued
caps on possible joint trajectories. No bounded-total-bill, termination, native
representation or independence premise is supplied. -/
theorem native_resources {P : Type} (x : Input)
    (limits : Limits (GreedyNative.labels x.planner).length)
    (sample : Sampler (GreedyNative.labels x.planner).length P) (seed : P)
    (hs : RuntimeControl.stopped (initial x) = false)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns)
    (hcap : ∀ pair ∈ (sample (ConcurrentBatch.initial seed)
      (batch x (live_nonempty x hs))).support, ∀ i,
      ((pair.1 i).accrued (limits.cutoff i) : ℝ) ≤
        (GreedyNative.oracleAt x.planner.val ((GreedyNative.labels x.planner).get i)).cost)
    (outcome : Option (NativeReplyContext.Observation
      (ServerState (GreedyNative.labels x.planner).length P)))
    (houtcome : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample) ⟨controller.program.initialConfig (encoding x),
        ⟨ConcurrentBatch.initial seed, []⟩⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧
      (tokenBill final.memory.events : ℝ) ≤ (Cslib.Algorithms.Lean.Multicover.bill
        ((GreedyNative.labels x.planner).map (GreedyNative.oracleAt x.planner.val)) : ℝ) ∧
      elapsed final.memory.events ≤ limits.deadline ∧
      WellFormed limits final.memory.privateState ∧ final.memory.events.length = 1 := by
  rw [source_law x limits sample seed hs hd ht] at houtcome
  obtain ⟨⟨paths, next⟩, hp, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp houtcome
  have hres := receipt_resources x (live_nonempty x hs) limits paths (hcap _ hp)
  have had := admit_requests x (live_nonempty x hs) limits seed hd ht
  have hwf := commit_wellFormed limits (ConcurrentBatch.initial seed)
    (initial_wellFormed limits seed) (requests x) (batch x (live_nonempty x hs)) had paths next
  refine ⟨_, rfl, ?_, ?_, ?_, rfl⟩
  · simpa only [finished, Memory.record, tokenBill, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, replyOf, NNReal.coe_natCast] using hres.1
  · simpa only [finished, Memory.record, elapsed, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, replyOf] using hres.2
  · simpa only [finished, Memory.record, ConcurrentBatch.initial, tsub_zero] using hwf

end Cslib.Probability.StochasticOracle.PartialCover.NativeExecution
