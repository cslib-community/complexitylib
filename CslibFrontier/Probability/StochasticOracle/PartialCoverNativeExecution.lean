/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.SourceQuery
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.SourceEncoding
public import CslibFrontier.Probability.StochasticOracle.PartialCoverGreedyNative
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchAdmission
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.TokenBounds
import Mathlib.Tactic

/-!
# Native execution of computed and supplied source batches

[Wang2027], Theorem 4, PDF pp. 10–11. A single native program computes the
threshold and complete greedy plan, or reads supplied original-oracle occurrences
from original input, forms one concurrent
packet before seeing any reply, reads the unbounded full response and performs
rational local certification/retention. The opportunity count is computed from
the selected runtime batch, not fixed in the program. Supplied occurrences encode
an arbitrary call-count vector; greedy mode computes them instead.

Addresses in each call word are computed original-table indices, followed by
the corresponding original opaque source query. The concurrent transport assigns
one fresh opportunity to
each occurrence, so repeated calls to an underlying oracle remain distinct.
The theorem preserves the actual joint hidden state, raw report, bill and oracle
duration. Local instructions are excluded from the source deadline (PDF p. 5).
Opaque source-query strings are runtime input, not a fixed WSC query encoding.
Original binary incidence input is converted by native startup before local tests.
The conditional-success transfer and comparison with the source risk optimum
are in the importing native-risk and native-optimum modules. No universal claim
is made about arbitrary third-party serializers or noncomputable real input.

## Main definitions

* `Input`, `encoding`: binary incidence, opaque source queries and selection mode.
* `labels`: selected occurrences, supplied or computed before any response.
* `requests`, `initial`: the computed preformed packet and fresh runtime State.
* `controller`: one implementation shared by all execution conclusions.

## Main results

* `requests_encode`: the computed packet is the exact source batch codec.
* `admit_requests`: initial source admission without an admission premise.
* `source_law`: actual native execution of the admitted batch on one correlated oracle.
* `external_source_law`: original opaque queries reach the original joint source oracle.
* `completed_decodes`, `completed_certificate`: actual output readback and local certificate.
* `native_resources`: derived terminal bill/deadline/source-feasibility bounds for the same code.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.NativeExecution
open Turing Turing.MultiTapeTM NativeOpenExecution ConcurrentBatch NativeRetention

/-- Original runtime input, with either greedy selection or supplied call occurrences.
No contexts, histories or native execution witnesses are input fields. -/
structure Input where
  /-- Eligibility/cost metadata and rational probability/budget. -/
  planner : GreedyNative.Input
  /-- Original binary incidence matrix, weights and dual certificate. -/
  source : SourceEncoding.Input
  /-- Actual opaque source-query strings, indexed by original oracle configuration. -/
  queries : List Word
  /-- A supplied arbitrary source batch, or `none` to compute the greedy batch. -/
  calls : Option (List ℕ)
  /-- Both parts refer to the same ground prefix; no extra runtime proof bits. -/
  ground_eq : planner.val.ground = source.dual.length
  /-- Supplied batch entries name original oracle configurations. -/
  calls_valid : ∀ ls, calls = some ls → ∀ j ∈ ls, j < planner.val.rows.length

/-- The internally converted WSC system, computed from original incidence bits. -/
abbrev Input.system (x : Input) : NativeRetention.Input := SourceEncoding.toNative x.source

/-- Framed planning input, then WSC data and framed opaque source queries.
Ground/address well-formedness proofs are erased. -/
@[expose] def encoding : Input ↪ List Bool :=
  ⟨fun x => encPair GreedyNative.encoding (encPair SourceEncoding.encoding
        (encPair (encList encBits) (encOption (encList encNat))))
      (x.planner, x.source, x.queries, x.calls), by
    intro x y h
    have he := (encPair GreedyNative.encoding
      (encPair SourceEncoding.encoding
        (encPair (encList encBits) (encOption (encList encNat))))).injective h
    cases x; cases y; cases he; rfl⟩

private theorem input_fields : ComputableInPolyTime
    (fun x : Input => (x.planner, x.source, x.queries, x.calls)) encoding
    (encPair GreedyNative.encoding (encPair SourceEncoding.encoding
        (encPair (encList encBits) (encOption (encList encNat))))) :=
  .of_eq fun _ => rfl

/-- Native readback of original planning data; proof erasure changes no bytes. -/
theorem computable_planner : ComputableInPolyTime Input.planner encoding
    GreedyNative.encoding := input_fields.fst'

/-- Native readback of the original WSC system sharing the planning ground. -/
theorem computable_system : ComputableInPolyTime Input.system encoding encInput :=
  SourceEncoding.computable_toNative.comp input_fields.snd'.fst'

/-- Native readback of the original opaque source-query table. -/
theorem computable_queries : ComputableInPolyTime Input.queries encoding (encList encBits) :=
  input_fields.snd'.snd'.fst'

/-- Native readback of the optional arbitrary original-oracle batch. -/
theorem computable_calls : ComputableInPolyTime Input.calls encoding
    (encOption (encList encNat)) := input_fields.snd'.snd'.snd'

/-- Runtime-selected original oracle occurrences; no response is inspected. -/
@[expose] def labels (x : Input) : List ℕ := x.calls.getD (GreedyNative.labels x.planner)

/-- Greedy mode selects exactly the computed native greedy plan. -/
theorem labels_greedy (x : Input) (h : x.calls = none) :
    labels x = GreedyNative.labels x.planner := by simp [labels, h]

/-- One addressed source query contains a binary oracle index and its actual opaque
query string. The original WSC representation stays local to certification. -/
@[expose] def callWord (x : Input) (j : ℕ) : Word :=
  encPair encNat encBits (j, x.queries.getD j [])

/-- Actual variable-size batch bytes, with every call formed before the response. -/
@[expose] def requests (x : Input) : Word :=
  (labels x).flatMap fun j =>
    true :: Kolmogorov.selfDelimitingCode (callWord x j)

/-- Distinct opportunities for all occurrences in the actual runtime plan. -/
@[expose] def slots (x : Input) : Fin (labels x).length → Option Word :=
  fun i => some (callWord x ((labels x).get i))

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
theorem source_labels (x : Input) (j : ℕ) (hj : j ∈ labels x) :
    j < x.planner.val.rows.length := by
  cases hc : x.calls with
  | none =>
    rw [labels_greedy x hc] at hj
    exact GreedyNative.labels_lt _ hj
  | some ls =>
    exact x.calls_valid ls hc j (by simpa only [labels, hc, Option.getD_some] using hj)

/-- Each issued occurrence addresses an original oracle configuration. -/
theorem source_label (x : Input) (i : Fin (labels x).length) :
    (labels x).get i < x.planner.val.rows.length := source_labels x _ (List.get_mem _ _)

/-- The entire original system is retained separately from the wire request.
A single turn processes all completed proposals, including after cancellations. -/
@[expose] def initial (x : Input) : RuntimeControl.State :=
  ⟨⟨x.system, (labels x).length, []⟩, [], requests x,
    1, (labels x).length, 1⟩

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
  ⟨⟨p.1.system, (p.1.calls.getD p.2).length, []⟩, [],
    (p.1.calls.getD p.2).flatMap (fun j => true :: Kolmogorov.selfDelimitingCode (callWord p.1 j)),
    1, (p.1.calls.getD p.2).length, 1⟩

private theorem prepare_computable : ComputableInPolyTime prepare preparedEncoding
    RuntimeControl.encoding := by
  have hx := ComputableInPolyTime.fst encoding (encList encNat)
  have hdefault := ComputableInPolyTime.snd encoding (encList encNat)
  have hl := (ComputableInPolyTime.optionGetD (encList encNat)).comp
    ((computable_calls.comp hx).prod hdefault)
  have hs := computable_system.comp hx
  have hn := (ComputableInPolyTime.length_list encNat).comp hl
  have hqueries := computable_queries.comp hx
  have hreq : ComputableInPolyTime (fun p : Input × List ℕ => (p.1.calls.getD p.2).flatMap
      (fun j => true :: Kolmogorov.selfDelimitingCode (callWord p.1 j)))
      preparedEncoding encBits := by
    have hindex := ComputableInPolyTime.snd preparedEncoding encNat
    have htable := hqueries.comp (ComputableInPolyTime.fst preparedEncoding encNat)
    have hword := ComputableInPolyTime.listGetD_binary (encA := encBits) ([] : Word) htable hindex
    have hc := hindex.prod hword
    have he : ComputableInPolyTime (fun q : ℕ × Word => encPair encNat encBits q)
        (encPair encNat encBits) encBits := .of_eq fun _ => rfl
    exact (ComputableInPolyTime.flatMapToBitsWithInput hl
      (ComputableInPolyTime.bitsCons (.const true)
        (ComputableInPolyTime.selfDelimitingCode.comp (he.comp hc)))).of_enc_eq fun _ => rfl
  have hwork : ComputableInPolyTime
      (fun p : Input × List ℕ => (⟨p.1.system, (p.1.calls.getD p.2).length, []⟩ : Packets.Work))
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
    0 < (labels x).length := by
  by_contra hn
  have hz : (labels x).length = 0 := by omega
  simp [RuntimeControl.stopped, initial, hz] at h

/-- Any nonempty supplied or computed batch starts on the nonempty source ground.
The guard is derived from original input, not an assumed execution law. -/
theorem startup_live_of_nonempty (x : Input) (hn : 0 < (labels x).length) :
    RuntimeControl.stopped (initial x) = false := by
  have hg : x.system.dual.length ≠ 0 := by
    change x.source.dual.length ≠ 0
    rw [← x.ground_eq]
    exact Nat.ne_of_gt x.planner.property.ground_pos
  simpa [RuntimeControl.stopped, initial, Nat.ne_of_gt hn, Packets.decision,
    Packets.assemble, complete, covered, ground, retain] using
      (show ∃ i, i < x.system.dual.length from ⟨0, Nat.pos_of_ne_zero hg⟩)

/-- The source batch is constructed from the computed runtime plan. -/
@[expose] def batch (x : Input) (hn : 0 < (labels x).length) :
    Batch (labels x).length :=
  ⟨slots x, by rw [active_slots]; exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩⟩

/-- Concrete bytes pass the source's initial nonempty/turn/deadline/nonreuse guard.
No admission/representation promise is an input to this theorem. -/
theorem admit_requests (x : Input) (hn : 0 < (labels x).length)
    (limits : Limits (labels x).length) {P : Type} (seed : P)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns) :
    admit limits (ConcurrentBatch.initial seed) (requests x) = some (batch x hn) := by
  have he : requests x = encodeBatch (batch x hn) := requests_encode x
  rw [admit, he, decodeBatch_encode]
  simp [ConcurrentBatch.initial, hd, ht]

/-- Concrete query adaptation sends every original configuration exactly its
opaque query payload. No equality of source and transport laws is assumed. -/
theorem source_sample {P : Type} (x : Input) (hn : 0 < (labels x).length)
    (source : SourceQuery.SourceSampler P) (state : ServerState (labels x).length P) :
    SourceQuery.adapt source (labels x).length state (batch x hn) =
      source (labels x).length state (fun i =>
        some ((labels x).get i, x.queries.getD ((labels x).get i) [])) := by
  unfold SourceQuery.adapt
  congr 1
  funext i
  change some (SourceQuery.decode (SourceQuery.encoding
    ((labels x).get i, x.queries.getD ((labels x).get i) []))) = _
  rw [SourceQuery.decode_encode]

/-- Readback after the actual full reply, with local tests and stop/output recomputed. -/
@[expose] def responseInput (x : Input) (reply : Word) : NativeRetention.Input :=
  Packets.assemble ⟨x.system, (labels x).length, [reply]⟩

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
    (limits : Limits (labels x).length)
    (sample : Sampler (labels x).length P) (seed : P)
    (hs : RuntimeControl.stopped (initial x) = false)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns) :
    let memory : Memory Unit (ServerState (labels x).length P) :=
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

/-- The same native blank-tape program interacts with one consistent external
source oracle. Source trajectories, hidden state, invoices and duration are
unchanged by the derived address/query adaptation. -/
theorem external_source_law {P : Type} (x : Input) (limits : Limits (labels x).length)
    (source : SourceQuery.SourceSampler P) (seed : P)
    (hs : RuntimeControl.stopped (initial x) = false)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns) :
    let memory : Memory Unit (ServerState (labels x).length P) :=
      ⟨ConcurrentBatch.initial seed, []⟩
    (NativeUnboundedExecution.terminal controller.program
      (environment limits (SourceQuery.adapt source (labels x).length))
        ⟨controller.program.initialConfig (encoding x), memory⟩).map
          (Option.map (NativeReplyContext.observe controller.context)) =
      (source (labels x).length (ConcurrentBatch.initial seed) (fun i =>
        some ((labels x).get i, x.queries.getD ((labels x).get i) []))).map
          fun (paths, next) =>
            let receipt := observe limits limits.deadline (batch x (live_nonempty x hs)) paths
            some (finished x memory (replyOf receipt)
              (commit (ConcurrentBatch.initial seed) receipt next)) := by
  dsimp only
  rw [source_law x limits (SourceQuery.adapt source (labels x).length) seed hs hd ht,
    source_sample]

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
theorem receipt_resources (x : Input) (hn : 0 < (labels x).length)
    (limits : Limits (labels x).length)
    (paths : Fin (labels x).length → CallTrace)
    (hcap : ∀ i, ((paths i).accrued (limits.cutoff i) : ℝ) ≤
      (GreedyNative.oracleAt x.planner.val ((labels x).get i)).cost) :
    let receipt := observe limits limits.deadline (batch x hn) paths
    (receipt.tokens : ℝ) ≤ (Cslib.Algorithms.Lean.Multicover.bill
      ((labels x).map (GreedyNative.oracleAt x.planner.val)) : ℝ) ∧
      receipt.duration ≤ limits.deadline := by
  dsimp only
  refine ⟨?_, observe_duration_le _ _ _ _⟩
  have h := observe_tokens_le limits limits.deadline (batch x hn) paths
    (fun i => ((GreedyNative.oracleAt x.planner.val ((labels x).get i)).cost : ℝ))
    (fun i _ => hcap i)
  have he : active (batch x hn).slots = Finset.univ := active_slots x
  rw [he] at h
  calc
    _ ≤ ∑ i, ((GreedyNative.oracleAt x.planner.val ((labels x).get i)).cost : ℝ) := h
    _ = _ := by
      rw [← List.sum_ofFn]
      have h := List.ofFn_getElem_eq_map (labels x)
        (fun j => ((GreedyNative.oracleAt x.planner.val j).cost : ℝ))
      simpa only [List.get_eq_getElem, Cslib.Algorithms.Lean.Multicover.bill,
        Rat.cast_list_sum, List.map_map, Function.comp_def] using congrArg List.sum h


/-- The actual named native program terminates after one source-admitted batch,
with its complete terminal bill and oracle duration bounded from per-call accrued
caps on possible joint trajectories. No bounded-total-bill, termination, native
representation or independence premise is supplied. -/
theorem native_resources {P : Type} (x : Input)
    (limits : Limits (labels x).length)
    (sample : Sampler (labels x).length P) (seed : P)
    (hs : RuntimeControl.stopped (initial x) = false)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns)
    (hcap : ∀ pair ∈ (sample (ConcurrentBatch.initial seed)
      (batch x (live_nonempty x hs))).support, ∀ i,
      ((pair.1 i).accrued (limits.cutoff i) : ℝ) ≤
        (GreedyNative.oracleAt x.planner.val ((labels x).get i)).cost)
    (outcome : Option (NativeReplyContext.Observation
      (ServerState (labels x).length P)))
    (houtcome : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample) ⟨controller.program.initialConfig (encoding x),
        ⟨ConcurrentBatch.initial seed, []⟩⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧
      (tokenBill final.memory.events : ℝ) ≤ (Cslib.Algorithms.Lean.Multicover.bill
        ((labels x).map (GreedyNative.oracleAt x.planner.val)) : ℝ) ∧
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
