/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualRouting
public import CslibFrontier.Probability.StochasticOracle.NativeResidualOptimum
public import CslibFrontier.Computability.Probabilistic.NativeBatch.TerminalResources
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.RuntimeProvenance
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOutputObservation
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Source residual routing from original runtime role metadata

[Wang2027], Theorem 6 setup (2)--(3), PDF pp. 12--13. The role table is
constructed from the known source subuniverses without using their hidden covers.
Original point and candidate enumerations are arbitrary. Routing reads the actual
retained residual after full raw-response parsing and local certification. The
same named native controller has certified success one, selection-only admission
and exact accrued expected bill. It attains the existing native OPT whenever the
adaptive alternative is cheaper. The all-specialist case and native one-turn
optimum remain separate; this is not the full source Theorem 6 equality.

## Main definitions

* `universes`, `input`: witness-free original instance and source-role input.
* `afterNear`: actual runtime update after the raw near report.

## Main results

* `roles_initial`, `roles_afterNear`: actual tape-decoded routing metadata.
* `second_slots`, `first_source`, `second_source`: actual selected requests and source dispatch.
* `native_law`, `native_resources`: joint compiled tape-output, memory, bill and duration laws.
* `native_certified`, `native_selectionOnly`: source deadline success and actual native admission.
* `native_expected_cost`, `native_cost_mem`: exact accrued cost attained by the same code.
* `native_optimum_of_adaptive_le`: equality with the native OPT when adaptation is cheaper.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualAttainment
open Turing NativeOpenExecution Turing.MultiTapeTM Finset NativeRetention ResidualCover
open NativeResidualEncoding ConcurrentBatch
open NativeResidualRouting
open Cslib.Optimization.OneConstraint
open scoped NNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- Known near/specialist subuniverses in original role order, with no hidden
exact-cover responses. Point labels remain those of the original input. -/
@[expose] def universes : List (List ℕ) :=
  List.range n :: List.ofFn (NativeResidualOracle.blockPoints T points)

/-- Original runtime input for both native strategies. Only the WSC instance,
known role subuniverses and scalar budgets are installed, not a prepared context. -/
@[expose] def input : GuardedStartup.Input :=
  ⟨⟨SourceEncoding.toNative (source T points candidates), 2, z + 1,
    roleWord (universes T points)⟩, 2⟩

/-- Original role metadata is decoded from the actual startup private word. -/
theorem roles_initial (adaptive : Bool) :
    roles (NativeResidualRouting.initial adaptive (input T points candidates)) =
      universes T points := by
  simp [roles, NativeResidualRouting.initial, input, GuardedStartup.state, RuntimeControl.initial,
    roleWord, unframe_frame, Decoder.decode_enc]

/-- Actual updated state after the complete raw near-cover report. -/
@[expose] def afterNear (j : Fin z) (invoice : ℕ) : RuntimeControl.State :=
  RuntimeControl.afterReply (NativeResidualRouting.initial true (input T points candidates))
    (encodeReport (NativeResidualReplies.report T candidates
      (NativeResidualReplies.single T (0 : Fin (z + 1)) (payload T (univ.erase j)) invoice)))

/-- Appended replies cannot replace or corrupt the original role-table frame. -/
theorem roles_afterNear (j : Fin z) (invoice : ℕ) :
    roles (afterNear T points candidates j invoice) = universes T points :=
  roles_afterReply _ _ rfl _

private theorem blockPoints_set (j : Fin z) :
    (NativeResidualOracle.blockPoints T points j).toFinset =
      (groundBlock T j).map (pointLabel T points) := by
  ext e
  simp only [NativeResidualOracle.blockPoints, List.mem_toFinset, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp he
    exact ⟨(points.symm p).isLt, Finset.mem_map.mpr ⟨p, hp, rfl⟩⟩

private theorem blockPoints_injective :
    Function.Injective (fun j => (NativeResidualOracle.blockPoints T points j).toFinset) := by
  intro i j h
  simp only [blockPoints_set, Finset.map_inj] at h
  let e : Fin (3 * (T i).r) := ⟨0, by have := (T i).r_pos; omega⟩
  have he : (⟨i, e⟩ : Point T) ∈ groundBlock T j := by
    rw [← h]
    exact (mem_groundBlock T i ⟨i, e⟩).mpr rfl
  exact (mem_groundBlock T j ⟨i, e⟩).mp he

/-- The actual decoded near response leaves precisely the original missing
subuniverse, independently of the numeric order of the point labels. -/
theorem afterNear_residual (hz : 3 ≤ z) (j : Fin z) (invoice : ℕ) :
    (NativeResidualSelector.residual (afterNear T points candidates j invoice)).toFinset =
      (NativeResidualOracle.blockPoints T points j).toFinset := by
  rw [blockPoints_set]
  have hwork : (afterNear T points candidates j invoice).work =
      (NativeResidualReplies.afterNear T points candidates j invoice).work := rfl
  simpa only [NativeResidualSelector.residual, hwork] using
    NativeResidualReplies.near_residual T points candidates hz j invoice

/-- The real updated guard remains live after the near reply. -/
theorem afterNear_live (hz : 3 ≤ z) (j : Fin z) (invoice : ℕ) :
    RuntimeControl.stopped (afterNear T points candidates j invoice) = false := by
  have hwork : (afterNear T points candidates j invoice).work =
      (NativeResidualReplies.afterNear T points candidates j invoice).work := rfl
  have hold := NativeResidualReplies.near_live T points candidates hz j invoice
  change (decide (1 = 0) || decide (z + 1 - 1 = 0) || decide (1 = 0) || _) = false at hold ⊢
  rw [hwork]
  exact hold

/-- The next native packet selects exactly the original missing specialist and
uses its exact original source-query bytes. No admission or routing law is a premise. -/
theorem second_slots (hz : 3 ≤ z) (j : Fin z) (invoice : ℕ) :
    slots (afterNear T points candidates j invoice) =
      fun i : Fin (z + 1) => if i = j.succ then
        some (NativeResidualOracle.query T points candidates i) else none := by
  have hturn : (afterNear T points candidates j invoice).turns = 1 := rfl
  have hhistory : (afterNear T points candidates j invoice).work.history.isEmpty = false := rfl
  have hsystem : (afterNear T points candidates j invoice).work.system =
      SourceEncoding.toNative (source T points candidates) := rfl
  funext (i : Fin (z + 1))
  simp only [slots, selected, hturn, Nat.reduceEqDiff, ite_false,
    decide_true, Bool.true_and, hhistory, Bool.false_or, hsystem]
  rw [roles_afterNear]
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Fin.ext_iff]
  · have hr : (universes T points).getD k.succ.val [] =
        NativeResidualOracle.blockPoints T points k := by
      simp [universes, List.getD_eq_getElem?_getD]
    rw [hr]
    have he : sameUniverse (NativeResidualOracle.blockPoints T points k)
        (NativeResidualSelector.residual (afterNear T points candidates j invoice)) =
        decide (k = j) := by
      apply Bool.eq_iff_iff.mpr
      rw [sameUniverse_eq, afterNear_residual T points candidates hz, decide_eq_true_eq]
      exact blockPoints_injective T points |>.eq_iff
    rw [he]
    by_cases hk : k = j
    · subst k
      simp only [Fin.val_succ, Nat.succ_pos, decide_true, Bool.true_and, ite_true]
      rfl
    · simp [hk]

/-- Source unit-latency opportunities with the stated two-turn deadline. -/
@[expose] def limits : Limits (z + 1) := ⟨fun _ => 1, by intro _; norm_num, 2, 2⟩

/-- A preformed singleton query for an original source opportunity. -/
@[expose] def batch (i : Fin (z + 1)) : ConcurrentBatch.Batch (z + 1) :=
  ⟨fun k => if k = i then some (NativeResidualOracle.query T points candidates i) else none,
    ⟨i, by simp [active]⟩⟩

private theorem active_batch (i : Fin (z + 1)) :
    active (batch T points candidates i).slots = {i} := by
  ext k
  by_cases h : k = i <;> simp [active, batch, h]

/-- The executable singleton request selects exactly its original source role. -/
theorem calls_batch (i : Fin (z + 1)) :
    NativeResidualOracle.calls (batch T points candidates i) = {finSuccEquiv z i} := by
  rw [NativeResidualOracle.calls, active_batch, Finset.map_singleton]
  rfl

/-- Actual completed receipt at unit remaining allotment; the same receipt is
also observed at the initial remaining deadline two. -/
@[expose] def receipt (invoice : Fin (z + 1) → ℕ) (i : Fin (z + 1))
    (r : Option (Fin z)) : Exchange (z + 1) :=
  observe limits 1 (batch T points candidates i)
    (NativeResidualOracle.paths T points candidates invoice (batch T points candidates i) r)

private theorem observed_receipt (invoice : Fin (z + 1) → ℕ) (i : Fin (z + 1))
    (r : Option (Fin z)) (remaining : ℝ≥0) (hr : 1 ≤ remaining) :
    observe limits remaining (batch T points candidates i)
      (NativeResidualOracle.paths T points candidates invoice (batch T points candidates i) r) =
      receipt T points candidates invoice i r := by
  simp only [observe, limits, min_eq_left hr, receipt, min_self]

private theorem receipt_resources (invoice : Fin (z + 1) → ℕ)
    (i : Fin (z + 1)) (r : Option (Fin z)) :
    (receipt T points candidates invoice i r).tokens = invoice i ∧
      (receipt T points candidates invoice i r).duration = 1 := by
  have h := NativeResidualReplies.observed_resources T candidates limits 1
    (batch T points candidates i)
    (NativeResidualOracle.families T points candidates (batch T points candidates i) r)
    invoice (fun _ => rfl) le_rfl
  have hpaths : NativeResidualOracle.paths T points candidates invoice
      (batch T points candidates i) r = (fun k => NativeResidualReplies.path T candidates
        (NativeResidualOracle.families T points candidates (batch T points candidates i) r k)
        (invoice k)) := rfl
  rw [receipt, hpaths]
  simpa only [active_batch, Finset.sum_singleton] using h

private theorem receipt_report (invoice : Fin (z + 1) → ℕ)
    (i : Fin (z + 1)) (r : Option (Fin z)) :
    (receipt T points candidates invoice i r).report = fun k =>
      if k = i then some ((NativeResidualOracle.answer T r i).map
        (fun C => encodeFamily (NativeResidualReplies.family T candidates C)), invoice i)
      else none := by
  have hpaths : NativeResidualOracle.paths T points candidates invoice
      (batch T points candidates i) r = (fun k => NativeResidualReplies.path T candidates
        (NativeResidualOracle.families T points candidates (batch T points candidates i) r k)
        (invoice k)) := rfl
  rw [receipt, hpaths, NativeResidualReplies.observe_report T candidates limits 1
    (batch T points candidates i) _ invoice (fun _ => rfl) le_rfl]
  funext k
  by_cases hk : k = i
  · subst k
    simp [NativeResidualReplies.report, NativeResidualReplies.answersFor,
      batch, NativeResidualOracle.families]
  · simp [NativeResidualReplies.report, NativeResidualReplies.answersFor, batch, hk]

/-- A singleton source receipt depends on the invoice of its selected role only. -/
theorem receipt_congr (f g : Fin (z + 1) → ℕ) (i : Fin (z + 1))
    (r : Option (Fin z)) (h : f i = g i) :
    receipt T points candidates f i r = receipt T points candidates g i r := by
  have hr : (receipt T points candidates f i r).report =
      (receipt T points candidates g i r).report := by
    rw [receipt_report, receipt_report, h]
  change Exchange.mk (batch T points candidates i) _ _ =
    Exchange.mk (batch T points candidates i) _ _
  congr 1

private theorem first_slots :
    slots (NativeResidualRouting.initial true (input T points candidates)) =
      (batch T points candidates 0).slots := by
  have ht : (NativeResidualRouting.initial true (input T points candidates)).turns = 2 := rfl
  have hx : (NativeResidualRouting.initial true (input T points candidates)).work.system =
      SourceEncoding.toNative (source T points candidates) := rfl
  funext (i : Fin (z + 1))
  simp only [slots, selected, ht, ite_true, decide_eq_true_eq, hx,
    roles_initial T points candidates true]
  by_cases hi : i = 0
  · subst i
    simp [universes, batch, NativeResidualOracle.query]
  · have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hn, batch, hi]

/-- The actual runtime-computed first packet is the source's near-cover query. -/
theorem first_request : request (NativeResidualRouting.initial true (input T points candidates)) =
    encodeBatch (batch T points candidates 0) := by
  rw [request_eq, first_slots]
  rfl

/-- The actual updated second packet is the original missing specialist query. -/
theorem second_request (hz : 3 ≤ z) (j : Fin z) (invoice : ℕ) :
    request (afterNear T points candidates j invoice) =
      encodeBatch (batch T points candidates j.succ) := by
  rw [request_eq, second_slots T points candidates hz]
  congr 1
  funext i
  by_cases h : i = j.succ <;> simp [batch, h]

/-- Fresh source memory with no prior accepted or rejected events. -/
@[expose] def initialMemory : Memory Unit (ServerState (z + 1) Unit) :=
  ⟨ConcurrentBatch.initial (), []⟩
/-- Actual source memory after the first correlated near-cover receipt. -/
@[expose] def afterNearMemory (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    Memory Unit (ServerState (z + 1) Unit) :=
  (initialMemory (z := z)).record ((), encodeBatch (batch T points candidates 0))
    (replyOf (receipt T points candidates invoice 0 (some j)))
    (commit (ConcurrentBatch.initial ()) (receipt T points candidates invoice 0 (some j)) ())

private theorem first_admit : admit limits (ConcurrentBatch.initial ())
    (encodeBatch (batch T points candidates 0)) = some (batch T points candidates 0) := by
  simp [admit, decodeBatch_encode, ConcurrentBatch.initial, limits]

private theorem second_admit (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    admit limits (afterNearMemory T points candidates invoice j).privateState
      (encodeBatch (batch T points candidates j.succ)) =
        some (batch T points candidates j.succ) := by
  have hres := (receipt_resources T points candidates invoice 0 (some j)).2
  have hd : Disjoint (active (batch T points candidates j.succ).slots)
      (active (batch T points candidates 0).slots) := by
    rw [active_batch, active_batch]
    simp [Fin.ext_iff]
  simp only [admit, decodeBatch_encode, afterNearMemory, initialMemory, Memory.record, commit,
    ConcurrentBatch.initial, List.length_cons, List.length_nil, zero_add, Finset.union_empty]
  rw [hres]
  have hd' : Disjoint (active (batch T points candidates j.succ).slots)
      (active (receipt T points candidates invoice 0 (some j)).batch.slots) := hd
  exact ite_eq_left ⟨by norm_num [limits], by norm_num [limits], hd'⟩

/-- Actual first response with a possibly residual-dependent invoice, drawn
only after the original near batch has been selected. -/
theorem first_source_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z) :
    serve limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (request (NativeResidualRouting.initial true (input T points candidates)))
      (ConcurrentBatch.initial ()) =
      P.missing.toPMF.bind fun j =>
        (ν [] (batch T points candidates 0) (some j)).map fun invoice =>
          (replyOf (receipt T points candidates invoice 0 (some j)),
            (afterNearMemory T points candidates invoice j).privateState) := by
  rw [first_request]
  rw [serve_accepted _ _ _ _ _ (first_admit T points candidates)]
  have hc : NativeResidualOracle.calls (batch T points candidates 0) = {none} := by
    rw [calls_batch, finSuccEquiv_zero]
  simp only [NativeResidualConditionalInvoice.sample, hc, reply, Finset.mem_singleton, ite_true,
    Distribution.toPMF_map, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    ConcurrentBatch.initial]
  apply congrArg P.missing.toPMF.bind
  funext j
  apply congrArg (fun f => (ν [] (batch T points candidates 0) (some j)).map f)
  funext invoice
  have hremaining : (limits (z := z)).deadline -
      (ConcurrentBatch.initial (n := z + 1) ()).elapsed = 2 := by
    simp [limits, ConcurrentBatch.initial]
  simp only [ConcurrentBatch.initial] at hremaining
  rw [hremaining,
    observed_receipt T points candidates invoice 0 (some j) 2 (by norm_num)]
  rfl

/-- Actual follow-up response using the invoice law at its reached history,
including the already observed near invoice and selected specialist. -/
theorem second_source_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z) (hz : 3 ≤ z) (j : Fin z)
    (previous : Fin (z + 1) → ℕ) :
    serve limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (request (afterNear T points candidates j (previous 0)))
      (afterNearMemory T points candidates previous j).privateState =
      (ν (afterNearMemory T points candidates previous j).privateState.history
        (batch T points candidates j.succ) none).map fun invoice =>
        (replyOf (receipt T points candidates invoice j.succ none),
        commit (afterNearMemory T points candidates previous j).privateState
          (receipt T points candidates invoice j.succ none) ()) := by
  rw [second_request T points candidates hz,
    serve_accepted _ _ _ _ _ (second_admit T points candidates previous j)]
  simp only [NativeResidualConditionalInvoice.sample, calls_batch, finSuccEquiv_succ, reply,
    Finset.mem_singleton, reduceCtorEq, ite_false, Distribution.toPMF_pure,
    PMF.pure_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (fun f => (ν (afterNearMemory T points candidates previous j).privateState.history
    (batch T points candidates j.succ) none).map f)
  funext invoice
  have hremaining : (limits (z := z)).deadline -
      (afterNearMemory T points candidates previous j).privateState.elapsed = 1 := by
    have hres := (receipt_resources T points candidates previous 0 (some j)).2
    simp only [afterNearMemory, initialMemory, Memory.record, commit,
      ConcurrentBatch.initial, zero_add, hres, limits]
    exact tsub_eq_of_eq_add (by norm_num)
  rw [hremaining, observed_receipt T points candidates invoice j.succ none 1 le_rfl]


/-- The fixed-invoice first response specializes the conditional source law. -/
theorem first_source (P : Parameters z) (invoice : Fin (z + 1) → ℕ) :
    serve limits (NativeResidualOracle.sample T points candidates P invoice)
      (request (NativeResidualRouting.initial true (input T points candidates)))
      (ConcurrentBatch.initial ()) =
      P.missing.toPMF.map fun j =>
        (replyOf (receipt T points candidates invoice 0 (some j)),
          (afterNearMemory T points candidates invoice j).privateState) := by
  simpa only [NativeResidualConditionalInvoice.sample_const, NativeResidualInvoice.sample_pure,
    PMF.map, Function.comp_def, PMF.pure_bind] using
    first_source_conditional T points candidates P (fun _ _ _ => PMF.pure invoice)

/-- The fixed-invoice follow-up specializes the conditional source law. -/
theorem second_source (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (j : Fin z) (previous : Fin (z + 1) → ℕ := invoice) :
    serve limits (NativeResidualOracle.sample T points candidates P invoice)
      (request (afterNear T points candidates j (previous 0)))
      (afterNearMemory T points candidates previous j).privateState =
      PMF.pure (replyOf (receipt T points candidates invoice j.succ none),
        commit (afterNearMemory T points candidates previous j).privateState
          (receipt T points candidates invoice j.succ none) ()) := by
  simpa only [NativeResidualConditionalInvoice.sample_const, NativeResidualInvoice.sample_pure,
    PMF.pure_map] using
    second_source_conditional T points candidates P (fun _ _ _ => PMF.pure invoice) hz j previous

/-- The first actual native report is the original near-cover packet, including its invoice. -/
theorem near_word (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    (replyOf (receipt T points candidates invoice 0 (some j))).word =
      encodeReport (NativeResidualReplies.report T candidates
        (NativeResidualReplies.single T (0 : Fin (z + 1))
          (payload T (univ.erase j)) (invoice 0))) := by
  change encodeReport _ = _
  rw [receipt_report]
  congr 1
  funext i
  by_cases hi : i = 0 <;>
    simp [NativeResidualReplies.report, NativeResidualReplies.single,
      NativeResidualOracle.answer, hi]

private theorem specialist_word (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    (replyOf (receipt T points candidates invoice j.succ none)).word =
      encodeReport (NativeResidualReplies.report T candidates
        (NativeResidualReplies.single T j.succ (specialist T j) (invoice j.succ))) := by
  change encodeReport _ = _
  rw [receipt_report]
  congr 1
  funext i
  by_cases hi : i = j.succ <;>
    simp [NativeResidualReplies.report, NativeResidualReplies.single,
      NativeResidualOracle.answer, hi]

/-- Actual runtime context after both concrete source transactions. -/
@[expose] def afterSpecialist (invoice : Fin (z + 1) → ℕ) (j : Fin z) : RuntimeControl.State :=
  RuntimeControl.afterReply (afterNear T points candidates j (invoice 0))
    (replyOf (receipt T points candidates invoice j.succ none)).word

/-- Actual accepted-source memory after the response-dependent specialist call. -/
@[expose] def afterSpecialistMemory (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    Memory Unit (ServerState (z + 1) Unit) :=
  (afterNearMemory T points candidates invoice j).record
    ((), encodeBatch (batch T points candidates j.succ))
    (replyOf (receipt T points candidates invoice j.succ none))
    (commit (afterNearMemory T points candidates invoice j).privateState
      (receipt T points candidates invoice j.succ none) ())

/-- Both fixed strategies start live on every nonempty promised source instance. -/
theorem initial_live (adaptive : Bool) (hz : 3 ≤ z) :
    RuntimeControl.stopped (NativeResidualRouting.initial adaptive (input T points candidates)) =
      false := by
  let j : Fin z := ⟨0, by omega⟩
  let e : Fin (3 * (T j).r) := ⟨0, by have := (T j).r_pos; omega⟩
  have hn : 0 < n := Nat.zero_lt_of_lt (points.symm ⟨j, e⟩).isLt
  have hno : (Packets.decision
      (NativeResidualRouting.initial adaptive (input T points candidates)).work).1 = false := by
    simpa [Packets.decision, Packets.assemble, NativeResidualRouting.initial, input,
      GuardedStartup.state, RuntimeControl.initial, complete, ground, retain, covered,
      source, SourceEncoding.toNative, List.all_eq_false] using (⟨0, hn⟩ : ∃ x : ℕ, x < n)
  change (decide ((if adaptive then 2 else 1 : ℕ) = 0) ||
    decide (z + 1 = 0) || decide (2 = 0) || _) = false
  rw [hno]
  cases adaptive <;> simp

/-- The completed native runtime result decodes to a full weight-one cover;
no hidden cover or optimal-output contract is supplied to the program. -/
theorem completed (hz : 3 ≤ z) (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    ∃ C, decodeFamily (SourceEncoding.toNative (source T points candidates)).rows.length
        (RuntimeControl.result (afterSpecialist T points candidates invoice j)) = some C ∧
      (nativeInstance T points candidates (by omega)).covered (C.image Fin.val) =
        (nativeInstance T points candidates (by omega)).ground ∧
      (nativeInstance T points candidates (by omega)).cost (C.image Fin.val) = 1 := by
  have hw0 : (afterNear T points candidates j (invoice 0)).work =
      (NativeResidualReplies.afterNear T points candidates j (invoice 0)).work := rfl
  have hw : (afterSpecialist T points candidates invoice j).work =
      (NativeResidualReplies.afterSpecialist T points candidates j (invoice 0)
        (invoice j.succ)).work := by
    change { (afterNear T points candidates j (invoice 0)).work with history :=
      (replyOf (receipt T points candidates invoice j.succ none)).word ::
        (afterNear T points candidates j (invoice 0)).work.history } = _
    rw [hw0, specialist_word]
    rfl
  have hout := (NativeResidualReplies.completed_output T points candidates hz j
    (invoice 0) (invoice j.succ)).2
  simpa only [RuntimeControl.result, hw] using hout

/-- The completed state actually takes the stop branch, with no further query. -/
theorem completed_stop (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    RuntimeControl.stopped (afterSpecialist T points candidates invoice j) = true := by
  have ht : (afterSpecialist T points candidates invoice j).turns = 0 := rfl
  simp [RuntimeControl.stopped, ht]

/-- Concrete source feedback law for the same clockless routing code. The source
near residual is sampled after the first query and determines the admitted next
request. The result retains original labels, raw history and actual joint resources. -/
theorem feedback_law (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z) :
    (Feedback.run (environment limits (NativeResidualOracle.sample T points candidates P invoice))
      2 (NativeResidualRouting.initial true (input T points candidates))
      (fun _ => ⟨[], [], 0⟩) initialMemory request).map
        (fun outcome => (outcome.state, outcome.memory)) =
      P.missing.toPMF.map fun j =>
        (afterSpecialist T points candidates invoice j,
          afterSpecialistMemory T points candidates invoice j) := by
  have henv : environment limits (NativeResidualOracle.sample T points candidates P invoice)
      ((), request (NativeResidualRouting.initial true (input T points candidates)))
      initialMemory = P.missing.toPMF.map (fun j =>
        (replyOf (receipt T points candidates invoice 0 (some j)),
          (afterNearMemory T points candidates invoice j).privateState)) := by
    change serve _ _ _ (ConcurrentBatch.initial ()) = _
    exact first_source T points candidates P invoice
  rw [Feedback.run, initial_live T points candidates true hz]
  simp only [Bool.false_eq_true, ite_false, PMF.monad_bind_eq_bind, PMF.map_bind]
  rw [henv, PMF.bind_map]
  have hstate (j : Fin z) : RuntimeControl.afterReply
      (NativeResidualRouting.initial true (input T points candidates))
      (replyOf (receipt T points candidates invoice 0 (some j))).word =
        afterNear T points candidates j (invoice 0) := by
    rw [near_word]
    rfl
  have hmem (j : Fin z) : initialMemory.record
      ((), request (NativeResidualRouting.initial true (input T points candidates)))
      (replyOf (receipt T points candidates invoice 0 (some j)))
      (afterNearMemory T points candidates invoice j).privateState =
        afterNearMemory T points candidates invoice j := by
    rw [first_request]
    rfl
  have henv2 (j : Fin z) : environment limits
      (NativeResidualOracle.sample T points candidates P invoice)
      ((), request (afterNear T points candidates j (invoice 0)))
      (afterNearMemory T points candidates invoice j) =
      PMF.pure (replyOf (receipt T points candidates invoice j.succ none),
        commit (afterNearMemory T points candidates invoice j).privateState
          (receipt T points candidates invoice j.succ none) ()) :=
    second_source T points candidates P invoice hz j
  simp only [Function.comp_def, hstate, hmem, Feedback.run,
    afterNear_live T points candidates hz, Bool.false_eq_true, ite_false, henv2,
    PMF.pure_bind, PMF.pure_map, PMF.monad_bind_eq_bind]
  simp only [second_request T points candidates hz]
  rfl

/-- End-to-end actual native terminal output and shared-memory law on the
original-label source oracle, not an assumed machine representation. -/
theorem native_law (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z) :
    (NativeUnboundedExecution.terminal (controller true).program
      (environment limits (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)),
        initialMemory⟩).map (Option.map fun world =>
          (world.config.tapes.output, world.memory)) =
      P.missing.toPMF.map fun j => some
        (RuntimeControl.result (afterSpecialist T points candidates invoice j),
          afterSpecialistMemory T points candidates invoice j) := by
  have h := congrArg (PMF.map (Option.map fun observation : NativeReplyContext.Observation
      (ServerState (z + 1) Unit) => (observation.output, observation.memory)))
    (controller_law true _
      (environment limits (NativeResidualOracle.sample T points candidates P invoice))
      (input T points candidates) initialMemory)
  simp only [PMF.map_comp, Function.comp_def, Option.map_map, NativeReplyContext.observe,
    ite_true] at h
  rw [h]
  have hf := congrArg (PMF.map (fun pair : RuntimeControl.State ×
      Memory Unit (ServerState (z + 1) Unit) =>
        some (RuntimeControl.result pair.1, pair.2)))
    (feedback_law T points candidates P invoice hz)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using hf


/-- The completed adaptive memory records exactly both selected role invoices
and two units of source elapsed time. -/
theorem afterSpecialistMemory_resources (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    tokenBill (afterSpecialistMemory T points candidates invoice j).events =
        (invoice 0 + invoice j.succ : ℕ) ∧
      elapsed (afterSpecialistMemory T points candidates invoice j).events = 2 := by
  obtain ⟨hfirstBill, hfirstTime⟩ := receipt_resources T points candidates invoice 0 (some j)
  obtain ⟨hsecondBill, hsecondTime⟩ := receipt_resources T points candidates invoice j.succ none
  simp only [afterSpecialistMemory, afterNearMemory, initialMemory, Memory.record,
    tokenBill, elapsed, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, replyOf,
    add_zero, hfirstBill, hfirstTime, hsecondBill, hsecondTime, Nat.cast_add]
  constructor
  · exact add_comm _ _
  · norm_num

/-- The completed adaptive source memory has elapsed time two, independently
of both role invoices and the selected residual. -/
theorem afterSpecialistMemory_elapsed (invoice : Fin (z + 1) → ℕ) (j : Fin z) :
    (afterSpecialistMemory T points candidates invoice j).privateState.elapsed = 2 := by
  simp only [afterSpecialistMemory, afterNearMemory, initialMemory, Memory.record, commit,
    ConcurrentBatch.initial, zero_add, (receipt_resources T points candidates invoice 0 (some j)).2,
    (receipt_resources T points candidates invoice j.succ none).2]
  norm_num

/-- Actual native accrued token bill and oracle duration, derived jointly for the
same program, source seed and runtime role table. Costs are paid on both calls;
the source near residual determines the second invoice. -/
theorem native_resources (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z) :
    (NativeUnboundedExecution.terminal (controller true).program
      (environment limits (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)),
        initialMemory⟩).map (Option.map fun world =>
          (tokenBill world.memory.events, elapsed world.memory.events)) =
      P.missing.toPMF.map fun j => some
        (((invoice 0 + invoice j.succ : ℕ) : ℝ≥0), (2 : ℝ≥0)) := by
  have h := congrArg (PMF.map (Option.map fun pair : Word ×
      Memory Unit (ServerState (z + 1) Unit) =>
        (tokenBill pair.2.events, elapsed pair.2.events)))
    (native_law T points candidates P invoice hz)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map, Option.map_some,
    (afterSpecialistMemory_resources T points candidates invoice _).1,
    (afterSpecialistMemory_resources T points candidates invoice _).2] using h

/-- The final native tape contains an optimal decoded source cover with
probability one, by the deadline. This is a statement about the actual compiled
output and oracle duration, not merely the local runtime result. -/
theorem native_optimal_output (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z) :
    let I := nativeInstance T points candidates (by omega)
    let good := fun result : Option (Word × Memory Unit (ServerState (z + 1) Unit)) =>
      result.any fun pair =>
        (decodeFamily (SourceEncoding.toNative (source T points candidates)).rows.length pair.1).any
          fun C => decide (I.covered (C.image Fin.val) = I.ground ∧
            I.cost (C.image Fin.val) = 1 ∧ elapsed pair.2.events ≤ 2)
    ((NativeUnboundedExecution.terminal (controller true).program
      (environment limits (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)),
        initialMemory⟩).map (Option.map fun world =>
          (world.config.tapes.output, world.memory))).map good = PMF.pure true := by
  classical
  dsimp only
  rw [native_law T points candidates P invoice hz, PMF.map_comp]
  have h (j : Fin z) :
      (decodeFamily (SourceEncoding.toNative (source T points candidates)).rows.length
        (RuntimeControl.result (afterSpecialist T points candidates invoice j))).any
        (fun C => decide ((nativeInstance T points candidates (by omega)).covered
          (C.image Fin.val) = (nativeInstance T points candidates (by omega)).ground ∧
          (nativeInstance T points candidates (by omega)).cost (C.image Fin.val) = 1 ∧
          elapsed (afterSpecialistMemory T points candidates invoice j).events ≤ 2)) = true := by
    obtain ⟨C, hdecode, hcover, hcost⟩ := completed T points candidates hz invoice j
    rw [hdecode]
    simp [hcover, hcost, (afterSpecialistMemory_resources T points candidates invoice j).2]
  simp only [Function.comp_def, Option.any_some, h]
  exact PMF.map_const _ _


open scoped ENNReal in
/-- The compiled adaptive controller attains its source expected token cost in
actual accrued-bill accounting. Termination is derived from its concrete native
law, so no divergent prefix is silently discarded and no integrability or
expected-resource conclusion is an input. -/
theorem native_expected_cost (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    NativeBatch.Quantitative.expected limits
      (NativeResidualOracle.sample T points candidates P invoice) (controller true).program
      NativeBatch.Trace.charge 3
      ⟨(controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)),
        initialMemory⟩ = ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) := by
  classical
  let program := (controller true).program
  let env := environment limits (NativeResidualOracle.sample T points candidates P invoice)
  let world := (⟨program.initialConfig (GuardedStartup.encoding (input T points candidates)),
    initialMemory⟩ : World (controller true).tapes (controller true).Controls
      Unit (ServerState (z + 1) Unit) (GuardedStartup.encoding (input T points candidates)))
  let μ := NativeUnboundedExecution.terminal program env world
  have hlaw := native_law T points candidates P invoice hz
  have hterm : μ none = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hn
    have hm : none ∈ (μ.map (Option.map fun next =>
        (next.config.tapes.output, next.memory))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
    rw [hlaw] at hm
    obtain ⟨j, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    cases he
  have he := NativeBatch.Quantitative.expected_charge_eq_terminal limits
    (NativeResidualOracle.sample T points candidates P invoice) program world
    (NativeBatch.initial_invariant limits ()) rfl hterm
  change NativeBatch.Quantitative.expected (limits (z := z))
    (NativeResidualOracle.sample T points candidates P invoice) program NativeBatch.Trace.charge
    ((limits (z := z)).turns + 1) world = _
  rw [he]
  have hm := PMF.tsum_map_mul μ (Option.map fun next =>
    (next.config.tapes.output, next.memory))
    (fun result => result.elim 0 (fun pair => (tokenBill pair.2.events : ℝ≥0∞)))
  simp only [Option.elim_map, Function.comp_def] at hm
  change (∑' result, μ result *
    result.elim 0 (fun next => (tokenBill next.memory.events : ℝ≥0∞))) = _
  rw [← hm, hlaw, PMF.tsum_map_mul]
  simp only [Option.elim_some, (afterSpecialistMemory_resources T points candidates invoice _).1]
  have hnear : (invoice 0 : ℝ) = P.nearCost := by simpa using hprice 0
  have hspec (j : Fin z) : (invoice j.succ : ℝ) = P.specialistCost j := by
    simpa using hprice j.succ
  have hmean : P.nearCost + P.missing.mean P.specialistCost =
      P.missing.mean (fun j => ((invoice 0 + invoice j.succ : ℕ) : ℝ)) := by
    rw [← Distribution.mean_const P.missing P.nearCost, ← Distribution.mean_add]
    congr 1
    funext j
    simp [Nat.cast_add, hnear, hspec]
  rw [hmean]
  simp only [Distribution.mean]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg (P.missing.nonneg j) (by positivity)), tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_mul (P.missing.nonneg j), ENNReal.ofReal_natCast]
  rfl


/-- Every decoded completed adaptive output comes from its actual response events. -/
theorem completed_output_provenance (invoice : Fin (z + 1) → ℕ) (j : Fin z)
    (hx : Valid (SourceEncoding.toNative (source T points candidates)))
    (C : Finset (Fin (SourceEncoding.toNative (source T points candidates)).rows.length))
    (hC : decodeFamily (SourceEncoding.toNative (source T points candidates)).rows.length
      (RuntimeControl.result (afterSpecialist T points candidates invoice j)) = some C) :
    C ⊆ NativeBatch.nativeAvailable (n := z + 1)
      (SourceEncoding.toNative (source T points candidates)).rows.length
      (afterSpecialistMemory T points candidates invoice j).events := by
  let state := afterSpecialist T points candidates invoice j
  have hwork : state.work.system = SourceEncoding.toNative (source T points candidates) := rfl
  have hopps : state.work.opportunities = z + 1 := rfl
  have hhistory : state.work.history =
      (afterSpecialistMemory T points candidates invoice j).events.map (fun e => e.reply.word) := by
    change [_ , _] = [_ , _]
    dsimp only
    rw [near_word T points candidates invoice j]
  apply RuntimeProvenance.result_available state _ (hwork.symm ▸ hx) hopps hhistory _ C hC
  intro word hw
  change word ∈ [_ , _] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;>
    exact (Packets.families_report _).trans (by simp only [replyOf, parseProposals_report])

/-- The compiled adaptive program is actually admitted in the source's native
selection-only class. Admission follows from its runtime retention and actual
raw response events, including all finite halted executions. -/
theorem native_selectionOnly (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (accept : Finset (Fin (SourceEncoding.toNative (source T points candidates)).rows.length) →
      Bool) :
    NativeUnboundedExecution.SelectionOnly (controller true).program
      (environment limits (NativeResidualOracle.sample T points candidates P invoice))
      (NativeBatch.candidateParser (n := z + 1)
        (SourceEncoding.toNative (source T points candidates)).rows.length)
      (decodeFamily (SourceEncoding.toNative (source T points candidates)).rows.length) accept
      ⟨(controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)),
        initialMemory⟩ := by
  intro fuel next hn C hC _
  have hh : NativeUnboundedExecution.halted next := by
    unfold NativeOpenSelection.result at hC
    split_ifs at hC with h
    exact Option.isNone_iff_eq_none.mp h
  have hs := (NativeUnboundedExecution.terminal_support _ _ _ _).mpr ⟨hh, fuel, hn⟩
  have hm : some (next.config.tapes.output, next.memory) ∈
      ((NativeUnboundedExecution.terminal (controller true).program
        (environment limits (NativeResidualOracle.sample T points candidates P invoice))
        ⟨(controller true).program.initialConfig
          (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
          (Option.map fun world => (world.config.tapes.output, world.memory))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨some next, hs, rfl⟩
  rw [native_law T points candidates P invoice hz] at hm
  obtain ⟨j, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  obtain ⟨ho, hm⟩ := Prod.mk.inj (Option.some.inj he)
  have hdecode : decodeFamily
      (SourceEncoding.toNative (source T points candidates)).rows.length
      (RuntimeControl.result (afterSpecialist T points candidates invoice j)) = some C := by
    have hhalt : next.config.tapes.state = none := hh
    simpa only [NativeOpenSelection.result, hhalt, Option.isNone_none, ite_true, ← ho] using hC
  rw [NativeBatch.candidateParser_proposals, ← hm]
  exact completed_output_provenance T points candidates invoice j
    (SourceEncoding.valid_toNative _ (source_valid T points candidates (by omega))) C hdecode



/-- Source promises derive validity of the actual original runtime WSC input. -/
theorem valid (hz : 0 < z) : Valid (input T points candidates).startup.system :=
  SourceEncoding.valid_toNative _ (source_valid T points candidates hz)

/-- The completed adaptive output passes the same tape certificate used for
all native competitors, with its actual deadline and source memory. -/
theorem completed_certifiedObservation (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z) (j : Fin z) :
    BatchOutput.certifiedObservation limits (input T points candidates).startup.system
      (valid T points candidates (by omega))
      (some (RuntimeControl.result (afterSpecialist T points candidates invoice j),
        afterSpecialistMemory T points candidates invoice j)) = true := by
  obtain ⟨C, hc, hcover, hcost⟩ := completed T points candidates hz invoice j
  have hI : instanceOf (input T points candidates).startup.system
      (valid T points candidates (by omega)) =
      nativeInstance T points candidates (by omega) := rfl
  have hrho : (input T points candidates).startup.system.rho = 1 := rfl
  have hc' : decodeFamily (input T points candidates).startup.system.rows.length
      (RuntimeControl.result (afterSpecialist T points candidates invoice j)) = some C := hc
  simp only [BatchOutput.certifiedObservation, Option.any_some, hc', BatchOutput.accept,
    hI, hrho, Rat.cast_one, one_mul, native_dual_objective]
  simp only [afterSpecialistMemory_elapsed, limits, le_refl, decide_true, Bool.and_true]
  change decide ((nativeInstance T points candidates (by omega)).covered (C.image Fin.val) =
    (nativeInstance T points candidates (by omega)).ground) &&
    decide ((nativeInstance T points candidates (by omega)).cost (C.image Fin.val) ≤ 1) = true
  simp only [hcover, hcost, le_refl, decide_true, Bool.and_self]

/-- The same named native controller has certified halted tape success one in
Theorem 5's exact event convention, including its oracle-only deadline. -/
theorem native_certified (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z) :
    ((NativeUnboundedExecution.terminal (controller true).program
      (environment limits (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)),
        initialMemory⟩).map (BatchOutput.certified limits (input T points candidates).startup.system
          (valid T points candidates (by omega)))) true = 1 := by
  rw [BatchOutput.terminal_certified, native_law T points candidates P invoice hz,
    PMF.map_comp]
  simp only [Function.comp_def, completed_certifiedObservation T points candidates invoice hz]
  simp only [PMF.map_apply, ite_true, PMF.tsum_coe]

open scoped ENNReal in
/-- The adaptive controller's exact actual bill is attained in the existing
common-oracle native competitor class, on the source's constructed original input. -/
theorem native_cost_mem (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) ∈
      BatchOptimum.costs limits (NativeResidualOracle.sample T points candidates P invoice)
        (input T points candidates) () (valid T points candidates (by omega)) 1 := by
  have hm : NativeBatch.Quantitative.expected limits
      (NativeResidualOracle.sample T points candidates P invoice) (controller true).program
      NativeBatch.Trace.charge 3
      ⟨(controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)),
        initialMemory⟩ ∈ BatchOptimum.costs limits
          (NativeResidualOracle.sample T points candidates P invoice)
          (input T points candidates) () (valid T points candidates (by omega)) 1 := by
    refine ⟨(controller true).tapes, (controller true).Controls, (controller true).finite,
      (controller true).program, native_selectionOnly T points candidates P invoice hz _, ?_, rfl⟩
    exact (native_certified T points candidates P invoice hz).ge
  rwa [native_expected_cost T points candidates P invoice hz hprice] at hm

open scoped ENNReal in
/-- A matching actual adaptive upper bound for the same native token infimum.
This statement asserts attained cost, not merely an abstract policy envelope. -/
theorem native_upper (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    BatchOptimum.optimum limits (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1 ≤
        ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) :=
  sInf_le (native_cost_mem T points candidates P invoice hz hprice)


open scoped ENNReal in
/-- The actual residual-controller bill is the attained native optimum whenever
the adaptive strategy is the cheaper source alternative. No native optimum or
success premise is supplied. The complementary all-specialist case is separate. -/
theorem native_optimum_of_adaptive_le (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost)
    (hcheaper : P.nearCost + P.missing.mean P.specialistCost ≤ ∑ j, P.specialistCost j) :
    BatchOptimum.optimum limits (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) := by
  apply le_antisymm (native_upper T points candidates P invoice hz hprice)
  let c := (finCongr (rows_length T points candidates)).trans candidates
  have hdata : (input T points candidates).startup.system =
      SourceEncoding.toNative (source T points c) := by
    rw [source_reindex]
    rfl
  have hlower := NativeResidualOptimum.two_lower T points (input T points candidates) c
    P limits invoice (by omega) (valid T points candidates (by omega)) hdata rfl hprice
  dsimp only [c, input] at hlower
  rw [NativeResidualOracle.sample_reindex T points candidates
    (rows_length T points candidates), min_eq_right hcheaper] at hlower
  exact hlower


end Cslib.Probability.StochasticOracle.NativeResidualAttainment
