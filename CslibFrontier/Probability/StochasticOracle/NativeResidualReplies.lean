/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualEncoding
import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchReceipts
import Mathlib.Tactic

/-!
# Original residual families through actual raw source replies

[Wang2027], setup (2)--(3) and Theorem 6, PDF pp. 12--13. Original source
families are encoded as candidate masks inside the actual concurrent report
codec. The native streaming parser and rational retention operate on those bytes,
including arbitrary invoice bits, inactive opportunities and cancellation.
No parser-validity, decoded-family or desired-retention law is assumed.

This connects the original-label construction to actual runtime local processing.
Downstream, `NativeResidualAttainment` and `NativeResidualAll` derive source
admission and complete native execution for the runtime-role controllers;
`NativeResidualPolicies` derives the native-to-behavioral competitor laws, and
`NativeResidualMinima` identifies the attained native one/two-turn optima and ratio.
The legacy least-element controller still needs its own canonical-role specialization.
Invoices use the existing natural wire format; no arbitrary-real invoice encoding
or deadline including local instructions is claimed.

## Main definitions

* `Answers`, `report`: original completed/canceled families and their raw source reports.
* `returned`, `work`: returned source families and the runtime raw-history input.
* `path`, `answersFor`: actual unit-latency trajectories and selected source reports.
* `afterNear`, `afterSpecialist`: runtime updates on those raw source replies.

## Main results

* `normalized_report`: actual raw parsing and normalization recover original labels.
* `observed_proposals`, `observed_resources`: actual receipts, raw words, invoices and unit latency.
* `retained`: full raw-history retention agrees with source local certification.
* `near_residual`, `near_live`: first raw reply computes the missing block and keeps the guard live.
* `completed_output`, `specialist_stopped`: the next raw reply yields the optimal decoded result.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualReplies
open Finset NativeRetention ResidualCover NativeResidualEncoding ConcurrentBatch
open scoped NNReal
variable {z n m k : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- One optional completed/canceled source family and invoice per opportunity.
Outer `none` means inactive; inner `none` means cancellation with its invoice. -/
abbrev Answers (k : ℕ) := Fin k → Option (Option (Finset (Candidate T)) × ℕ)

/-- Original candidate indices in the declared finite enumeration. -/
@[expose] def family (C : Finset (Candidate T)) : Finset (Fin m) :=
  C.map candidates.symm.toEmbedding

/-- Actual source report: original candidate masks, cancellation tags and
unrestricted natural invoice bits, before native packet parsing. -/
@[expose] def report (answers : Answers T k) : Report k :=
  fun i => (answers i).map fun receipt =>
    (receipt.1.map fun C => encodeFamily (family T candidates C), receipt.2)

/-- Completed source families in concurrent opportunity order. -/
@[expose] def returned (answers : Answers T k) : List (Finset (Candidate T)) :=
  (List.ofFn fun i => (answers i).bind fun receipt => receipt.1).filterMap id

/-- Native original-label WSC and its actual raw replies, newest first.
No decoded proposals are installed in this runtime input. -/
@[expose] def work (history : List (Answers T k)) : Packets.Work :=
  ⟨SourceEncoding.toNative (source T points candidates), k,
    history.map fun answers => encodeReport (report T candidates answers)⟩

private theorem family_labels (C : Finset (Candidate T)) :
    (family T candidates C).image Fin.val = C.map (candidateLabel T candidates) := by
  rw [family, Finset.map_eq_image, image_image, Finset.map_eq_image]
  rfl

private theorem proposals_report (answers : Answers T k) :
    proposals m (report T candidates answers) =
      (returned T answers).map (family T candidates) := by
  have hi (i : Fin k) :
      ((report T candidates answers) i).bind
          (fun receipt => receipt.1.bind (decodeFamily m)) =
        ((answers i).bind fun receipt => receipt.1).map (family T candidates) := by
    cases h : answers i with
    | none => simp [report, h]
    | some receipt =>
      rcases receipt with ⟨_ | C, tokens⟩ <;>
        simp [report, h, decodeFamily_encode]
  simp only [proposals, hi, returned, List.ofFn_eq_map, List.filterMap_map,
    List.map_filterMap, Function.comp_def, id_eq]

/-- The streaming parser, strict family masks and native normalization recover
exactly the returned original candidates; canceled and inactive slots add none. -/
theorem normalized_report (answers : Answers T k) :
    ((Packets.families k (SourceEncoding.toNative (source T points candidates)).rows.length
      (encodeReport (report T candidates answers))).map fun P =>
        (normalize (SourceEncoding.toNative (source T points candidates)) P).toFinset) =
      (returned T answers).map fun C => C.map (candidateLabel T candidates) := by
  have hn (x : NativeRetention.Input) (h : x.rows.length = m) (C : Finset (Fin m)) :
      (normalize x (sourceIndices C)).toFinset = C.image Fin.val := by
    subst m
    exact BatchReceipts.normalize_sourceIndices x C
  rw [rows_length, Packets.families_report, proposals_report, List.map_map, List.map_map]
  apply List.map_congr_left
  intro C _
  simp only [Function.comp_apply]
  rw [hn _ (rows_length T points candidates), family_labels]

/-- Concrete source call: a completed original family returns at unit latency,
or cancellation has no returned word. The invoice is accrued in either case. -/
@[expose] def path (C : Option (Finset (Candidate T))) (invoice : ℕ) : CallTrace :=
  ⟨C.map (fun F => (1, encodeFamily (family T candidates F))),
    fun _ => invoice, fun _ _ _ => le_refl _⟩

/-- Only the already selected preformed batch acquires source reports.
The vector of joint replies need not have independent coordinates. -/
@[expose] def answersFor (batch : Batch k)
    (families : Fin k → Option (Finset (Candidate T))) (invoices : Fin k → ℕ) : Answers T k :=
  fun i => (batch.slots i).map fun _ => (families i, invoices i)

/-- Observing the actual call trajectories at unit cutoff gives precisely the
encoded source report, including cancellation invoices and inactive slots. -/
theorem observe_report (limits : Limits k) (remaining : ℝ≥0) (batch : Batch k)
    (families : Fin k → Option (Finset (Candidate T))) (invoices : Fin k → ℕ)
    (hcut : ∀ i, limits.cutoff i = 1) (hremaining : 1 ≤ remaining) :
    (observe limits remaining batch (fun i => path T candidates (families i) (invoices i))).report =
      report T candidates (answersFor T batch families invoices) := by
  funext i
  cases hs : batch.slots i with
  | none => simp [observe, report, answersFor, hs]
  | some word =>
    cases hc : families i <;>
      simp [observe, report, answersFor, hs, path, hc, CallTrace.report,
        CallTrace.response, hcut, min_eq_left hremaining]

/-- The actual receipt's raw wire word, not a supplied decoded report, is fed
through the native streaming parser. The input batch was fixed before the joint
response vector; no response-independence or parser-validity premise appears. -/
theorem observed_proposals (limits : Limits k) (remaining : ℝ≥0) (batch : Batch k)
    (families : Fin k → Option (Finset (Candidate T))) (invoices : Fin k → ℕ)
    (hcut : ∀ i, limits.cutoff i = 1) (hremaining : 1 ≤ remaining) :
    (Packets.families k (SourceEncoding.toNative (source T points candidates)).rows.length
      (replyOf (observe limits remaining batch
        (fun i => path T candidates (families i) (invoices i)))).word).map
          (fun P => (normalize (SourceEncoding.toNative (source T points candidates)) P).toFinset) =
      (returned T (answersFor T batch families invoices)).map
        (fun C => C.map (candidateLabel T candidates)) := by
  change (Packets.families _ _ (encodeReport _)).map _ = _
  rw [observe_report T candidates limits remaining batch families invoices hcut hremaining]
  exact normalized_report T points candidates _

/-- The same trajectories retain every active invoice, including canceled calls;
their maximum concurrent latency is one. These are derived joint resources. -/
theorem observed_resources (limits : Limits k) (remaining : ℝ≥0) (batch : Batch k)
    (families : Fin k → Option (Finset (Candidate T))) (invoices : Fin k → ℕ)
    (hcut : ∀ i, limits.cutoff i = 1) (hremaining : 1 ≤ remaining) :
    let receipt := observe limits remaining batch
      (fun i => path T candidates (families i) (invoices i))
    receipt.tokens = ∑ i ∈ active batch.slots, invoices i ∧ receipt.duration = 1 := by
  dsimp only
  constructor
  · rw [observe_tokens]
    rfl
  · have htime (i : Fin k) (hi : i ∈ active batch.slots) :
        (observe limits remaining batch
          (fun j => path T candidates (families j) (invoices j))).time i = 1 := by
      have hs : (batch.slots i).isSome = true := (mem_filter.mp hi).2
      cases hc : families i <;>
        simp [observe, path, CallTrace.stop, hs, hc, hcut, min_eq_left hremaining]
    change (active batch.slots).sup
      (observe limits remaining batch
        (fun i => path T candidates (families i) (invoices i))).time = 1
    rw [Finset.sup_congr rfl htime]
    exact Finset.sup_const batch.nonempty 1

private theorem retain_labels (hz : 0 < z) (C : Finset (Candidate T))
    (ps : List (Finset (Candidate T))) :
    (nativeInstance T points candidates hz).retain 1 (C.map (candidateLabel T candidates))
        (ps.map fun P => P.map (candidateLabel T candidates)) =
      ((coverInstance T hz).retain 1 C ps).map (candidateLabel T candidates) := by
  classical
  induction ps generalizing C with
  | nil => rfl
  | cons P ps ih =>
    simp only [List.map_cons, PartialCover.Instance.retain]
    rw [certified_label]
    split_ifs with h
    · rw [← Finset.map_union, ih]
    · exact ih C

/-- Full newest-first raw histories, with arbitrary correlated reports, yield
exactly chronological source retention under original labels. -/
theorem retained (hz : 0 < z) (history : List (Answers T k)) :
    (retain (Packets.assemble (work T points candidates history))).toFinset =
      ((coverInstance T hz).retain 1 ∅ (history.reverse.flatMap (returned T))).map
        (candidateLabel T candidates) := by
  let x := SourceEncoding.toNative (source T points candidates)
  let data := Packets.assemble (work T points candidates history)
  have hx : Valid x := SourceEncoding.valid_toNative _ (source_valid T points candidates hz)
  have hv : Valid data := ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  have hi : instanceOf data hv = nativeInstance T points candidates hz := rfl
  rw [retain_eq data hv, hi]
  have hr : (data.rho : ℝ) = 1 := by simp [data, work, Packets.assemble, source,
    SourceEncoding.toNative]
  rw [hr]
  have hp : (data.proposals.map fun P => (normalize data P).toFinset) =
      (history.reverse.flatMap (returned T)).map fun C => C.map (candidateLabel T candidates) := by
    change ((history.map (fun answers => encodeReport
      (report T candidates answers))).reverse.flatMap
      (Packets.families k x.rows.length)).map (fun P => (normalize x P).toFinset) = _
    rw [← List.map_reverse, List.flatMap_map, List.map_flatMap, List.map_flatMap]
    congr 1
    funext answers
    exact normalized_report T points candidates answers
  rw [hp]
  simpa only [map_empty] using retain_labels T points candidates hz ∅
    (history.reverse.flatMap (returned T))

/-- The computed runtime completion flag is exactly full source coverage after
parsing and local certification of the raw history. -/
theorem completion (hz : 0 < z) (history : List (Answers T k)) :
    (Packets.decision (work T points candidates history)).1 = true ↔
      (coverInstance T hz).covered
        ((coverInstance T hz).retain 1 ∅ (history.reverse.flatMap (returned T))) =
          (coverInstance T hz).ground := by
  let data := Packets.assemble (work T points candidates history)
  have hx := SourceEncoding.valid_toNative _ (source_valid T points candidates hz)
  have hv : Valid data := ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  have hi : instanceOf data hv = nativeInstance T points candidates hz := rfl
  change complete data = true ↔ _
  rw [complete_eq data hv, hi, retained, covered_label, ground_label]
  exact Finset.map_injective (pointLabel T points) |>.eq_iff

/-- The actual output mask decodes to the original-label retained source
family, for the entire raw history, rather than an assumed output witness. -/
theorem decoded_output (hz : 0 < z) (history : List (Answers T k)) :
    ∃ F, decodeFamily (SourceEncoding.toNative (source T points candidates)).rows.length
        (Packets.decision (work T points candidates history)).2 = some F ∧
      F.image Fin.val =
        ((coverInstance T hz).retain 1 ∅ (history.reverse.flatMap (returned T))).map
          (candidateLabel T candidates) := by
  let data := Packets.assemble (work T points candidates history)
  refine ⟨outputFamily data, decode_output data, ?_⟩
  change (outputFamily data).image (fun i : Fin data.rows.length => i.val) = _
  rw [outputFamily_image data]
  exact retained T points candidates hz history

/-- One actual completed source call in an arbitrary opportunity slot. -/
@[expose] def single (slot : Fin k) (C : Finset (Candidate T)) (invoice : ℕ) : Answers T k :=
  fun i => if i = slot then some (some C, invoice) else none

/-- Opportunity position and invoice size do not change which source family
is returned by this actual encoded single-call report. -/
theorem returned_single (slot : Fin k) (C : Finset (Candidate T)) (invoice : ℕ) :
    returned T (single T slot C invoice) = [C] := by
  induction k with
  | zero => exact Fin.elim0 slot
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) slot
    · simp [returned, single, List.ofFn_succ]
    · have hj : (0 : Fin (k + 1)) ≠ j.succ := by
        intro h
        have he := congrArg Fin.val h
        simp at he
      simpa [returned, single, List.ofFn_succ, hj] using ih j

/-- Actual runtime context after the first encoded near-cover reply. -/
@[expose] def afterNear (j : Fin z) (invoice : ℕ) : RuntimeControl.State :=
  RuntimeControl.afterReply (NativeResidualSelector.initial z (source T points candidates))
    (encodeReport (report T candidates
      (single T (0 : Fin (z + 1)) (payload T (univ.erase j)) invoice)))

/-- Actual runtime context after the specialist's encoded reply, with the same
original instance and the first raw report still in runtime history. -/
@[expose] def afterSpecialist (j : Fin z)
    (nearInvoice specialistInvoice : ℕ) : RuntimeControl.State :=
  RuntimeControl.afterReply (afterNear T points candidates j nearInvoice)
    (encodeReport (report T candidates
      (single T j.succ (specialist T j) specialistInvoice)))

private theorem near_retained (hz : 3 ≤ z) (j : Fin z) (invoice : ℕ) :
    (retain (Packets.assemble (afterNear T points candidates j invoice).work)).toFinset =
      (payload T (univ.erase j)).map (candidateLabel T candidates) := by
  change (retain (Packets.assemble (work T points candidates
    [single T (0 : Fin (z + 1)) (payload T (univ.erase j)) invoice]))).toFinset = _
  rw [retained T points candidates (by omega)]
  obtain ⟨hc, _⟩ := responses_certified T hz j
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
    returned_single, List.flatMap_nil, List.append_nil, PartialCover.Instance.retain,
    hc, ite_true, empty_union]

/-- The residual computed from the actual first raw reply is exactly its
original missing block; neither a residual tag nor a decoding law is supplied. -/
theorem near_residual (hz : 3 ≤ z) (j : Fin z) (invoice : ℕ) :
    (NativeResidualSelector.residual (afterNear T points candidates j invoice)).toFinset =
      (groundBlock T j).map (pointLabel T points) := by
  let data := Packets.assemble (afterNear T points candidates j invoice).work
  have hx := SourceEncoding.valid_toNative _ (source_valid T points candidates (by omega))
  have hv : Valid data := ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  have hi : instanceOf data hv = nativeInstance T points candidates (by omega) := rfl
  have he : (NativeResidualSelector.residual (afterNear T points candidates j invoice)).toFinset =
      (instanceOf data hv).ground \ (instanceOf data hv).covered (retain data).toFinset := by
    rw [← covered_eq]
    ext e
    simp [NativeResidualSelector.residual, instanceOf, List.mem_toFinset, data]
  rw [he, hi, near_retained T points candidates hz, native_near_residual]

/-- The actual first reply does not stop the selector: the missing block is
nonempty and the native completion bit is false while all budgets remain. -/
theorem near_live (hz : 3 ≤ z) (j : Fin z) (invoice : ℕ) :
    RuntimeControl.stopped (afterNear T points candidates j invoice) = false := by
  have hx := SourceEncoding.valid_toNative _ (source_valid T points candidates (by omega))
  let data := Packets.assemble (afterNear T points candidates j invoice).work
  have hv : Valid data := ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  have hi : instanceOf data hv = nativeInstance T points candidates (by omega) := rfl
  have hne : (nativeInstance T points candidates (by omega)).covered
      ((payload T (univ.erase j)).map (candidateLabel T candidates)) ≠
        (nativeInstance T points candidates (by omega)).ground := by
    rw [covered_label, ground_label, ne_eq, Finset.map_inj]
    obtain ⟨_, hnear, _, _⟩ := near_specialist_properties T hz j
    exact hnear
  have hc : (Packets.decision (afterNear T points candidates j invoice).work).1 = false := by
    apply Bool.eq_false_iff.mpr
    change complete data ≠ true
    intro hc
    have h := (complete_eq data hv).mp hc
    rw [hi, near_retained T points candidates hz] at h
    exact hne h
  have hcounter : decide ((afterNear T points candidates j invoice).opportunities = 0) = false := by
    simp only [afterNear, RuntimeControl.afterReply, NativeResidualSelector.initial,
      Nat.add_sub_cancel_right, decide_eq_false_iff_not]
    omega
  change (decide (1 = 0) || decide
    ((afterNear T points candidates j invoice).opportunities = 0) || decide (1 = 0) || _) = false
  rw [hcounter, hc]
  rfl

private theorem specialist_retained (hz : 3 ≤ z) (j : Fin z)
    (nearInvoice specialistInvoice : ℕ) :
    (retain (Packets.assemble
      (afterSpecialist T points candidates j nearInvoice specialistInvoice).work)).toFinset =
        (payload T univ).map (candidateLabel T candidates) := by
  classical
  change (retain (Packets.assemble (work T points candidates
    [single T j.succ (specialist T j) specialistInvoice,
      single T (0 : Fin (z + 1)) (payload T (univ.erase j)) nearInvoice]))).toFinset = _
  rw [retained T points candidates (by omega)]
  obtain ⟨hnear, hspecialist⟩ := responses_certified T hz j
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.flatMap_cons, returned_single, List.flatMap_nil, List.append_nil,
    List.cons_append, PartialCover.Instance.retain, hnear, ite_true, empty_union, hspecialist]
  have hsingle : payload T {j} = specialist T j := by simp [payload]
  rw [← hsingle, ← payload_union]
  have hu : univ.erase j ∪ {j} = univ := by ext i; simp
  rw [hu]

/-- After both actual raw reports, the computed completion flag is true and
the source decoder reads a full weight-one optimal native WSC family. Invoice
sizes and the hidden exact covers are not supplied to the native local test. -/
theorem completed_output (hz : 3 ≤ z) (j : Fin z) (nearInvoice specialistInvoice : ℕ) :
    let state := afterSpecialist T points candidates j nearInvoice specialistInvoice
    let I := nativeInstance T points candidates (by omega)
    (Packets.decision state.work).1 = true ∧
      ∃ F, decodeFamily (SourceEncoding.toNative (source T points candidates)).rows.length
          (RuntimeControl.result state) = some F ∧
        I.covered (F.image Fin.val) = I.ground ∧ I.cost (F.image Fin.val) = 1 := by
  dsimp only
  let state := afterSpecialist T points candidates j nearInvoice specialistInvoice
  let data := Packets.assemble state.work
  have hx := SourceEncoding.valid_toNative _ (source_valid T points candidates (by omega))
  have hv : Valid data := ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  have hi : instanceOf data hv = nativeInstance T points candidates (by omega) := rfl
  obtain ⟨hcover, hcost, _⟩ := native_primal_optimum T points candidates (by omega)
  have hc : (Packets.decision state.work).1 = true := by
    change complete data = true
    rw [complete_eq data hv, hi, specialist_retained T points candidates hz]
    exact hcover
  refine ⟨hc, outputFamily data, ?_, ?_, ?_⟩
  · change decodeFamily data.rows.length (RuntimeControl.result state) = _
    simp only [RuntimeControl.result, hc, ite_true]
    exact decode_output data
  · change (nativeInstance T points candidates (by omega)).covered
      ((outputFamily data).image (fun i : Fin data.rows.length => i.val)) = _
    rw [outputFamily_image data, specialist_retained T points candidates hz]
    exact hcover
  · change (nativeInstance T points candidates (by omega)).cost
      ((outputFamily data).image (fun i : Fin data.rows.length => i.val)) = _
    rw [outputFamily_image data, specialist_retained T points candidates hz]
    exact hcost

/-- Completion after the raw specialist reply triggers the actual stop guard,
so the final mask is emitted without issuing a third query. -/
theorem specialist_stopped (hz : 3 ≤ z) (j : Fin z) (nearInvoice specialistInvoice : ℕ) :
    RuntimeControl.stopped
      (afterSpecialist T points candidates j nearInvoice specialistInvoice) = true := by
  have h := (completed_output T points candidates hz j nearInvoice specialistInvoice).1
  simp only [RuntimeControl.stopped, h, Bool.or_true]

end Cslib.Probability.StochasticOracle.NativeResidualReplies
