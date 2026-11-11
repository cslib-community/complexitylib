/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualReplies
public import CslibFrontier.Probability.StochasticOracle.ResidualPolicy
public import CslibFrontier.Probability.FiniteTableOfPMF
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Quantitative
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# The residual construction as one actual native source oracle

[Wang2027], setup (1)--(3) and Theorem 6, PDF pp. 12--13. The near-cover
missing block is drawn only after a complete batch has been selected. Every
specialist has its fixed hidden exact cover. Invalid subinstance queries are
canceled, rather than receiving a fabricated valid source response. All native
machines use the same sampler; no machine-to-policy law is an input. The probability
fields of `Parameters` determine the residual law; its real-valued price fields
are not silently identified with the separate natural invoices.

## Main definitions

* `calls`: actual selected opportunity labels, with zero denoting the near cover.
* `query`, `families`, `sample`: actual source requests, responses and joint trajectory sampler.

## Main results

* `response_factor`: actual unbounded native response dispatch has the source conditional law.
* `response_record`: actual selected source calls agree with the appended receipt.
* `observe_proposals_subset`, `response_available`: raw proposals have source provenance.
* `batchCost_invoice`, `response_charge`: per-call prices yield actual accrued charges.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualOracle
open Finset NativeRetention ResidualCover NativeResidualEncoding ConcurrentBatch
open Cslib.Optimization.OneConstraint
open scoped NNReal ENNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- Original source call names of a concretely selected native batch. -/
@[expose] def calls (batch : ConcurrentBatch.Batch (z + 1)) : ResidualCover.Batch z :=
  (active batch.slots).map (finSuccEquiv z).toEmbedding

/-- Original point labels of a subuniverse, in the native increasing scan order. -/
@[expose] def blockPoints (j : Fin z) : List ℕ :=
  (List.range n).filter fun e => decide (e ∈ (groundBlock T j).map (pointLabel T points))

/-- Exact original-instance/subinstance source request; no exact-cover witness
is encoded in the request. -/
@[expose] def query (i : Fin (z + 1)) : Word :=
  NativeResidualSelector.queryEncoding
    ⟨SourceEncoding.toNative (source T points candidates),
      (finSuccEquiv z i).elim (List.range n) (blockPoints T points)⟩

/-- Ideal source responses for the sampled near-cover residual. -/
@[expose] def answer (r : Option (Fin z)) (i : Fin (z + 1)) : Option (Finset (Candidate T)) :=
  (finSuccEquiv z i).elim (r.map fun j => payload T (univ.erase j))
    (fun j => some (specialist T j))

/-- Only the original source request for that role receives its promised
family. A wrong subinstance is canceled, with its accrued invoice retained. -/
@[expose] def families (batch : ConcurrentBatch.Batch (z + 1)) (r : Option (Fin z)) :
    Fin (z + 1) → Option (Finset (Candidate T)) :=
  fun i => if batch.slots i = some (query T points candidates i) then answer T r i else none

/-- Unit-latency actual source trajectories, including wrong-query cancellations.
Invoices use the existing discrete wire costs. `batchCost_invoice` identifies these
with analytic source prices under an explicit
per-opportunity price convention. No native total-cost conclusion is an input. -/
@[expose] def paths (invoice : Fin (z + 1) → ℕ)
    (batch : ConcurrentBatch.Batch (z + 1)) (r : Option (Fin z)) : Fin (z + 1) → CallTrace :=
  fun i => NativeResidualReplies.path T candidates
    (families T points candidates batch r i) (invoice i)

/-- One consistent oracle for every native competitor. Specialist-only batches
have deterministic responses. A batch containing the near call samples its
full-support missing-block law only after selection, even if its query is wrong. -/
@[expose] def sample (P : Parameters z) (invoice : Fin (z + 1) → ℕ) : Sampler (z + 1) Unit :=
  fun _ batch => ((reply P (calls batch)).toPMF).map fun r =>
    (paths T points candidates invoice batch r, ())

/-- Each original opportunity is selected exactly when its original source call
label appears in the pre-response action. -/
theorem mem_calls (batch : ConcurrentBatch.Batch (z + 1)) (i : Fin (z + 1)) :
    finSuccEquiv z i ∈ calls batch ↔ i ∈ active batch.slots := by
  simp [calls]

open Turing NativeOpenExecution NativeInterface NativeBatch
variable {tapes : ℕ} {Control : Type} {input : List Bool}

/-- Actual source-call action at the selected native checkpoint. Halt, silent
divergence and non-query phases have the empty action. -/
@[expose] def selectedCalls (limits : Limits (z + 1))
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input)) :
    ResidualCover.Batch z :=
  ((sourceSignal limits hit).bind (fun (_, batch) => batch)).elim ∅ calls

private def fixedSample (invoice : Fin (z + 1) → ℕ) (r : Option (Fin z)) :
    Sampler (z + 1) Unit :=
  fun _ batch => PMF.pure (paths T points candidates invoice batch r, ())

/-- The actual native response with the current source residual fixed, retaining
its complete hidden state and exact resource receipt. Future source choices
remain in the ordinary sampler; this kernel fixes only this response. -/
def response (limits : Limits (z + 1)) (invoice : Fin (z + 1) → ℕ)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (r : Option (Fin z)) : PMF (Trace.State (z + 1) tapes Unit Control input) :=
  Trace.respond limits (fixedSample T points candidates invoice r) machine state hit

/-- At every actual native checkpoint, including silent divergence, dispatch
factors through the source response law of the already selected call set.
Work tapes, private random bits and raw query strings are not approximated. -/
theorem response_factor (P : Parameters z) (limits : Limits (z + 1))
    (invoice : Fin (z + 1) → ℕ) (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input)) :
    Trace.respond limits (sample T points candidates P invoice) machine state hit =
      (reply P (selectedCalls limits hit)).toPMF.bind
        (response T points candidates limits invoice machine state hit) := by
  change Trace.respond limits (sample T points candidates P invoice) machine state hit =
    (reply P (selectedCalls limits hit)).toPMF.bind (fun r =>
      Trace.respond limits (fixedSample T points candidates invoice r) machine state hit)
  cases hit with
  | none => simp [Trace.respond, respondSource, selectedCalls, sourceSignal, reply,
      Distribution.toPMF_pure]
  | some phase =>
    cases phase with
    | ready world =>
      simp only [selectedCalls, sourceSignal, Option.bind_some, Option.elim_none, reply,
        Finset.notMem_empty, ite_false, Distribution.toPMF_pure, PMF.pure_bind]
      rfl
    | pending chosen =>
      cases chosen with
      | halted world =>
        simp [selectedCalls, sourceSignal, reply, Distribution.toPMF_pure,
          Trace.respond, respondSource, phaseStep, dispatch]
      | «local» world =>
        simp [selectedCalls, sourceSignal, reply, Distribution.toPMF_pure,
          Trace.respond, respondSource, phaseStep, dispatch]
      | query world operation next =>
        cases operation
        cases ha : admit limits world.memory.privateState
          (world.config.channels ()).queryBuffer with
        | none =>
          simp [selectedCalls, sourceSignal, ha, reply, Distribution.toPMF_pure,
            Trace.respond, respondSource, phaseStep, dispatch, environment,
            serve_rejected _ _ _ _ ha]
        | some batch =>
          simp only [selectedCalls, sourceSignal, ha, Option.map_some, Option.bind_some,
            Option.elim_some]
          simp only [Trace.respond, respondSource, phaseStep, dispatch,
            environment, serve_accepted _ _ _ _ _ ha, sample, fixedSample,
            PMF.map_comp, Function.comp_def, PMF.pure_map]
          rfl

/-- A fixed residual with positive source mass is an actual response branch of
this same oracle, rather than a counterfactual program supplied by a caller. -/
theorem response_support (P : Parameters z) (limits : Limits (z + 1))
    (invoice : Fin (z + 1) → ℕ) (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (r : Option (Fin z)) (hr : r ∈ (reply P (selectedCalls limits hit)).toPMF.support)
    (hn : next ∈ (response T points candidates limits invoice machine state hit r).support) :
    next ∈ (Trace.respond limits (sample T points candidates P invoice)
      machine state hit).support := by
  rw [response_factor]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨r, hr, hn⟩

/-- The actual appended receipt carries exactly the selected source-call set.
No-call halt/divergence appends `none` and contributes the empty action. -/
theorem response_record (limits : Limits (z + 1)) (invoice : Fin (z + 1) → ℕ)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase)
    (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits invoice machine state hit r).support) :
    ∃ record, next.records = record :: state.records ∧
      selectedCalls limits hit = record.elim ∅ (fun receipt => calls receipt.batch) := by
  cases hit with
  | none =>
    simp only [response, Trace.respond, respondSource, PMF.pure_map,
      PMF.mem_support_pure_iff] at hn
    subst next
    exact ⟨none, rfl, rfl⟩
  | some phase =>
    have hb := hb phase rfl
    cases phase with
    | ready world =>
      change world.config.tapes.state = none at hb
      simp only [response, Trace.respond, respondSource, phaseStep, hb, Option.isNone_none,
        ite_true, PMF.pure_map, PMF.mem_support_pure_iff] at hn
      subst next
      exact ⟨none, rfl, rfl⟩
    | pending chosen =>
      cases chosen with
      | halted world => exact hb.elim
      | «local» world => exact hb.elim
      | query world operation control =>
        cases operation
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [sourceBoundary, ha] at hb
        | some batch =>
          simp only [response, Trace.respond, respondSource, phaseStep, dispatch, environment,
            serve_accepted _ _ _ _ _ ha, fixedSample, PMF.pure_map,
            PMF.mem_support_pure_iff] at hn
          subst next
          refine ⟨some (observe limits (limits.deadline - world.memory.privateState.elapsed)
            batch (paths T points candidates invoice batch r)), rfl, ?_⟩
          simp only [selectedCalls, sourceSignal, ha, Option.map_some, Option.bind_some,
            Option.elim_some]
          rfl

private theorem family_subset (batch : ConcurrentBatch.Batch (z + 1)) (r : Option (Fin z))
    (i : Fin (z + 1)) (F : Finset (Candidate T))
    (hF : families T points candidates batch r i = some F) :
    F ⊆ payload T (received (calls batch) r) := by
  classical
  have hq : batch.slots i = some (query T points candidates i) := by
    by_contra hn
    simp [families, hn] at hF
  have hi : finSuccEquiv z i ∈ calls batch :=
    (mem_calls batch i).mpr (by simp [active, hq])
  simp only [families, hq, ite_true, answer] at hF
  cases he : finSuccEquiv z i with
  | none =>
    rw [he] at hF
    cases r with
    | none => simp at hF
    | some j =>
      simp only [Option.elim_none, Option.map_some, Option.some.injEq] at hF
      rw [← hF]
      exact biUnion_subset_biUnion_of_subset_left _ (subset_union_right)
  | some j =>
    simp only [he, Option.elim_some, Option.some.injEq] at hF
    rw [← hF]
    apply subset_biUnion_of_mem
    simp only [received, mem_union, mem_filter, mem_univ, true_and]
    exact Or.inl (he ▸ hi)

/-- Every decoded proposal in an actual raw response comes from the ideal source
payload for the already selected batch. Wrong queries, cutoffs and cancellations
can delete proposals, but cannot invent a candidate. -/
theorem observe_proposals_subset (limits : Limits (z + 1)) (remaining : ℝ≥0)
    (invoice : Fin (z + 1) → ℕ) (batch : ConcurrentBatch.Batch (z + 1))
    (r : Option (Fin z)) (C : Finset (Fin m))
    (hC : C ∈ proposals m (observe limits remaining batch
      (paths T points candidates invoice batch r)).report) :
    C.map candidates.toEmbedding ⊆ payload T (received (calls batch) r) := by
  classical
  simp only [proposals, List.mem_filterMap, List.mem_ofFn] at hC
  obtain ⟨entry, ⟨i, rfl⟩, hC⟩ := hC
  cases hi : batch.slots i with
  | none => simp [observe, hi] at hC
  | some word =>
    cases hF : families T points candidates batch r i with
    | none => simp [observe, hi, paths, NativeResidualReplies.path, hF,
        CallTrace.report, CallTrace.response] at hC
    | some F =>
      simp only [observe, hi, Option.map_some, Option.bind_some, paths,
        NativeResidualReplies.path, hF, Option.map_some, CallTrace.report,
        CallTrace.response] at hC
      split_ifs at hC with ht
      · simp only [Option.bind_some, decodeFamily_encode, id_eq, Option.some.injEq] at hC
        subst C
        simpa [NativeResidualReplies.family, Finset.map_eq_image, Finset.image_image] using
          family_subset T points candidates batch r i F hF
      · simp at hC

/-- Original-label candidate availability from actual accepted raw receipts. -/
@[expose] def available (records : List (Trace.Record (z + 1))) : Finset (Candidate T) :=
  (sourceAvailable m (records.filterMap id)).map candidates.toEmbedding

private theorem observed_available (limits : Limits (z + 1)) (remaining : ℝ≥0)
    (invoice : Fin (z + 1) → ℕ) (batch : ConcurrentBatch.Batch (z + 1))
    (r : Option (Fin z)) :
    ((proposals m (observe limits remaining batch
      (paths T points candidates invoice batch r)).report).foldr (· ∪ ·) ∅).map
        candidates.toEmbedding ⊆ payload T (received (calls batch) r) := by
  have h := observe_proposals_subset T points candidates limits remaining invoice batch r
  generalize proposals m (observe limits remaining batch
    (paths T points candidates invoice batch r)).report = cs at *
  induction cs with
  | nil => simp
  | cons C cs ih =>
    simp only [List.foldr_cons, Finset.map_union]
    exact union_subset (h C (by simp)) (ih (fun D hD => h D (by simp [hD])))

/-- Actual source-response bytes can only add source-promised candidates.
This is derived through the wire parser, including canceled and wrong requests. -/
theorem response_available (limits : Limits (z + 1)) (invoice : Fin (z + 1) → ℕ)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase)
    (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits invoice machine state hit r).support) :
    available T candidates next.records ⊆ available T candidates state.records ∪
      payload T (received (selectedCalls limits hit) r) := by
  cases hit with
  | none =>
    simp only [response, Trace.respond, respondSource, PMF.pure_map,
      PMF.mem_support_pure_iff] at hn
    subst next
    simp [available, Trace.receipt]
  | some phase =>
    have hb := hb phase rfl
    cases phase with
    | ready world =>
      change world.config.tapes.state = none at hb
      simp only [response, Trace.respond, respondSource, phaseStep, hb, Option.isNone_none,
        ite_true, PMF.pure_map, PMF.mem_support_pure_iff] at hn
      subst next
      simp [available, Trace.receipt]
    | pending chosen =>
      cases chosen with
      | halted world => exact hb.elim
      | «local» world => exact hb.elim
      | query world operation control =>
        cases operation
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [sourceBoundary, ha] at hb
        | some batch =>
          simp only [response, Trace.respond, respondSource, phaseStep, dispatch, environment,
            serve_accepted _ _ _ _ _ ha, fixedSample, PMF.pure_map,
            PMF.mem_support_pure_iff] at hn
          subst next
          simp only [available, Trace.receipt, Memory.record, commit, List.head?_cons,
            List.filterMap_cons, id_eq,
            sourceAvailable, Finset.map_union, selectedCalls, sourceSignal, ha,
            Option.map_some, Option.bind_some, Option.elim_some]
          exact union_subset
            ((observed_available T points candidates limits _ invoice batch r).trans
              subset_union_right) subset_union_left

/-- Sum of the actual discrete invoices for an issued source call set. The
near-cover and specialist names are translated back to their wire opportunity labels. -/
@[expose] def invoiceCost (invoice : Fin (z + 1) → ℕ) (A : ResidualCover.Batch z) : ℕ :=
  ∑ i ∈ A, invoice ((finSuccEquiv z).symm i)

/-- Relabeling the preformed batch preserves its actual additive invoice. -/
theorem invoiceCost_calls (invoice : Fin (z + 1) → ℕ) (batch : ConcurrentBatch.Batch (z + 1)) :
    invoiceCost invoice (calls batch) = ∑ i ∈ active batch.slots, invoice i := by
  simp [invoiceCost, calls]

/-- The analytic source prices agree with the discrete bill when each individual
opportunity price is its actual invoice. This is a per-call convention, not a
hypothesis about total cost or its expectation. -/
theorem batchCost_invoice (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) (A : ResidualCover.Batch z) :
    batchCost P A = (invoiceCost invoice A : ℝ) := by
  classical
  rw [invoiceCost, Nat.cast_sum]
  have he (i : ResidualCover.Call z) :
      (invoice ((finSuccEquiv z).symm i) : ℝ) = i.elim P.nearCost P.specialistCost := by
    simpa using hprice ((finSuccEquiv z).symm i)
  simp only [he]
  have hsum : (∑ i : ResidualCover.Call z,
      if i ∈ A then i.elim P.nearCost P.specialistCost else 0) =
      ∑ i ∈ A, i.elim P.nearCost P.specialistCost := by
    rw [← Finset.sum_filter]
    simp
  rw [← hsum, Fintype.sum_option]
  rfl

/-- Every actual response retains its previous accrued bill and adds exactly the
issued opportunity invoices, even if the query is wrong or its reply is canceled.
No cutoff or termination condition is needed: these trajectories charge on issue. -/
theorem response_charge (limits : Limits (z + 1)) (invoice : Fin (z + 1) → ℕ)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase)
    (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits invoice machine state hit r).support) :
    Trace.accrued Trace.charge next = Trace.accrued Trace.charge state +
      (invoiceCost invoice (selectedCalls limits hit) : ℝ≥0∞) := by
  cases hit with
  | none =>
    simp only [response, Trace.respond, respondSource, PMF.pure_map,
      PMF.mem_support_pure_iff] at hn
    subst next
    simp [Trace.accrued, Trace.charge, Trace.receipt, selectedCalls, sourceSignal, invoiceCost]
  | some phase =>
    have hb := hb phase rfl
    cases phase with
    | ready world =>
      change world.config.tapes.state = none at hb
      simp only [response, Trace.respond, respondSource, phaseStep, hb, Option.isNone_none,
        ite_true, PMF.pure_map, PMF.mem_support_pure_iff] at hn
      subst next
      simp [Trace.accrued, Trace.charge, Trace.receipt, selectedCalls, sourceSignal, invoiceCost]
    | pending chosen =>
      cases chosen with
      | halted world => exact hb.elim
      | «local» world => exact hb.elim
      | query world operation control =>
        cases operation
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [sourceBoundary, ha] at hb
        | some batch =>
          simp only [response, Trace.respond, respondSource, phaseStep, dispatch, environment,
            serve_accepted _ _ _ _ _ ha, fixedSample, PMF.pure_map,
            PMF.mem_support_pure_iff] at hn
          subst next
          simp only [Trace.accrued, List.map_cons, List.sum_cons, Trace.charge,
            Option.elim_some, selectedCalls, sourceSignal, ha, Option.map_some,
            Option.bind_some, invoiceCost_calls, Trace.receipt, Memory.record, commit,
            List.head?_cons]
          rw [observe_tokens]
          exact add_comm _ _

/-- Concrete source-packet queries are checked independently for each role;
no native classifier or semantic parser contract is supplied. -/
theorem wrong_query (batch : ConcurrentBatch.Batch (z + 1)) (r : Option (Fin z))
    (i : Fin (z + 1)) (h : batch.slots i ≠ some (query T points candidates i)) :
    families T points candidates batch r i = none := by
  simp [families, h]

end Cslib.Probability.StochasticOracle.NativeResidualOracle
