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
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualOracle
open Finset NativeRetention ResidualCover NativeResidualEncoding ConcurrentBatch
open Cslib.Optimization.OneConstraint
open scoped NNReal
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
Invoices use the existing discrete wire costs. Their connection to the analytic
source token-cost parameters remains a separate obligation; no native total-cost
conclusion or price identity is asserted here. -/
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

/-- Concrete source-packet queries are checked independently for each role;
no native classifier or semantic parser contract is supplied. -/
theorem wrong_query (batch : ConcurrentBatch.Batch (z + 1)) (r : Option (Fin z))
    (i : Fin (z + 1)) (h : batch.slots i ≠ some (query T points candidates i)) :
    families T points candidates batch r i = none := by
  simp [families, h]

end Cslib.Probability.StochasticOracle.NativeResidualOracle
