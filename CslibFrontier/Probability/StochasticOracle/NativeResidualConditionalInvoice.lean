/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualInvoice
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Conditional invoices for native residual oracles

This extends the native realization of the residual construction in [Wang2027],
Theorem 6 (PDF p. 13). Unlike the fixed costs in that construction, the invoice
law here may depend on the accepted source history, the selected batch and the
newly drawn residual. The primitive mean averages over both residual and invoice
randomness, conditional on history and batch selection. In particular, costs and
responses need not be independent (as permitted by the general model on PDF p. 5).
This generalization does not establish unrestricted source-policy compilation.

## Main definitions

* `Kernel`: natural invoice vectors conditional on history, batch and residual.
* `sample`: the actual source sampler, with selection preceding both random draws.
* `HasMean`: expected charge of each selected batch, averaged over its residual.

## Main results

* `response_factor`: dispatch preserves the source residual marginal.
* `expected_score_eq_charge`: conditional batch means give exact native accrued billing.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualConditionalInvoice
open Finset NativeRetention ResidualCover ConcurrentBatch NativeBatch
open Turing NativeOpenExecution NativeInterface
open Cslib.Optimization.OneConstraint
open scoped ENNReal
variable {z n m tapes : ℕ} {Control : Type} {input : List Bool}
variable (T : Fin z → Block) (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- A natural invoice vector drawn conditional on accepted source history,
the whole selected batch (including query bytes), and its residual.
Cutoffs remain fixed by the source limits. -/
abbrev Kernel (z : ℕ) := List (Exchange (z + 1)) → ConcurrentBatch.Batch (z + 1) →
  Option (Fin z) → PMF (Fin (z + 1) → ℕ)

/-- The residual is sampled after selection; its invoice may depend on that
residual and every accepted source receipt. Rejected requests draw neither. -/
@[expose] def sample (P : Parameters z) (ν : Kernel z) : Sampler (z + 1) Unit :=
  fun state batch => (reply P (NativeResidualOracle.calls batch)).toPMF.bind fun r =>
    (ν state.history batch r).map fun invoice =>
      (NativeResidualOracle.paths T points candidates invoice batch r, ())

/-- Candidate-count transport preserves query bytes and the same conditional
invoice kernel, including every accepted history and residual. -/
theorem sample_reindex {m' : ℕ} (h : m' = m) (P : Parameters z) (ν : Kernel z) :
    sample T points ((finCongr h).trans candidates) P ν =
      sample T points candidates P ν := by
  subst m'
  rfl

/-- Primitive conditional mean for one selected batch. The residual is averaged
before imposing the mean; no mean conditional on the response is required. -/
@[expose] def HasMean (P : Parameters z) (ν : Kernel z) : Prop :=
  ∀ history batch,
    ∑' r, (reply P (NativeResidualOracle.calls batch)).toPMF r *
      ∑' invoice, ν history batch r invoice *
        (NativeResidualOracle.invoiceCost invoice (NativeResidualOracle.calls batch) : ℝ≥0∞) =
      ENNReal.ofReal (batchCost P (NativeResidualOracle.calls batch))

/-- A stronger response-wise mean condition suffices, but is not required by
`HasMean`. This is useful for kernels assembled from existing fixed-mean laws. -/
theorem hasMean_of_residual_mean {P : Parameters z} {ν : Kernel z}
    (H : ∀ history batch r,
      ∑' invoice, ν history batch r invoice *
        (NativeResidualOracle.invoiceCost invoice (NativeResidualOracle.calls batch) : ℝ≥0∞) =
        ENNReal.ofReal (batchCost P (NativeResidualOracle.calls batch))) : HasMean P ν := by
  intro history batch
  simp_rw [H]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Every old fixed invoice law is a conditional invoice kernel. -/
theorem hasMean_const {P : Parameters z} {ν : PMF (Fin (z + 1) → ℕ)}
    (hν : NativeResidualInvoice.HasMean P ν) : HasMean P (fun _ _ _ => ν) :=
  hasMean_of_residual_mean (fun _ batch _ => hν (NativeResidualOracle.calls batch))

/-- Constant kernels reproduce the original actual sampler, including raw
responses, charges, query cancellation and the source private state. -/
theorem sample_const (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) :
    sample T points candidates P (fun _ _ _ => ν) =
      NativeResidualInvoice.sample T points candidates P ν := by
  funext state batch
  simp only [sample, NativeResidualInvoice.sample, mixture, NativeResidualOracle.sample]
  exact PMF.bind_comm _ _ _

/-- Invoice law at the actual selected checkpoint. Non-query decisions use
zero invoices, with no source randomness or resource charge. -/
@[expose] def selectedInvoices (limits : Limits (z + 1)) (ν : Kernel z)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (r : Option (Fin z)) : PMF (Fin (z + 1) → ℕ) :=
  match sourceSignal limits hit with
  | some (history, some batch) => ν history batch r
  | _ => PMF.pure (fun _ => 0)

/-- Actual native response with only the residual fixed. The invoice is still
sampled from its conditional law, and all hidden native state is retained. -/
def response (limits : Limits (z + 1)) (ν : Kernel z)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (r : Option (Fin z)) : PMF (Trace.State (z + 1) tapes Unit Control input) :=
  NativeResidualInvoice.response T points candidates limits
    (selectedInvoices limits ν hit r) machine state hit r

/-- Dispatch samples the source residual after the actual batch selection,
then draws a possibly response-dependent invoice. -/
theorem response_factor (P : Parameters z) (limits : Limits (z + 1))
    (ν : Kernel z) (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input)) :
    Trace.respond limits (sample T points candidates P ν) machine state hit =
      (reply P (NativeResidualOracle.selectedCalls limits hit)).toPMF.bind
        (response T points candidates limits ν machine state hit) := by
  cases hit with
  | none => simp [Trace.respond, respondSource, NativeResidualOracle.selectedCalls,
      sourceSignal, reply, Distribution.toPMF_pure, response,
      NativeResidualInvoice.response, NativeResidualOracle.response_eq]
  | some phase =>
    cases phase with
    | ready world =>
      simp only [NativeResidualOracle.selectedCalls, sourceSignal, Option.bind_some,
        Option.elim_none, reply, Finset.notMem_empty, ite_false,
        Distribution.toPMF_pure, PMF.pure_bind]
      simp [response, selectedInvoices, sourceSignal, NativeResidualInvoice.response,
        NativeResidualOracle.response_eq, Trace.respond, respondSource, phaseStep]
    | pending chosen =>
      cases chosen with
      | halted world =>
        simp [NativeResidualOracle.selectedCalls, sourceSignal, reply,
          Distribution.toPMF_pure, response, selectedInvoices, NativeResidualInvoice.response,
          NativeResidualOracle.response_eq, Trace.respond, respondSource, phaseStep, dispatch]
      | «local» world =>
        simp [NativeResidualOracle.selectedCalls, sourceSignal, reply,
          Distribution.toPMF_pure, response, selectedInvoices, NativeResidualInvoice.response,
          NativeResidualOracle.response_eq, Trace.respond, respondSource, phaseStep, dispatch]
      | query world operation next =>
        cases operation
        cases ha : admit limits world.memory.privateState
          (world.config.channels ()).queryBuffer with
        | none =>
          simp [NativeResidualOracle.selectedCalls, sourceSignal, ha, reply,
            Distribution.toPMF_pure, response, selectedInvoices, NativeResidualInvoice.response,
            NativeResidualOracle.response_eq, Trace.respond, respondSource, phaseStep, dispatch,
            environment, serve_rejected _ _ _ _ ha]
        | some batch =>
          simp only [NativeResidualOracle.selectedCalls, sourceSignal, ha, Option.map_some,
            Option.bind_some, Option.elim_some]
          change _ = (reply P (NativeResidualOracle.calls batch)).toPMF.bind
            (fun r => response T points candidates limits ν machine state
              (some (.pending (.query world () next))) r)
          simp only [response, selectedInvoices, sourceSignal, ha, Option.map_some,
            NativeResidualInvoice.response, NativeResidualOracle.response_eq,
            Trace.respond, respondSource, phaseStep, dispatch, environment,
            serve_accepted _ _ _ _ _ ha, sample,
            Function.comp_def, PMF.map, PMF.bind_bind, PMF.pure_bind]

/-- A positive residual branch is an actual response branch of the same oracle. -/
theorem response_support (P : Parameters z) (limits : Limits (z + 1))
    (ν : Kernel z) (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (r : Option (Fin z))
    (hr : r ∈ (reply P (NativeResidualOracle.selectedCalls limits hit)).toPMF.support)
    (hn : next ∈ (response T points candidates limits ν machine state hit r).support) :
    next ∈ (Trace.respond limits (sample T points candidates P ν) machine state hit).support := by
  rw [response_factor]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨r, hr, hn⟩

/-- Response-dependent fees preserve the actual selected-call receipt. -/
theorem response_record (limits : Limits (z + 1)) (ν : Kernel z)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits ν machine state hit r).support) :
    ∃ record, next.records = record :: state.records ∧
      NativeResidualOracle.selectedCalls limits hit =
        record.elim ∅ (fun receipt => NativeResidualOracle.calls receipt.batch) :=
  NativeResidualInvoice.response_record T points candidates limits
    (selectedInvoices limits ν hit r) machine state next hit hb r hn

/-- Fees cannot introduce an unproposed source candidate. -/
theorem response_available (limits : Limits (z + 1)) (ν : Kernel z)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits ν machine state hit r).support) :
    NativeResidualOracle.available T candidates next.records ⊆
      NativeResidualOracle.available T candidates state.records ∪
        payload T (received (NativeResidualOracle.selectedCalls limits hit) r) :=
  NativeResidualInvoice.response_available T points candidates limits
    (selectedInvoices limits ν hit r) machine state next hit hb r hn

/-- The declared-price score is determined by the selected batch, irrespective
of invoice correlation with the residual or accepted source history. -/
theorem response_score (P : Parameters z) (limits : Limits (z + 1)) (ν : Kernel z)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits ν machine state hit r).support) :
    Trace.accrued (NativeResidualInvoice.score P) next =
      Trace.accrued (NativeResidualInvoice.score P) state +
        ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) :=
  NativeResidualInvoice.response_score T points candidates P limits
    (selectedInvoices limits ν hit r) machine state next hit hb r hn

/-- The primitive conditional mean holds at each selected native checkpoint,
including zero-call halt and divergence decisions. -/
theorem selected_mean (P : Parameters z) (limits : Limits (z + 1))
    (ν : Kernel z) (hν : HasMean P ν)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input)) :
    (∑' r, (reply P (NativeResidualOracle.selectedCalls limits hit)).toPMF r *
      ∑' invoice, selectedInvoices limits ν hit r invoice *
        (NativeResidualOracle.invoiceCost invoice
          (NativeResidualOracle.selectedCalls limits hit) : ℝ≥0∞)) =
      ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) := by
  cases hs : sourceSignal limits hit with
  | none =>
    simp [selectedInvoices, NativeResidualOracle.selectedCalls, hs,
      NativeResidualOracle.invoiceCost, batchCost]
  | some signal =>
    obtain ⟨history, batch⟩ := signal
    cases batch with
    | none =>
      simp [selectedInvoices, NativeResidualOracle.selectedCalls, hs,
        NativeResidualOracle.invoiceCost, batchCost]
    | some batch =>
      simpa only [selectedInvoices, NativeResidualOracle.selectedCalls, hs,
        Option.bind_some, Option.elim_some] using hν history batch

/-- The actual source response has the declared batch mean, even when the
invoice depends on its residual. The mean is imposed before the response is known. -/
theorem response_mean_charge (P : Parameters z) (limits : Limits (z + 1))
    (ν : Kernel z) (hν : HasMean P ν) (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) :
    Quantitative.mean (Trace.respond limits (sample T points candidates P ν)
      machine state hit) (Trace.accrued Trace.charge) =
      Trace.accrued Trace.charge state +
        ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) := by
  unfold Quantitative.mean
  rw [response_factor, PMF.tsum_bind_mul]
  simp_rw [show ∀ r, (∑' next, response T points candidates limits ν machine state hit r next *
      Trace.accrued Trace.charge next) = Trace.accrued Trace.charge state +
        ∑' invoice, selectedInvoices limits ν hit r invoice *
          (NativeResidualOracle.invoiceCost invoice
            (NativeResidualOracle.selectedCalls limits hit) : ℝ≥0∞) from
    fun r => NativeResidualInvoice.response_mean_charge_eq T points candidates limits
      (selectedInvoices limits ν hit r) machine state hit hb r]
  simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [selected_mean P limits ν hν hit]

/-- Authentication fixes the declared-price increment independently of the
response-dependent invoice law. -/
theorem response_mean_score (P : Parameters z) (limits : Limits (z + 1))
    (ν : Kernel z) (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) :
    Quantitative.mean (Trace.respond limits (sample T points candidates P ν)
      machine state hit) (Trace.accrued (NativeResidualInvoice.score P)) =
      Trace.accrued (NativeResidualInvoice.score P) state +
        ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) := by
  unfold Quantitative.mean
  rw [response_factor, PMF.tsum_bind_mul]
  have H (r : Option (Fin z)) :
      (∑' next, response T points candidates limits ν machine state hit r next *
        Trace.accrued (NativeResidualInvoice.score P) next) =
        Trace.accrued (NativeResidualInvoice.score P) state +
          ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) :=
    NativeResidualInvoice.response_mean_score T points candidates P limits
      (selectedInvoices limits ν hit r) machine state hit hb r
  simp_rw [H]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Declared-price accounting equals actual accrued token billing at every
finite native epoch horizon. Costs may depend jointly on all earlier source
receipts, the selected batch and its response. No stopping, integrability or
bounded-total-bill hypothesis is needed; earlier charges survive silent divergence. -/
theorem expected_score_eq_charge (P : Parameters z) (limits : Limits (z + 1))
    (ν : Kernel z) (hν : HasMean P ν) (machine : MultiTapePTM tapes Bool Control Unit)
    (turns : ℕ) (world : World tapes Control Unit (ServerState (z + 1) Unit) input) :
    Quantitative.expected limits (sample T points candidates P ν) machine
      (NativeResidualInvoice.score P) turns world =
    Quantitative.expected limits (sample T points candidates P ν) machine
      Trace.charge turns world := by
  exact Quantitative.expected_eq_of_response limits (sample T points candidates P ν) machine
    (NativeResidualInvoice.score P) Trace.charge
    (fun hit => ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)))
    (fun state hit hb => response_mean_score T points candidates P limits ν machine state hit hb)
    (fun state hit hb => response_mean_charge T points candidates P limits ν hν
      machine state hit hb) turns world

end Cslib.Probability.StochasticOracle.NativeResidualConditionalInvoice
