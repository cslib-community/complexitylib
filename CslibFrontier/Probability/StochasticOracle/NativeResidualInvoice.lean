/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualOracle
public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Mixture
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic

/-!
# Fresh invoice kernels for actual residual source epochs

[Wang2027], model p. 5 and Theorem 6 p. 13. Natural invoices are drawn after
batch selection. Their law may have arbitrary real masses and correlated
coordinates. The invoice law is fixed and drawn independently of the residual
index `J` and the preceding history. A point mass recovers the constant-invoice source. Conditional
residual factorization and raw source provenance are derived from dispatch.

## Main definitions

* `sample`, `response`: the actual fresh-invoice source and fixed-residual response.
* `HasMean`, `score`: primitive conditional batch means and their declared-price ledger.

## Main results

* `response_factor`, `response_support`: actual selected-before-response epoch laws.
* `response_record`, `response_available`: authenticated receipts and raw provenance.
* `expected_score_eq_charge`: exact actual expected ledger accounting at every horizon.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualInvoice
open Finset NativeRetention ResidualCover ConcurrentBatch NativeBatch
open Turing NativeOpenExecution NativeInterface
open scoped ENNReal
variable {z n m tapes : ℕ} {Control : Type} {input : List Bool}
variable (T : Fin z → Block) (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- One consistent source, sampling a fresh natural invoice vector at each batch. -/
@[expose] def sample (P : Parameters z) (invoices : PMF (Fin (z + 1) → ℕ)) :
    Sampler (z + 1) Unit := mixture invoices (NativeResidualOracle.sample T points candidates P)

/-- Candidate-count transport preserves the same source bytes and invoice law. -/
theorem sample_reindex {m' : ℕ} (h : m' = m) (P : Parameters z)
    (invoices : PMF (Fin (z + 1) → ℕ)) :
    sample T points ((finCongr h).trans candidates) P invoices =
      sample T points candidates P invoices := by
  subst m'
  rfl

/-- Fix the current source residual, then draw fresh invoices for this response. -/
@[expose] def response (limits : Limits (z + 1)) (invoices : PMF (Fin (z + 1) → ℕ))
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (r : Option (Fin z)) : PMF (Trace.State (z + 1) tapes Unit Control input) :=
  invoices.bind fun invoice =>
    NativeResidualOracle.response T points candidates limits invoice machine state hit r

/-- Native dispatch is linear in a fresh batch mixture, including halt/divergence. -/
theorem respond_mixture (limits : Limits (z + 1)) {I : Type} (μ : PMF I)
    (samples : I → Sampler (z + 1) Unit) (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input)) :
    Trace.respond limits (mixture μ samples) machine state hit =
      μ.bind fun i => Trace.respond limits (samples i) machine state hit := by
  cases hit with
  | none => simp [Trace.respond, respondSource]
  | some phase =>
    cases phase with
    | ready world =>
      by_cases hh : world.config.tapes.state = none
      · simp [Trace.respond, respondSource, phaseStep, hh]
      · simp [Trace.respond, respondSource, phaseStep, hh, prepare]
    | pending chosen =>
      cases chosen with
      | halted world => simp [Trace.respond, respondSource, phaseStep, dispatch]
      | «local» world => simp [Trace.respond, respondSource, phaseStep, dispatch]
      | query world op next =>
        cases op
        simp only [Trace.respond, respondSource, phaseStep, dispatch,
          environment_mixture, PMF.map_bind]

/-- Fresh invoices are drawn after the native call set and source residual law. -/
theorem response_factor (P : Parameters z) (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ)) (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input)) :
    Trace.respond limits (sample T points candidates P invoices) machine state hit =
      (reply P (NativeResidualOracle.selectedCalls limits hit)).toPMF.bind
        (response T points candidates limits invoices machine state hit) := by
  rw [sample, respond_mixture]
  simp_rw [NativeResidualOracle.response_factor]
  exact PMF.bind_comm _ _ _

/-- Positive residual branches are supported branches of the same actual oracle. -/
theorem response_support (P : Parameters z) (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ)) (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (r : Option (Fin z))
    (hr : r ∈ (reply P (NativeResidualOracle.selectedCalls limits hit)).toPMF.support)
    (hn : next ∈ (response T points candidates limits invoices machine state hit r).support) :
    next ∈ (Trace.respond limits (sample T points candidates P invoices)
      machine state hit).support := by
  rw [response_factor]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨r, hr, hn⟩

/-- Fresh invoice draws preserve the exact selected-call receipt. -/
theorem response_record (limits : Limits (z + 1)) (invoices : PMF (Fin (z + 1) → ℕ))
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits invoices machine state hit r).support) :
    ∃ record, next.records = record :: state.records ∧
      NativeResidualOracle.selectedCalls limits hit =
        record.elim ∅ (fun receipt => NativeResidualOracle.calls receipt.batch) := by
  obtain ⟨invoice, _, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
  exact NativeResidualOracle.response_record T points candidates limits invoice machine
    state next hit hb r hn

/-- Fresh invoices do not add any unproposed source candidate. -/
theorem response_available (limits : Limits (z + 1)) (invoices : PMF (Fin (z + 1) → ℕ))
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits invoices machine state hit r).support) :
    NativeResidualOracle.available T candidates next.records ⊆
      NativeResidualOracle.available T candidates state.records ∪
        payload T (received (NativeResidualOracle.selectedCalls limits hit) r) := by
  obtain ⟨invoice, _, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
  exact NativeResidualOracle.response_available T points candidates limits invoice machine
    state next hit hb r hn

/-- Primitive source expected invoice for every batch chosen before this draw.
This concerns one response, not policy cost, stopping, success or integrability. -/
@[expose] def HasMean (P : Parameters z) (invoices : PMF (Fin (z + 1) → ℕ)) : Prop :=
  ∀ A : ResidualCover.Batch z, ∑' f, invoices f *
    (NativeResidualOracle.invoiceCost f A : ℝ≥0∞) = ENNReal.ofReal (batchCost P A)

/-- Point-mass invoice laws recover the original same-oracle native source. -/
theorem sample_pure (P : Parameters z) (invoice : Fin (z + 1) → ℕ) :
    sample T points candidates P (PMF.pure invoice) =
      NativeResidualOracle.sample T points candidates P invoice := by
  funext state batch
  simp [sample, ConcurrentBatch.mixture]

/-- The old natural-price convention is an instance of the primitive mean law. -/
theorem hasMean_pure (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    HasMean P (PMF.pure invoice) := by
  intro A
  rw [NativeResidualOracle.batchCost_invoice P invoice hprice]
  simp [ENNReal.ofReal_natCast]

/-- Analytic price of the actual selected batch, including zero-call decisions. -/
@[expose] def score (P : Parameters z) (record : Trace.Record (z + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal (batchCost P (record.elim ∅ (fun r => NativeResidualOracle.calls r.batch)))

/-- Empty decisions have zero declared price. -/
theorem score_none (P : Parameters z) : score P none = 0 := by
  simp [score, batchCost]

/-- Actual record authentication identifies the declared price increment. -/
theorem response_score (P : Parameters z) (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ)) (machine : MultiTapePTM tapes Bool Control Unit)
    (state next : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z))
    (hn : next ∈ (response T points candidates limits invoices machine state hit r).support) :
    Trace.accrued (score P) next = Trace.accrued (score P) state +
      ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) := by
  obtain ⟨record, he, ha⟩ := response_record T points candidates limits invoices machine
    state next hit hb r hn
  simp only [Trace.accrued, he, List.map_cons, List.sum_cons, score]
  rw [← ha]
  exact add_comm _ _

/-- Expected actual billing for an arbitrary fresh invoice law, before imposing
any price means. This retains the prefix even when local computation diverges. -/
theorem response_mean_charge_eq (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ))
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z)) :
    Quantitative.mean (response T points candidates limits invoices machine state hit r)
      (Trace.accrued Trace.charge) = Trace.accrued Trace.charge state +
        ∑' invoice, invoices invoice * (NativeResidualOracle.invoiceCost invoice
          (NativeResidualOracle.selectedCalls limits hit) : ℝ≥0∞) := by
  unfold Quantitative.mean response
  rw [PMF.tsum_bind_mul]
  have hf (f : Fin (z + 1) → ℕ) :
      (∑' next, NativeResidualOracle.response T points candidates limits f machine state hit r
        next * Trace.accrued Trace.charge next) = Trace.accrued Trace.charge state +
          (NativeResidualOracle.invoiceCost f
            (NativeResidualOracle.selectedCalls limits hit) : ℝ≥0∞) := by
    rw [PMF.tsum_mul_congr_support _ (fun next hn =>
      NativeResidualOracle.response_charge T points candidates limits f machine
        state next hit hb r hn)]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  simp_rw [hf]
  simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The actual response's expected accrued bill is its previous bill plus the
primitive source batch mean. Silent divergence retains its accrued prefix. -/
theorem response_mean_charge (P : Parameters z) (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ)) (hmean : HasMean P invoices)
    (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z)) :
    Quantitative.mean (response T points candidates limits invoices machine state hit r)
      (Trace.accrued Trace.charge) = Trace.accrued Trace.charge state +
        ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) := by
  rw [response_mean_charge_eq T points candidates limits invoices machine state hit hb r, hmean]

/-- The declared-price ledger has the same conditional increment. -/
theorem response_mean_score (P : Parameters z) (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ)) (machine : MultiTapePTM tapes Bool Control Unit)
    (state : Trace.State (z + 1) tapes Unit Control input)
    (hit : Option (Phase tapes Control Unit (ServerState (z + 1) Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) (r : Option (Fin z)) :
    Quantitative.mean (response T points candidates limits invoices machine state hit r)
      (Trace.accrued (score P)) = Trace.accrued (score P) state +
        ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) := by
  unfold Quantitative.mean
  rw [PMF.tsum_mul_congr_support _ (fun next hn =>
    response_score T points candidates P limits invoices machine state next hit hb r hn)]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

private theorem response_mean (P : Parameters z) (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ)) (machine : MultiTapePTM tapes Bool Control Unit)
    (resource : Trace.Record (z + 1) → ℝ≥0∞)
    (H : ∀ (state : Trace.State (z + 1) tapes Unit Control input) hit,
      (∀ phase, hit = some phase → sourceBoundary limits phase) →
      ∀ r, Quantitative.mean
        (response T points candidates limits invoices machine state hit r)
        (Trace.accrued resource) = Trace.accrued resource state +
          ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)))
    (state : Trace.State (z + 1) tapes Unit Control input) hit
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase) :
    Quantitative.mean (Trace.respond limits (sample T points candidates P invoices)
      machine state hit) (Trace.accrued resource) = Trace.accrued resource state +
        ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) := by
  unfold Quantitative.mean
  rw [response_factor, PMF.tsum_bind_mul]
  have hres (r : Option (Fin z)) :
      (∑' next, response T points candidates limits invoices machine state hit r next *
        Trace.accrued resource next) = Trace.accrued resource state +
          ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)) :=
    H state hit hb r
  simp_rw [hres]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Expected analytic batch-price accounting equals actual accrued token billing
at every finite native epoch horizon. Fresh fees are averaged only after selection;
all policies, hidden metadata, silent divergence and accrued prefixes are retained.
No integrability or bounded-total-bill hypothesis is required. -/
theorem expected_score_eq_charge (P : Parameters z) (limits : Limits (z + 1))
    (invoices : PMF (Fin (z + 1) → ℕ)) (hmean : HasMean P invoices)
    (machine : MultiTapePTM tapes Bool Control Unit) (turns : ℕ)
    (world : World tapes Control Unit (ServerState (z + 1) Unit) input) :
    Quantitative.expected limits (sample T points candidates P invoices) machine
      (score P) turns world =
    Quantitative.expected limits (sample T points candidates P invoices) machine
      Trace.charge turns world := by
  exact Quantitative.expected_eq_of_response limits (sample T points candidates P invoices)
    machine (score P) Trace.charge
    (fun hit => ENNReal.ofReal (batchCost P (NativeResidualOracle.selectedCalls limits hit)))
    (response_mean T points candidates P limits invoices machine (score P)
      (fun state hit hb r => response_mean_score T points candidates P limits invoices
        machine state hit hb r))
    (response_mean T points candidates P limits invoices machine Trace.charge
      (fun state hit hb r => response_mean_charge T points candidates P limits invoices hmean
        machine state hit hb r)) turns world

end Cslib.Probability.StochasticOracle.NativeResidualInvoice
