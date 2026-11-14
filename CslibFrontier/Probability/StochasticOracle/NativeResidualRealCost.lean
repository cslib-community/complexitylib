/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FixedMeanInvoice
public import CslibFrontier.Probability.StochasticOracle.NativeResidualInvoice
public import CslibFrontier.Probability.StochasticOracle.NativeResidualAll
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOutputObservation
public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Mixture
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.FeedbackMixture
import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution.OutputTransfer
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Fixed real expected prices in the actual residual oracle

[Wang2027], model PDF p. 5 and Theorem 6 p. 13. Analytic costs may be real;
algorithmic numerical inputs are binary rationals. Fixed real means are realized
by natural token reports drawn freshly after each batch selection, from an arbitrary
invoice PMF `ν` with the source batch means (`NativeResidualInvoice.HasMean`).
Coordinates may be correlated; `FixedMeanInvoice.law` (`hasMean`) is one instance.
The conditional-kernel results also allow the law to depend on history, selected
batch and residual; only the actual selected-batch mean is required.
The invoice vector is drawn independently of the residual index `J` and the
preceding history. The compiled program reads ordinary report bytes, never a real-number encoding.

## Main definitions

* `prices`: the primitive source means of the opportunities.

## Main results

* `expected_finset`, `hasMean_bind`: source means on every opportunity set, and mixtures.
* `batch_expected_cost`: the actual selected-batch invoice has the source mean.
* `native_all_expected_cost_conditional`, `native_all_cost_mem_conditional`:
  attained one-batch bills for history- and response-dependent kernels.
* `native_all_mixture`, `native_all_resources`: actual all-specialist native execution.
* `native_all_expected_cost`, `native_all_certified`, `native_all_cost_mem`: attained
  real expected bill, certified tape output and membership in the native cost class.

Adaptive attainment is downstream in `NativeResidualRealAdaptive`; universal
real-price optima are assembled in `NativeResidualRealMinima`. In
particular, a fresh per-batch mixture is not a once-for-all mixture of an adaptive policy.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualRealCost
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention ConcurrentBatch ResidualCover
open Finset
open Cslib.Optimization.OneConstraint
open scoped NNReal ENNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- The source's fixed positive per-opportunity expected costs, with no integrality restriction. -/
@[expose] def prices (P : Parameters z) : Fin (z + 1) → ℝ≥0 :=
  Fin.cases ⟨P.nearCost, P.near_pos.le⟩ (fun j => ⟨P.specialistCost j, (P.specialist_pos j).le⟩)

/-- The source batch price is the sum of the primitive prices of its opportunities. -/
theorem batchCost_eq_prices (P : Parameters z) (A : ResidualCover.Batch z) :
    batchCost P A = ∑ i ∈ A.map (finSuccEquiv z).symm.toEmbedding, (prices P i : ℝ) := by
  rw [batchCost_eq_sum, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | none => rfl
  | some j => rfl

theorem invoiceCost_eq (f : Fin (z + 1) → ℕ) (A : ResidualCover.Batch z) :
    NativeResidualOracle.invoiceCost f A = ∑ i ∈ A.map (finSuccEquiv z).symm.toEmbedding, f i := by
  simp [NativeResidualOracle.invoiceCost]

/-- The constructed natural invoices have the source's arbitrary real batch means. -/
theorem hasMean (P : Parameters z) :
    NativeResidualInvoice.HasMean P (FixedMeanInvoice.law (prices P)) := by
  intro A
  simp_rw [invoiceCost_eq, Nat.cast_sum]
  rw [FixedMeanInvoice.expected_batch, batchCost_eq_prices]

/-- Every invoice law with the source batch means has the source mean on every set
of opportunities; coordinates may be arbitrarily correlated. -/
theorem expected_finset {P : Parameters z} {ν : PMF (Fin (z + 1) → ℕ)}
    (hν : NativeResidualInvoice.HasMean P ν) (B : Finset (Fin (z + 1))) :
    (∑' f, ν f * (∑ i ∈ B, (f i : ℝ≥0∞))) = ENNReal.ofReal (∑ i ∈ B, (prices P i : ℝ)) := by
  have hB : (B.map (finSuccEquiv z).toEmbedding).map (finSuccEquiv z).symm.toEmbedding = B := by
    ext i; simp
  have h := hν (B.map (finSuccEquiv z).toEmbedding)
  simp_rw [invoiceCost_eq, hB, Nat.cast_sum] at h
  rw [h, batchCost_eq_prices, hB]

/-- Mixtures of invoice laws with the source batch means keep those means, so
correlated, heavy-tailed or partly deterministic fee laws are all admissible. -/
theorem hasMean_bind {P : Parameters z} {ι : Type*} (μ : PMF ι)
    (ν : ι → PMF (Fin (z + 1) → ℕ)) (h : ∀ i, NativeResidualInvoice.HasMean P (ν i)) :
    NativeResidualInvoice.HasMean P (μ.bind ν) := by
  intro A
  rw [PMF.tsum_bind_mul]
  simp_rw [h _ A]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The actual query-conditioned report kernel has the stated fixed expected
bill, for every server history, cutoff and remaining deadline, including cancellation.
No source mean or desired total-cost conclusion is supplied as a hypothesis. -/
theorem batch_expected_cost (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (limits : Limits (z + 1))
    (s : ServerState (z + 1) Unit) (b : ConcurrentBatch.Batch (z + 1)) (remaining : ℝ≥0) :
    (∑' result, NativeResidualInvoice.sample T points candidates P ν s b result *
      ((observe limits remaining b result.1).tokens : ℝ≥0∞)) =
      ENNReal.ofReal (∑ i ∈ active b.slots, (prices P i : ℝ)) := by
  rw [NativeResidualInvoice.sample, mixture, PMF.tsum_bind_mul]
  have hfixed (invoice : Fin (z + 1) → ℕ) :
      (∑' result, NativeResidualOracle.sample T points candidates P invoice s b result *
        ((observe limits remaining b result.1).tokens : ℝ≥0∞)) =
        ∑ i ∈ active b.slots, (invoice i : ℝ≥0∞) := by
    rw [NativeResidualOracle.sample, PMF.tsum_map_mul]
    simp only [observe_tokens, NativeResidualOracle.paths, NativeResidualReplies.path]
    simp only [Nat.cast_sum]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  simp_rw [hfixed]
  exact expected_finset hν (active b.slots)

private theorem raw_law {Private : Type} (env : Environment Unit Private)
    (data : GuardedStartup.Input) (memory : Memory Unit Private) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program env
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding data), memory⟩).map
      (Option.map fun w => (w.config.tapes.output, w.memory)) =
    (Feedback.run env 1 (NativeResidualRouting.initial false data)
      (fun _ => ⟨[], [], 0⟩) memory NativeResidualRouting.request).map fun outcome =>
        some (RuntimeControl.result outcome.state, outcome.memory) := by
  have h := congrArg (PMF.map (Option.map fun o : NativeReplyContext.Observation Private =>
    (o.output, o.memory))) (NativeResidualRouting.controller_law false Private env data memory)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map,
    NativeReplyContext.observe, Bool.false_eq_true, ite_false, Option.map_some] using h

/-- The one-query native program preserves a fresh sampler mixture. This is
proved through its actual feedback law, not assumed for an arbitrary policy. -/
theorem native_all_mixture {I : Type} (μ : PMF I) (samples : I → Sampler (z + 1) Unit)
    (limits : Limits (z + 1)) (data : GuardedStartup.Input)
    (memory : Memory Unit (ServerState (z + 1) Unit)) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
      (environment limits (mixture μ samples))
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding data), memory⟩).map
        (Option.map fun w => (w.config.tapes.output, w.memory)) =
      μ.bind fun i => (NativeUnboundedExecution.terminal
        (NativeResidualRouting.controller false).program (environment limits (samples i))
        ⟨(NativeResidualRouting.controller false).program.initialConfig
          (GuardedStartup.encoding data), memory⟩).map
          (Option.map fun w => (w.config.tapes.output, w.memory)) := by
  simp_rw [raw_law]
  have he : environment limits (mixture μ samples) =
      fun q memory => μ.bind fun i => environment limits (samples i) q memory := by
    funext q memory
    exact environment_mixture limits μ samples q memory
  rw [he, Feedback.run_one_mixture, PMF.map_bind]

/-- The one-batch strategy uses the conditional invoice law at exactly its
initial all-specialist query. No other history or residual is sampled. -/
theorem native_all_mixture_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
      (environment (NativeResidualAll.config budget)
        (NativeResidualConditionalInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩).map
        (Option.map fun w => (w.config.tapes.output, w.memory)) =
    (ν [] (NativeResidualAll.batch T points candidates (by omega)) none).bind fun invoice =>
      (NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
        (environment (NativeResidualAll.config budget)
          (NativeResidualOracle.sample T points candidates P invoice))
        ⟨(NativeResidualRouting.controller false).program.initialConfig
          (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
          NativeResidualAttainment.initialMemory⟩).map
          (Option.map fun w => (w.config.tapes.output, w.memory)) := by
  rw [NativeResidualAll.native_law_conditional T points candidates P ν hz budget hb]
  simp_rw [NativeResidualAll.native_law T points candidates P _ hz budget hb]
  rfl

/-- Actual one-batch resource law under conditional invoice kernels. -/
theorem native_all_resources_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
      (environment (NativeResidualAll.config budget)
        (NativeResidualConditionalInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩).map
      (Option.map fun w => (tokenBill w.memory.events, elapsed w.memory.events)) =
    (ν [] (NativeResidualAll.batch T points candidates (by omega)) none).map fun invoice =>
      some (((∑ j : Fin z, invoice j.succ : ℕ) : ℝ≥0), (1 : ℝ≥0)) := by
  have h := congrArg (PMF.map (Option.map fun p : Word × Memory Unit (ServerState (z + 1) Unit) =>
      (tokenBill p.2.events, elapsed p.2.events)))
    (native_all_mixture_conditional T points candidates P ν hz budget hb)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_map] at h
  refine h.trans ?_
  simp_rw [NativeResidualAll.native_resources T points candidates P _ hz budget hb]
  rfl

/-- Actual joint accrued bill and oracle duration for the unchanged compiled
all-specialist program. Invoice randomness is not hidden by a supplied bill bound. -/
theorem native_all_resources (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
      (environment (NativeResidualAll.config budget)
        (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩).map
      (Option.map fun w => (tokenBill w.memory.events, elapsed w.memory.events)) =
    ν.map fun invoice =>
      some (((∑ j : Fin z, invoice j.succ : ℕ) : ℝ≥0), (1 : ℝ≥0)) := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_all_resources_conditional T points candidates P (fun _ _ _ => ν) hz budget hb

/-- Real expected all-specialist cost in the actual accrued native trace.
Almost-sure termination and finite expectation are conclusions of the construction,
not hypotheses about total cost. The per-call invoices remain natural numbers. -/
theorem native_all_expected_cost_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget) :
    NativeBatch.Quantitative.expected (NativeResidualAll.config budget)
      (NativeResidualConditionalInvoice.sample T points candidates P ν)
        (NativeResidualRouting.controller false).program
      NativeBatch.Trace.charge (budget + 1)
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩ =
      ENNReal.ofReal (∑ j, P.specialistCost j) := by
  let program := (NativeResidualRouting.controller false).program
  let world := (⟨program.initialConfig
    (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
    NativeResidualAttainment.initialMemory⟩ :
      World (NativeResidualRouting.controller false).tapes
        (NativeResidualRouting.controller false).Controls Unit (ServerState (z + 1) Unit)
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)))
  let μ := NativeUnboundedExecution.terminal program
    (environment (NativeResidualAll.config budget)
      (NativeResidualConditionalInvoice.sample T points candidates P ν)) world
  have hlaw := native_all_resources_conditional T points candidates P ν hz budget hb
  have hterm : μ none = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hn
    have hm : none ∈ (μ.map (Option.map fun w =>
        (tokenBill w.memory.events, elapsed w.memory.events))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
    rw [hlaw] at hm
    obtain ⟨invoice, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    cases he
  have he := NativeBatch.Quantitative.expected_charge_eq_terminal (NativeResidualAll.config budget)
    (NativeResidualConditionalInvoice.sample T points candidates P ν) program world
    (NativeBatch.initial_invariant (NativeResidualAll.config budget) ()) rfl hterm
  change NativeBatch.Quantitative.expected _ _ _ NativeBatch.Trace.charge
    ((NativeResidualAll.config (z := z) budget).turns + 1) world = _
  rw [he]
  have hm := PMF.tsum_map_mul μ (Option.map fun w =>
    (tokenBill w.memory.events, elapsed w.memory.events))
    (fun result => result.elim 0 (fun p => (p.1 : ℝ≥0∞)))
  simp only [Option.elim_map, Function.comp_def] at hm
  change (∑' result, μ result * result.elim 0
    (fun w => (tokenBill w.memory.events : ℝ≥0∞))) = _
  rw [← hm, hlaw, PMF.tsum_map_mul]
  have hmean := hν [] (NativeResidualAll.batch T points candidates (by omega))
  have hinvoice (f : Fin (z + 1) → ℕ) :
      NativeResidualOracle.invoiceCost f (specialistBatch : ResidualCover.Batch z) =
        ∑ j : Fin z, f j.succ := by
    rw [← NativeResidualAll.calls_batch T points candidates (by omega),
      NativeResidualOracle.invoiceCost_calls, NativeResidualAll.active_batch]
    simp [Fin.univ_succ]
  rw [NativeResidualAll.calls_batch] at hmean
  simp_rw [hinvoice] at hmean
  simpa [reply, specialistBatch, Distribution.toPMF_pure, Nat.cast_sum, batchCost] using hmean

/-- Real expected all-specialist cost in the actual accrued native trace.
Almost-sure termination and finite expectation are conclusions of the construction,
not hypotheses about total cost. The per-call invoices remain natural numbers. -/
theorem native_all_expected_cost (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget) :
    NativeBatch.Quantitative.expected (NativeResidualAll.config budget)
      (NativeResidualInvoice.sample T points candidates P ν)
        (NativeResidualRouting.controller false).program
      NativeBatch.Trace.charge (budget + 1)
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩ =
      ENNReal.ofReal (∑ j, P.specialistCost j) := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_all_expected_cost_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz budget hb

/-- Certified actual tape success is preserved by the real-mean invoice kernel,
since the same one-batch program certifies every realized natural report. -/
theorem native_all_certified_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget) :
    ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
      (environment (NativeResidualAll.config budget)
        (NativeResidualConditionalInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩).map
      (BatchOutput.certified (NativeResidualAll.config budget)
        (NativeResidualAttainment.input T points candidates).startup.system
        (NativeResidualAttainment.valid T points candidates (by omega)))) true = 1 := by
  rw [BatchOutput.terminal_certified]
  rw [native_all_mixture_conditional T points candidates P ν hz budget hb, PMF.map_bind]
  simp_rw [← BatchOutput.terminal_certified]
  simp only [PMF.bind_apply,
    NativeResidualAll.native_certified T points candidates P _ hz budget hb,
    mul_one, PMF.tsum_coe]

/-- Every finite successful output of the same compiled code has source provenance
under the fresh real-mean invoice kernel. This is derived from actual terminal
support and the fixed-invoice executions, not imposed as an admission contract. -/
theorem native_all_selectionOnly_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget)
    (accept : Finset
      (Fin (NativeResidualAttainment.input T points candidates).startup.system.rows.length) →
        Bool) :
    NativeUnboundedExecution.SelectionOnly (NativeResidualRouting.controller false).program
      (environment (NativeResidualAll.config budget)
        (NativeResidualConditionalInvoice.sample T points candidates P ν))
      (NativeBatch.candidateParser (n := z + 1)
        (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      (decodeFamily (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      accept ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩ := by
  apply NativeUnboundedExecution.selectionOnly_of_output_memory_bind _ _
    (ν [] (NativeResidualAll.batch T points candidates (by omega)) none)
    (NativeResidualRouting.controller false).program
    (fun f => environment (NativeResidualAll.config budget)
      (NativeResidualOracle.sample T points candidates P f)) _ _ accept _
    (fun _ => ⟨(NativeResidualRouting.controller false).program.initialConfig
      (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
      NativeResidualAttainment.initialMemory⟩)
  · exact native_all_mixture_conditional T points candidates P ν hz budget hb
  · intro f _
    exact NativeResidualAll.native_selectionOnly T points candidates P f hz budget hb accept

/-- The real all-specialist expected cost is attained in the original common-oracle
native class for any positive source turn budget. -/
theorem native_all_cost_mem_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z)
    (budget : ℕ)
      (hb : 0 < budget) :
    ENNReal.ofReal (∑ j, P.specialistCost j) ∈
      BatchOptimum.costs (NativeResidualAll.config budget)
        (NativeResidualConditionalInvoice.sample T points candidates P ν)
        (NativeResidualAttainment.input T points candidates) ()
        (NativeResidualAttainment.valid T points candidates (by omega)) 1 := by
  exact ⟨(NativeResidualRouting.controller false).tapes,
    (NativeResidualRouting.controller false).Controls,
    (NativeResidualRouting.controller false).finite,
    (NativeResidualRouting.controller false).program,
    native_all_selectionOnly_conditional T points candidates P ν hz budget hb _,
    (native_all_certified_conditional T points candidates P ν hz budget hb).ge,
    (native_all_expected_cost_conditional T points candidates P ν hν hz budget hb).symm⟩

/-- Fixed invoice kernels specialize the conditional native result. -/
theorem native_all_certified (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget) :
    ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
      (environment (NativeResidualAll.config budget)
        (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩).map
      (BatchOutput.certified (NativeResidualAll.config budget)
        (NativeResidualAttainment.input T points candidates).startup.system
        (NativeResidualAttainment.valid T points candidates (by omega)))) true = 1 := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_all_certified_conditional T points candidates P (fun _ _ _ => ν) hz budget hb

/-- Fixed invoice kernels specialize the conditional native result. -/
theorem native_all_selectionOnly (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z)
    (budget : ℕ) (hb : 0 < budget)
    (accept : Finset
      (Fin (NativeResidualAttainment.input T points candidates).startup.system.rows.length) →
        Bool) :
    NativeUnboundedExecution.SelectionOnly (NativeResidualRouting.controller false).program
      (environment (NativeResidualAll.config budget)
        (NativeResidualInvoice.sample T points candidates P ν))
      (NativeBatch.candidateParser (n := z + 1)
        (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      (decodeFamily (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      accept ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩ := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_all_selectionOnly_conditional T points candidates P (fun _ _ _ => ν) hz budget hb accept

/-- Fixed invoice kernels specialize the conditional native result. -/
theorem native_all_cost_mem (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (budget : ℕ)
      (hb : 0 < budget) :
    ENNReal.ofReal (∑ j, P.specialistCost j) ∈
      BatchOptimum.costs (NativeResidualAll.config budget)
        (NativeResidualInvoice.sample T points candidates P ν)
        (NativeResidualAttainment.input T points candidates) ()
        (NativeResidualAttainment.valid T points candidates (by omega)) 1 := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_all_cost_mem_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz budget hb

/-- A genuine native upper bound on the same real-mean source oracle; no
restriction to handpicked competitors or a supplied finite optimum is used. -/
theorem native_all_upper_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z) (budget : ℕ)
      (hb : 0 < budget) :
    BatchOptimum.optimum (NativeResidualAll.config budget)
      (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (NativeResidualAttainment.input T points candidates) ()
      (NativeResidualAttainment.valid T points candidates (by omega)) 1 ≤
        ENNReal.ofReal (∑ j, P.specialistCost j) :=
  sInf_le (native_all_cost_mem_conditional T points candidates P ν hν hz budget hb)

/-- A genuine native upper bound on the same real-mean source oracle; no
restriction to handpicked competitors or a supplied finite optimum is used. -/
theorem native_all_upper (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (budget : ℕ)
      (hb : 0 < budget) :
    BatchOptimum.optimum (NativeResidualAll.config budget)
      (NativeResidualInvoice.sample T points candidates P ν)
      (NativeResidualAttainment.input T points candidates) ()
      (NativeResidualAttainment.valid T points candidates (by omega)) 1 ≤
        ENNReal.ofReal (∑ j, P.specialistCost j) :=
  sInf_le (native_all_cost_mem T points candidates P ν hν hz budget hb)

end Cslib.Probability.StochasticOracle.NativeResidualRealCost
