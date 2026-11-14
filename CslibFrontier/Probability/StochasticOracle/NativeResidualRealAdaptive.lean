/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualRealCost
import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution.OutputTransfer
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Adaptive residual execution with conditional fixed-mean invoices

[Wang2027], model p. 5 and Theorem 6 p. 13. The native program selects the
specialist from the actual near report. The first and second source batches draw
invoice vectors conditional on the actual accepted history, selected batch and
new residual. Their derived joint law keeps the dependent order of all three draws.
The fixed-PMF specializations also admit their independent mixture description;
no mixture of fixed-invoice oracles is asserted for a response-dependent kernel.

## Main definitions

* `combine`: the two invoices actually observed on a near-then-specialist path.

## Main results

* `feedback_law_conditional`, `native_law_conditional`, `native_resources_conditional`:
  actual execution with history- and response-dependent invoices.
* `native_expected_cost_conditional`, `native_certified_conditional`,
  `native_cost_mem_conditional`: exact bill, certified success and admitted attainment.
* `feedback_law`, `native_mixture`, `native_resources`: both actual response-dependent
  source epochs, their fresh invoices and joint native resources.
* `native_expected_cost`, `native_certified`, `native_selectionOnly`: exact expected
  bill and certified admitted tape output of that same native program.
* `minimum_cost_mem`: the real source minimum is attained as a feasible native cost.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualRealAdaptive
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention ConcurrentBatch ResidualCover
open NativeResidualAttainment NativeResidualRouting Finset
open Cslib.Optimization.OneConstraint
open scoped NNReal ENNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- The near invoice comes from the first draw; every potential specialist
invoice comes from the fresh second draw. No response-dependent price is introduced. -/
@[expose] def combine (f g : Fin (z + 1) → ℕ) : Fin (z + 1) → ℕ :=
  Fin.cases (f 0) (fun j => g j.succ)

private theorem near_memory (f g : Fin (z + 1) → ℕ) (j : Fin z) :
    afterNearMemory T points candidates f j =
      afterNearMemory T points candidates (combine f g) j := by
  unfold afterNearMemory
  rw [receipt_congr T points candidates f (combine f g) 0 (some j) rfl]

/-- The actual two-turn feedback has one residual draw and two fresh invoice
draws, retaining complete updated runtime state and source memory. -/
theorem feedback_law_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z) (hz : 3 ≤ z) :
    (Feedback.run
      (environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν))
      2 (NativeResidualRouting.initial true (input T points candidates))
      (fun _ => ⟨[], [], 0⟩) initialMemory request).map
        (fun outcome => (outcome.state, outcome.memory)) =
    P.missing.toPMF.bind fun j =>
      (ν [] (batch T points candidates 0) (some j)).bind fun f =>
        (ν (afterNearMemory T points candidates f j).privateState.history
          (batch T points candidates j.succ) none).map fun g =>
          (afterSpecialist T points candidates (combine f g) j,
            afterSpecialistMemory T points candidates (combine f g) j) := by
  have hfirst :
      environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
        ((), request (NativeResidualRouting.initial true (input T points candidates)))
        initialMemory = P.missing.toPMF.bind fun j =>
          (ν [] (batch T points candidates 0) (some j)).map fun invoice =>
            (replyOf (receipt T points candidates invoice 0 (some j)),
              (afterNearMemory T points candidates invoice j).privateState) :=
    first_source_conditional T points candidates P ν
  rw [Feedback.run, initial_live T points candidates true hz]
  simp only [Bool.false_eq_true, ite_false, PMF.monad_bind_eq_bind, PMF.map_bind]
  simp only [hfirst, PMF.bind_bind, PMF.bind_map]
  have hstate (f : Fin (z + 1) → ℕ) (j : Fin z) :
      RuntimeControl.afterReply (NativeResidualRouting.initial true (input T points candidates))
        (replyOf (receipt T points candidates f 0 (some j))).word =
          afterNear T points candidates j (f 0) := by
    rw [near_word]
    rfl
  have hmem (f : Fin (z + 1) → ℕ) (j : Fin z) : initialMemory.record
      ((), request (NativeResidualRouting.initial true (input T points candidates)))
      (replyOf (receipt T points candidates f 0 (some j)))
      (afterNearMemory T points candidates f j).privateState =
        afterNearMemory T points candidates f j := by
    rw [first_request]
    rfl
  have hsecond (f : Fin (z + 1) → ℕ) (j : Fin z) :
      environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
        ((), request (afterNear T points candidates j (f 0)))
        (afterNearMemory T points candidates f j) =
      (ν (afterNearMemory T points candidates f j).privateState.history
        (batch T points candidates j.succ) none).map fun g =>
        (replyOf (receipt T points candidates g j.succ none),
          commit (afterNearMemory T points candidates f j).privateState
            (receipt T points candidates g j.succ none) ()) :=
    second_source_conditional T points candidates P ν hz j f
  simp only [Function.comp_def, hstate, hmem, Feedback.run,
    afterNear_live T points candidates hz, Bool.false_eq_true, ite_false,
    hsecond, PMF.pure_map, PMF.monad_bind_eq_bind, PMF.map_bind]
  apply congrArg P.missing.toPMF.bind
  funext j
  apply congrArg (ν [] (batch T points candidates 0) (some j)).bind
  funext f
  simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  apply congrArg (ν (afterNearMemory T points candidates f j).privateState.history
    (batch T points candidates j.succ) none).bind
  funext g
  rw [receipt_congr T points candidates g (combine f g) j.succ none rfl,
    near_memory T points candidates f g j]
  simp only [second_request T points candidates hz]
  rfl

/-- The actual two-turn feedback has one residual draw and two fresh invoice
draws, retaining complete updated runtime state and source memory. -/
theorem feedback_law (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z) :
    (Feedback.run (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      2 (NativeResidualRouting.initial true (input T points candidates))
      (fun _ => ⟨[], [], 0⟩) initialMemory request).map
        (fun outcome => (outcome.state, outcome.memory)) =
    ν.bind fun f =>
      P.missing.toPMF.bind fun j =>
        ν.map fun g =>
          (afterSpecialist T points candidates (combine f g) j,
            afterSpecialistMemory T points candidates (combine f g) j) := by
  rw [← NativeResidualConditionalInvoice.sample_const, feedback_law_conditional T points candidates
    P (fun _ _ _ => ν) hz]
  exact PMF.bind_comm _ _ _

/-- The actual compiled adaptive program preserves the dependent order of
residual and invoice draws, including the reached history for its second invoice. -/
theorem native_law_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z) (hz : 3 ≤ z) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
        (Option.map fun w => (w.config.tapes.output, w.memory)) =
    P.missing.toPMF.bind fun j =>
      (ν [] (batch T points candidates 0) (some j)).bind fun f =>
        (ν (afterNearMemory T points candidates f j).privateState.history
          (batch T points candidates j.succ) none).map fun g =>
          some (RuntimeControl.result (afterSpecialist T points candidates (combine f g) j),
            afterSpecialistMemory T points candidates (combine f g) j) := by
  have h := congrArg (PMF.map (Option.map fun observation : NativeReplyContext.Observation
      (ServerState (z + 1) Unit) => (observation.output, observation.memory)))
    (NativeResidualRouting.controller_law true _
      (environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν))
      (input T points candidates) initialMemory)
  simp only [PMF.map_comp, Function.comp_def, Option.map_map, NativeReplyContext.observe,
    ite_true] at h
  rw [h]
  have hf := congrArg (PMF.map (fun pair : RuntimeControl.State ×
      Memory Unit (ServerState (z + 1) Unit) =>
        some (RuntimeControl.result pair.1, pair.2)))
    (feedback_law_conditional T points candidates P ν hz)
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some] using hf

/-- Joint resource law on the same conditional oracle: each actual near response
selects the next specialist and the history used by its invoice kernel. -/
theorem native_resources_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z) (hz : 3 ≤ z) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
        (Option.map fun w => (tokenBill w.memory.events, elapsed w.memory.events)) =
    P.missing.toPMF.bind fun j =>
      (ν [] (batch T points candidates 0) (some j)).bind fun f =>
        (ν (afterNearMemory T points candidates f j).privateState.history
          (batch T points candidates j.succ) none).map fun g =>
          some ((((f 0 + g j.succ : ℕ) : ℝ≥0)), (2 : ℝ≥0)) := by
  have h := congrArg (PMF.map (Option.map fun pair : Word ×
      Memory Unit (ServerState (z + 1) Unit) =>
        (tokenBill pair.2.events, elapsed pair.2.events)))
    (native_law_conditional T points candidates P ν hz)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_map,
    Option.map_some, afterSpecialistMemory_resources, combine] at h
  exact h

/-- The actual compiled adaptive program has the coupled fixed-invoice laws
obtained by executing its near and selected specialist epochs. Fresh draws at
those two epochs are kept separate; no arbitrary-policy mixture is assumed. -/
theorem native_mixture (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
        (Option.map fun w => (w.config.tapes.output, w.memory)) =
    ν.bind fun f =>
      ν.bind fun g =>
        (NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
          (environment limits (NativeResidualOracle.sample T points candidates P (combine f g)))
          ⟨(NativeResidualRouting.controller true).program.initialConfig
            (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
            (Option.map fun w => (w.config.tapes.output, w.memory)) := by
  have hn := congrArg (PMF.map (Option.map fun o : NativeReplyContext.Observation
      (ServerState (z + 1) Unit) => (o.output, o.memory)))
    (NativeResidualRouting.controller_law true _
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      (input T points candidates) initialMemory)
  simp only [PMF.map_comp, Function.comp_def, Option.map_map, NativeReplyContext.observe,
    ite_true, Option.map_some] at hn
  rw [hn]
  have hf := congrArg (PMF.map (fun pair : RuntimeControl.State ×
      Memory Unit (ServerState (z + 1) Unit) =>
        some (RuntimeControl.result pair.1, pair.2))) (feedback_law T points candidates P ν hz)
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at hf
  refine hf.trans ?_
  simp_rw [NativeResidualAttainment.native_law T points candidates P _ hz]
  apply congrArg ν.bind
  funext f
  exact PMF.bind_comm _ _ _

/-- Joint native resource law: the selected specialist depends on the actual
near response, and each epoch pays its own freshly drawn natural invoice. -/
theorem native_resources (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z) :
    (NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
        (Option.map fun w => (tokenBill w.memory.events, elapsed w.memory.events)) =
    ν.bind fun f =>
      P.missing.toPMF.bind fun j =>
        ν.map fun g =>
          some ((((f 0 + g j.succ : ℕ) : ℝ≥0)), (2 : ℝ≥0)) := by
  have h := congrArg (PMF.map (Option.map fun pair : Word ×
      Memory Unit (ServerState (z + 1) Unit) =>
        (tokenBill pair.2.events, elapsed pair.2.events))) (native_mixture T points candidates P
          ν hz)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_map] at h
  refine h.trans ?_
  simp_rw [NativeResidualAttainment.native_resources T points candidates P _ hz]
  apply congrArg ν.bind
  funext f
  change (ν.bind fun g => P.missing.toPMF.map fun j =>
    some ((((f 0 + g j.succ : ℕ) : ℝ≥0)), (2 : ℝ≥0))) = _
  exact PMF.bind_comm _ _ _

/-- The original adaptive program realizes arbitrary fixed real expected prices
by actual natural token reports. Local termination, prefix accounting and the
expected bill are derived, without integrability or bounded-bill premises. -/
theorem native_expected_cost_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z) :
    NativeBatch.Quantitative.expected limits
      (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (NativeResidualRouting.controller true).program NativeBatch.Trace.charge 3
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ =
      ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) := by
  let program := (NativeResidualRouting.controller true).program
  let world := (⟨program.initialConfig (GuardedStartup.encoding (input T points candidates)),
    initialMemory⟩ : World (NativeResidualRouting.controller true).tapes
      (NativeResidualRouting.controller true).Controls Unit (ServerState (z + 1) Unit)
      (GuardedStartup.encoding (input T points candidates)))
  let μ := NativeUnboundedExecution.terminal program
    (environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν)) world
  have hlaw := native_resources_conditional T points candidates P ν hz
  have hterm : μ none = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hn
    have hm : none ∈ (μ.map (Option.map fun w =>
        (tokenBill w.memory.events, elapsed w.memory.events))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
    rw [hlaw] at hm
    simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hm
    obtain ⟨f, _, j, _, g, _, he⟩ := hm
    cases he
  have he := NativeBatch.Quantitative.expected_charge_eq_terminal limits
    (NativeResidualConditionalInvoice.sample T points candidates P ν) program world
    (NativeBatch.initial_invariant limits ()) rfl hterm
  change NativeBatch.Quantitative.expected _ _ _ NativeBatch.Trace.charge
    ((limits (z := z)).turns + 1) world = _
  rw [he]
  have hm := PMF.tsum_map_mul μ (Option.map fun w =>
    (tokenBill w.memory.events, elapsed w.memory.events))
    (fun result => result.elim 0 (fun pair => (pair.1 : ℝ≥0∞)))
  simp only [Option.elim_map, Function.comp_def] at hm
  change (∑' result, μ result * result.elim 0
    (fun w => (tokenBill w.memory.events : ℝ≥0∞))) = _
  rw [← hm, hlaw, PMF.tsum_bind_mul]
  simp_rw [PMF.tsum_bind_mul, PMF.tsum_map_mul]
  simp only [Option.elim_some, ENNReal.coe_natCast, Nat.cast_add, ENNReal.coe_add]
  change (∑' j, P.missing.toPMF j *
    ∑' f, ν [] (batch T points candidates 0) (some j) f *
      ∑' g, ν (afterNearMemory T points candidates f j).privateState.history
        (batch T points candidates j.succ) none g *
          ((f 0 : ℝ≥0∞) + (g j.succ : ℝ≥0∞))) = _
  have hnear : (∑' j, P.missing.toPMF j *
      ∑' f, ν [] (batch T points candidates 0) (some j) f * (f 0 : ℝ≥0∞)) =
      ENNReal.ofReal P.nearCost := by
    simpa [calls_batch, finSuccEquiv_zero, reply, Distribution.toPMF_map,
      PMF.tsum_map_mul, NativeResidualOracle.invoiceCost, batchCost] using
      hν [] (batch T points candidates 0)
  have hspec (f : Fin (z + 1) → ℕ) (j : Fin z) :
      (∑' g, ν (afterNearMemory T points candidates f j).privateState.history
        (batch T points candidates j.succ) none g * (g j.succ : ℝ≥0∞)) =
      ENNReal.ofReal (P.specialistCost j) := by
    simpa [calls_batch, finSuccEquiv_succ, reply, Distribution.toPMF_pure,
      NativeResidualOracle.invoiceCost, batchCost] using
      hν (afterNearMemory T points candidates f j).privateState.history
        (batch T points candidates j.succ)
  have hg (f : Fin (z + 1) → ℕ) (j : Fin z) :
      (∑' g, ν (afterNearMemory T points candidates f j).privateState.history
        (batch T points candidates j.succ) none g *
          ((f 0 : ℝ≥0∞) + (g j.succ : ℝ≥0∞))) =
        (f 0 : ℝ≥0∞) + ENNReal.ofReal (P.specialistCost j) := by
    simp_rw [mul_add]
    rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, hspec]
  simp_rw [hg]
  simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [hnear]
  have hmean := Cslib.Optimization.OneConstraint.Distribution.ofReal_mean P.missing
    P.specialistCost (fun j => (P.specialist_pos j).le)
  rw [← hmean]
  exact (ENNReal.ofReal_add P.near_pos.le (Finset.sum_nonneg
    (fun j _ => mul_nonneg (P.missing.nonneg j) (P.specialist_pos j).le))).symm

/-- The original adaptive program realizes arbitrary fixed real expected prices
by actual natural token reports. Local termination, prefix accounting and the
expected bill are derived, without integrability or bounded-bill premises. -/
theorem native_expected_cost (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) :
    NativeBatch.Quantitative.expected limits (NativeResidualInvoice.sample T points candidates P ν)
      (NativeResidualRouting.controller true).program NativeBatch.Trace.charge 3
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ =
      ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_expected_cost_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz

/-- Response- and history-dependent invoices preserve successful-output
provenance of the actual adaptive program, including all finite halted runs. -/
theorem native_selectionOnly_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z) (hz : 3 ≤ z)
    (accept : Finset (Fin (input T points candidates).startup.system.rows.length) → Bool) :
    NativeUnboundedExecution.SelectionOnly (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν))
      (NativeBatch.candidateParser (n := z + 1)
        (input T points candidates).startup.system.rows.length)
      (decodeFamily (input T points candidates).startup.system.rows.length) accept
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ := by
  apply NativeUnboundedExecution.selectionOnly_of_output_memory_support
  intro output memory hm C hc _
  rw [native_law_conditional T points candidates P ν hz] at hm
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hm
  obtain ⟨j, _, f, _, g, _, he⟩ := hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  rw [NativeBatch.candidateParser_proposals]
  exact completed_output_provenance T points candidates (combine f g) j
    (valid T points candidates (by omega)) C hc

/-- The same actual adaptive program has certified tape success one under any
conditional invoice kernel, without a mean, bounded-fee or integrability premise. -/
theorem native_certified_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z) (hz : 3 ≤ z) :
    ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualConditionalInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
      (BatchOutput.certified limits (input T points candidates).startup.system
        (valid T points candidates (by omega)))) true = 1 := by
  rw [BatchOutput.terminal_certified, native_law_conditional T points candidates P ν hz,
    PMF.map_bind]
  simp_rw [PMF.map_bind, PMF.map_comp]
  simp only [Function.comp_def, completed_certifiedObservation T points candidates _ hz,
    PMF.bind_apply, PMF.map_apply, ite_true, mul_one, PMF.tsum_coe]

/-- Actual adaptive attainment in the same common-oracle competitor class,
with only primitive selected-before-response means imposed on invoices. -/
theorem native_cost_mem_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z) :
    ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) ∈
      BatchOptimum.costs limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
        (input T points candidates) () (valid T points candidates (by omega)) 1 := by
  refine ⟨(NativeResidualRouting.controller true).tapes,
    (NativeResidualRouting.controller true).Controls,
    (NativeResidualRouting.controller true).finite,
    (NativeResidualRouting.controller true).program,
    native_selectionOnly_conditional T points candidates P ν hz _, ?_, ?_⟩
  · exact (native_certified_conditional T points candidates P ν hz).ge
  · exact (native_expected_cost_conditional T points candidates P ν hν hz).symm

/-- Fresh natural invoices preserve successful-output selection provenance of
all finite halted executions of the actual adaptive native program. -/
theorem native_selectionOnly (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z)
    (accept : Finset (Fin (input T points candidates).startup.system.rows.length) → Bool) :
    NativeUnboundedExecution.SelectionOnly (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      (NativeBatch.candidateParser (n := z + 1) (input T points
        candidates).startup.system.rows.length)
      (decodeFamily (input T points candidates).startup.system.rows.length) accept
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_selectionOnly_conditional T points candidates P (fun _ _ _ => ν) hz accept

/-- Certified actual tape success for the same adaptive program and real-mean source. -/
theorem native_certified (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z) :
    ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller true).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
      (BatchOutput.certified limits (input T points candidates).startup.system
        (valid T points candidates (by omega)))) true = 1 := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_certified_conditional T points candidates P (fun _ _ _ => ν) hz

/-- The actual adaptive real expected bill is attained in the original native
competitor class, on the same oracle and initial seed used by all competitors. -/
theorem native_cost_mem (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) :
    ENNReal.ofReal (P.nearCost + P.missing.mean P.specialistCost) ∈
      BatchOptimum.costs limits (NativeResidualInvoice.sample T points candidates P ν)
        (input T points candidates) () (valid T points candidates (by omega)) 1 := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_cost_mem_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz

/-- Both source alternatives, with arbitrary real fixed means, are attained as
actual native bills. This statement records feasibility; the universal real-price
optimum equality is assembled downstream in `NativeResidualRealMinima`. -/
theorem minimum_cost_mem_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z) :
    ENNReal.ofReal (min (∑ j, P.specialistCost j)
      (P.nearCost + P.missing.mean P.specialistCost)) ∈
      BatchOptimum.costs limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
        (input T points candidates) () (valid T points candidates (by omega)) 1 := by
  by_cases h : P.nearCost + P.missing.mean P.specialistCost ≤ ∑ j, P.specialistCost j
  · rw [min_eq_right h]
    exact native_cost_mem_conditional T points candidates P ν hν hz
  · rw [min_eq_left (le_of_not_ge h)]
    exact NativeResidualRealCost.native_all_cost_mem_conditional T points candidates P ν hν hz
      2 (by omega)

/-- Both source alternatives, with arbitrary real fixed means, are attained as
actual native bills. This statement records feasibility; the universal real-price
optimum equality is assembled downstream in `NativeResidualRealMinima`. -/
theorem minimum_cost_mem (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) :
    ENNReal.ofReal (min (∑ j, P.specialistCost j)
      (P.nearCost + P.missing.mean P.specialistCost)) ∈
      BatchOptimum.costs limits (NativeResidualInvoice.sample T points candidates P ν)
        (input T points candidates) () (valid T points candidates (by omega)) 1 := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    minimum_cost_mem_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz

end Cslib.Probability.StochasticOracle.NativeResidualRealAdaptive
