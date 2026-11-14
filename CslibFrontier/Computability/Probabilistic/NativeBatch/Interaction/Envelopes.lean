/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction.Selection
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction.Rewards
import CslibFrontier.Probability.PMF.Disintegration.Support
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Fixed-source envelopes for actual native conditional rewards

Native conditional invoice and progress means are averages of primitive means
under the one fixed enriched source. Private selection may mix checkpoints, but
cannot replace the source filter after its complete history. Nonnegative extended
scores permit unbounded invoices and infinite expectations.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Interaction
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
open scoped ENNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- The actual native conditional reward is an average of the same fixed source's
history-filtered response means. This whole-law consequence includes null prior
completion; inequalities tied to a particular observation still require positive mass. -/
theorem conditional_reward (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
    (o : Quantitative.Observation n)
    (reward : List (Trace.Record n) → Trace.Record n → ℝ≥0∞) :
    History.conditionalMean limits sample machine
        (initial.bind fun privateState => Trace.law limits sample machine epochs
          ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩) o reward =
      ∑' view, PMF.posterior (selectionViews limits sample initial machine config epochs)
        (selectedObservation limits) o view *
          ∑' pair, ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).draw
            view.history view.query) pair * reward (view.history.map Prod.snd) pair.1 := by
  rw [History.conditionalMean, conditional_filteredSource]
  unfold Quantitative.mean
  rw [PMF.tsum_bind_mul]
  apply PMF.tsum_mul_congr_support
  intro view hv
  have hv' := PMF.support_posterior_subset
    (selectionViews limits sample initial machine config epochs) (selectedObservation limits) o hv
  obtain ⟨hq, hb⟩ := selectionViews_valid limits sample initial machine config epochs view hv'
  rw [InteractionProcess.Source.draw, PMF.tsum_bind_mul, PMF.tsum_bind_mul]
  apply PMF.tsum_mul_congr_support
  intro privateState _
  have he := response_reward limits sample initial machine
    (⟨view.history, view.policyState, privateState⟩ : State n k Private Control input)
    view.policyState hb reward
  simpa only [Quantitative.mean, trace, hidden, selectedTrace, hq] using he

section Bounds
variable (limits : Limits n) (sample : Sampler n Private) (initial : PMF Private)
  (machine : MultiTapePTM k Bool Control Unit)
  (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
  (o : Quantitative.Observation n)
  (reward : List (Trace.Record n) → Trace.Record n → ℝ≥0∞) (c : ℝ≥0∞)
  (ho : o ∈ ((Quantitative.select limits sample machine
    (initial.bind fun privateState => Trace.law limits sample machine epochs
      ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩)).map
        (Quantitative.observe limits)).support)

include ho

/-- Primitive upper means under the fixed source survive actual private stopping
and conditioning on a positive-mass native observation. -/
theorem conditional_reward_le
    (H : ∀ view ∈ (selectionViews limits sample initial machine config epochs).support,
      selectedObservation limits view = o →
        (∑' pair, ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).draw
          view.history view.query) pair * reward (view.history.map Prod.snd) pair.1) ≤ c) :
    History.conditionalMean limits sample machine
      (initial.bind fun privateState => Trace.law limits sample machine epochs
        ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩) o reward ≤ c := by
  rw [conditional_reward]
  apply PMF.tsum_mul_le_of_support
  intro view hv
  have ho' : o ∈ ((selectionViews limits sample initial machine config epochs).map
      (selectedObservation limits)).support := by
    rw [selection_observations]
    exact ho
  obtain ⟨hv', he⟩ := PMF.mem_support_of_posterior _ _ _ ho' view hv
  exact H view hv' he

/-- Primitive lower means under the fixed source survive actual private stopping
and conditioning on a positive-mass native observation, without an integrability premise. -/
theorem conditional_reward_ge
    (H : ∀ view ∈ (selectionViews limits sample initial machine config epochs).support,
      selectedObservation limits view = o →
        c ≤ ∑' pair,
          ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).draw
            view.history view.query) pair * reward (view.history.map Prod.snd) pair.1) :
    c ≤ History.conditionalMean limits sample machine
      (initial.bind fun privateState => Trace.law limits sample machine epochs
        ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩) o reward := by
  rw [conditional_reward]
  have ho' : o ∈ ((selectionViews limits sample initial machine config epochs).map
      (selectedObservation limits)).support := by
    rw [selection_observations]
    exact ho
  calc
    c = ∑' view, PMF.posterior (selectionViews limits sample initial machine config epochs)
        (selectedObservation limits) o view * c := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := PMF.tsum_mul_mono_support _ fun view hv => by
      obtain ⟨hv', he⟩ := PMF.mem_support_of_posterior _ _ _ ho' view hv
      exact H view hv' he

/-- Any supported fixed-source receipt property transfers to the actual native
conditional next record, with its exact previous receipt history retained. -/
theorem conditional_records (P : List (Trace.Record n) → Trace.Record n → Prop)
    (H : ∀ view ∈ (selectionViews limits sample initial machine config epochs).support,
      selectedObservation limits view = o →
        ∀ pair ∈ ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).draw
          view.history view.query).support, P (view.history.map Prod.snd) pair.1)
    (next : Trace.State n k Private Control input)
    (hn : next ∈ (Quantitative.conditional limits sample machine
      (initial.bind fun privateState => Trace.law limits sample machine epochs
        ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩) o).support) :
    ∃ record, next.records = record :: o.history ∧ P o.history record := by
  rw [conditional_filteredSource] at hn
  simp only [PMF.mem_support_bind_iff] at hn
  obtain ⟨view, hv, privateState, hp, hn⟩ := hn
  have ho' : o ∈ ((selectionViews limits sample initial machine config epochs).map
      (selectedObservation limits)).support := by
    rw [selection_observations]
    exact ho
  obtain ⟨hv', hobs⟩ := PMF.mem_support_of_posterior _ _ _ ho' view hv
  obtain ⟨hq, hb⟩ := selectionViews_valid limits sample initial machine config epochs view hv'
  have hh : view.history.map Prod.snd = o.history :=
    congrArg Quantitative.Observation.history hobs
  let state : State n k Private Control input := ⟨view.history, view.policyState, privateState⟩
  change next ∈ (Trace.respond limits sample machine (trace state)
    (view.policyState.map (Phase.mapMemory
      (Memory.mapPrivate (ServerState.mapPrivate fun _ => privateState))))).support at hn
  rw [← response_trace limits sample initial machine state view.policyState hb] at hn
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hn
  obtain ⟨⟨record, nextPrivate⟩, hr, nextPolicy, _, rfl⟩ := hn
  have hr' : (record, nextPrivate) ∈
      ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).draw
        view.history view.query).support := by
    rw [InteractionProcess.Source.draw, PMF.mem_support_bind_iff]
    refine ⟨privateState, hp, ?_⟩
    simpa only [state, hq] using hr
  refine ⟨record, ?_, ?_⟩
  · simp only [state, hh]
  · simpa only [hh] using H view hv' hobs (record, nextPrivate) hr'

end Bounds

end Cslib.Probability.NativeBatch.Interaction
