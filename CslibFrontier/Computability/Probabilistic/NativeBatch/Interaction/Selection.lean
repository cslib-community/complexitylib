/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Quantitative.Conditioning
public import CslibFrontier.Probability.PMF.Interaction.Selection
import CslibFrontier.Probability.PMF.Disintegration.Map
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual native selection before dispatch of the shared source

Private silent stopping selects a complete native checkpoint before the source
responds. The selected checkpoint and earlier accepted receipts recover the actual
native observation and conditional dispatch; source-private state is retained as
an independent filtered component of the separated selection law.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Interaction
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
open StochasticOracle.ConcurrentBatch.Interaction (Request)
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- Actual private selection and real latent source state before response sampling. -/
abbrev Selection (n k : ℕ) (Private Control : Type) (input : List Bool) :=
  InteractionProcess.Selected (Option (Request n)) (Option (Exchange n))
    (Option (Phase k Control Unit (ServerState n Unit) input)) Private

/-- Actual private selected checkpoints with latent source state erased.
This is the mixing law for source-independent native observations and envelopes. -/
@[expose] def selectionViews (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ) :
    PMF (Selection n k Unit Control input) :=
  (InteractionProcess.selectionLaw (policy limits machine config)
    (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs).map
      InteractionProcess.Selected.policyView

/-- Read the real selected checkpoint and retained receipts from actual private
selection, replacing only the dummy latent source state. -/
@[expose] def selectedTrace
    (picked : Selection n k Private Control input) :
    Trace.State n k Private Control input :=
  ⟨picked.policyState.map
    (Phase.mapMemory (Memory.mapPrivate (ServerState.mapPrivate fun _ => picked.sourceState))),
    picked.history.map Prod.snd⟩

/-- Native observation before response depends on the retained private selection,
not on latent source state. Analytical receipts remain in the history. -/
@[expose] def selectedObservation (limits : Limits n)
    (picked : Selection n k Unit Control input) :
    Quantitative.Observation n :=
  ⟨picked.history.map Prod.snd, sourceSignal limits picked.policyState⟩

/-- Restoring latent state does not alter the actual selected native observation. -/
theorem observe_selectedTrace (limits : Limits n)
    (picked : Selection n k Private Control input) :
    (⟨(selectedTrace picked).records, sourceSignal limits (selectedTrace picked).hidden⟩ :
      Quantitative.Observation n) = selectedObservation limits picked.policyView := by
  simp only [selectedTrace, selectedObservation, InteractionProcess.Selected.policyView,
    sourceSignal_mapPrivate]

/-- Actual native selected-checkpoint laws are the readback of the separated
selection law, before any source response is sampled. -/
theorem selection_trace (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ) :
    (InteractionProcess.selectionLaw (policy limits machine config)
      (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs).map
        selectedTrace =
      (Quantitative.select limits sample machine
        (initial.bind fun privateState => Trace.law limits sample machine epochs
          ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩)).map
            Quantitative.Selected.checkpointState := by
  rw [← execution_trace]
  simp only [InteractionProcess.selectionLaw, InteractionProcess.select, policy,
    Quantitative.select, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.bind_map, PMF.pure_map,
    PMF.map_comp, Function.comp_def, selectedTrace, Quantitative.Selected.checkpointState,
    trace, hidden]
  apply PMF.bind_congr_on_support
  intro state _
  rw [← seekSourceFrom_mapPrivate limits silentSampler sample machine
    (fun _ => state.sourceState) state.policyState]
  rw [PMF.bind_map]
  rfl

/-- Erased private selections have exactly the actual native observation law. -/
theorem selection_observations (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ) :
    (selectionViews limits sample initial machine config epochs).map
        (selectedObservation limits) =
      (Quantitative.select limits sample machine
        (initial.bind fun privateState => Trace.law limits sample machine epochs
          ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩)).map
            (Quantitative.observe limits) := by
  let observeTrace (state : Trace.State n k Private Control input) : Quantitative.Observation n :=
    ⟨state.records, sourceSignal limits state.hidden⟩
  have he := congrArg (PMF.map observeTrace)
    (selection_trace limits sample initial machine config epochs)
  rw [PMF.map_comp, PMF.map_comp] at he
  have hl : observeTrace ∘ selectedTrace =
      selectedObservation limits ∘ InteractionProcess.Selected.policyView := by
    funext picked
    exact observe_selectedTrace limits picked
  have hr : observeTrace ∘ Quantitative.Selected.checkpointState =
      Quantitative.observe (k := k) (Control := Control) (Private := Private) (input := input)
        limits := rfl
  rw [hl, hr] at he
  simpa only [selectionViews, PMF.map_comp] using he

/-- Every reached selection retains its actual request and stops at a genuine
accepted batch or committed halt; no supplied selection-validity premise is needed. -/
theorem selection_valid (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
    (picked : Selection n k Private Control input)
    (hp : picked ∈ (InteractionProcess.selectionLaw (policy limits machine config)
      (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs).support) :
    picked.query = request limits picked.policyState ∧
      ∀ phase, picked.policyState = some phase → sourceBoundary limits phase := by
  simp only [InteractionProcess.selectionLaw, PMF.mem_support_bind_iff] at hp
  obtain ⟨state, _, hp⟩ := hp
  simp only [InteractionProcess.select, policy, PMF.map_comp, Function.comp_def,
    PMF.mem_support_map_iff] at hp
  obtain ⟨hit, hh, rfl⟩ := hp
  refine ⟨rfl, ?_⟩
  intro phase he
  change hit = some phase at he
  rw [he] at hh
  cases hc : state.policyState with
  | none => simp [hc, seekSourceFrom] at hh
  | some previous =>
    simp only [hc, seekSourceFrom] at hh
    exact ((StoppedProcess.terminal_support _ _ _ _ _).mp hh).1

/-- Every supported private view retains its actual request and a genuine
accepted-batch/halting boundary after erasing latent source state. -/
theorem selectionViews_valid (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
    (view : Selection n k Unit Control input)
    (hv : view ∈ (selectionViews limits sample initial machine config epochs).support) :
    view.query = request limits view.policyState ∧
      ∀ phase, view.policyState = some phase → sourceBoundary limits phase := by
  obtain ⟨picked, hp, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
  exact selection_valid limits sample initial machine config epochs picked hp

/-- The original issued-source flag is exactly the presence of the actual selected request. -/
theorem selectedObservation_issued (limits : Limits n)
    (view : Selection n k Unit Control input) :
    (selectedObservation limits view).issued = (request limits view.policyState).isSome := by
  cases hc : view.policyState with
  | none => simp [selectedObservation, Quantitative.Observation.issued, sourceSignal, request, hc]
  | some phase =>
    cases phase with
    | ready world =>
      simp [selectedObservation, Quantitative.Observation.issued, sourceSignal, request, hc]
    | pending chosen =>
      cases chosen with
      | halted world =>
        simp [selectedObservation, Quantitative.Observation.issued, sourceSignal, request, hc]
      | «local» world =>
        simp [selectedObservation, Quantitative.Observation.issued, sourceSignal, request, hc]
      | query world op next =>
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer <;>
          simp [selectedObservation, Quantitative.Observation.issued, sourceSignal, request, hc, ha]

/-- The original native conditional response is obtained by conditioning the
actual separated selection law on its policy-side observation. This includes
null-observation prior completion and assumes no source-posterior identity. -/
theorem conditional_selectionLaw (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
    (o : Quantitative.Observation n) :
    Quantitative.conditional limits sample machine
        (initial.bind fun privateState => Trace.law limits sample machine epochs
          ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩) o =
      (PMF.posterior (InteractionProcess.selectionLaw (policy limits machine config)
        (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs)
          (selectedObservation limits ∘ InteractionProcess.Selected.policyView) o).bind
            (fun picked => Trace.respond limits sample machine
              (selectedTrace picked) (selectedTrace picked).hidden) := by
  rw [Quantitative.conditional_checkpointState, ← selection_trace,
    ← PMF.posterior_map, PMF.bind_map]
  have ho : (fun state : Trace.State n k Private Control input =>
      (⟨state.records, sourceSignal limits state.hidden⟩ : Quantitative.Observation n)) ∘
        selectedTrace = selectedObservation limits ∘ InteractionProcess.Selected.policyView := by
    funext picked
    exact observe_selectedTrace limits picked
  rw [ho]
  rfl

/-- Even after conditioning on the native observation, actual dispatch samples
latent state from the fixed source filter at the retained enriched history.
Only the mixture over private selected checkpoints depends on the native machine. -/
theorem conditional_filteredSource (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (config : Turing.MultiTapeMachine.Config k Bool Control Unit input) (epochs : ℕ)
    (o : Quantitative.Observation n) :
    Quantitative.conditional limits sample machine
        (initial.bind fun privateState => Trace.law limits sample machine epochs
          ⟨config, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩) o =
      (PMF.posterior (selectionViews limits sample initial machine config epochs)
        (selectedObservation limits) o).bind fun view =>
            ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).filter
              view.history).bind fun privateState =>
                let picked : Selection n k Private Control input :=
                  ⟨view.history, view.query, view.policyState, privateState⟩
                Trace.respond limits sample machine (selectedTrace picked)
                  (selectedTrace picked).hidden := by
  rw [conditional_selectionLaw]
  let response (pair : Selection n k Unit Control input × Private) :=
    let (view, privateState) := pair
    let picked : Selection n k Private Control input :=
      ⟨view.history, view.query, view.policyState, privateState⟩
    Trace.respond limits sample machine (selectedTrace picked) (selectedTrace picked).hidden
  have he := congrArg (fun μ : PMF (Selection n k Unit Control input × Private) => μ.bind response)
    (InteractionProcess.selectionLaw_posterior_joint (policy limits machine config)
      (StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial) epochs
      (selectedObservation limits) o)
  simpa only [selectionViews, PMF.bind_map, PMF.bind_bind, Function.comp_def, response,
    InteractionProcess.Selected.policyView] using he

end Cslib.Probability.NativeBatch.Interaction
