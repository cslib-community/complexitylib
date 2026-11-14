/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Interaction.Process
public import CslibFrontierTests.InteractionFilter
import Mathlib.Tactic

/-!
# Actual two-turn execution with a common persistent source filter

Independent source and policy private bits start an actual interaction process.
The first reply is noisy; later queries depend on that reply and the retained
private policy bit. The common source posterior is derived from actual execution,
including support of the complete two-turn history. No intermediate independent
posterior or behavioral representation equality is assumed.
-/

public section
noncomputable section
namespace CslibFrontierTests.InteractionProcess
open Cslib.Probability
open Cslib.Probability.InteractionProcess
open scoped ENNReal

/-- The first response is noisy; later selected queries may reveal the persistent bit. -/
def source : Source Bool Bool Bool where
  initial := InteractionFilter.fair
  step history s query := match history with
    | [] => InteractionFilter.fair.map fun noise => (s && noise, s)
    | _ :: _ => PMF.pure ((if query then s else false), s)

/-- Queries use the previous reply and private state; local updates preserve that state. -/
def policy (privateCoin : PMF Bool) : Policy Bool Bool Bool where
  initial := privateCoin
  choose history c := PMF.pure ((match history with
    | [] => false
    | (_, reply) :: _ => Bool.xor reply c), c)
  update _ c _ _ := PMF.pure c

/-- Reached first query/reply pair with an uninformative false response. -/
def firstHistory : List (Bool × Bool) := [(false, false)]
/-- Complete newest-first branch with a false second query and response. -/
def secondHistory : List (Bool × Bool) := [(false, false), (false, false)]

private theorem first_draw : source.draw [] false = InteractionFilter.first := by
  rw [Source.draw, Source.filter_nil]
  rfl

private theorem first_filter :
    source.filter firstHistory = PMF.conditionalSnd InteractionFilter.first false := by
  rw [firstHistory, Source.filter_cons, first_draw]

private theorem second_filter :
    source.filter secondHistory = PMF.conditionalSnd InteractionFilter.first false := by
  change source.filter ((false, false) :: firstHistory) = _
  rw [Source.filter_cons]
  have hd : source.draw firstHistory false = (source.filter firstHistory).map (false, ·) := by
    rfl
  rw [hd]
  have he := PMF.conditionalSnd_bind_pair (PMF.pure false)
    (fun _ : Bool => source.filter firstHistory) false (by simp)
  simpa only [PMF.pure_bind, first_filter] using he

private def state (history : List (Bool × Bool)) : State Bool Bool Bool Bool :=
  ⟨history, false, false⟩

private theorem first_step (privateCoin : PMF Bool) :
    step (policy privateCoin) source (state []) = PMF.pure (state firstHistory) := by
  simp [step, policy, source, state, firstHistory, Function.comp_def]

private theorem second_step (privateCoin : PMF Bool) :
    step (policy privateCoin) source (state firstHistory) = PMF.pure (state secondHistory) := by
  simp [step, policy, source, state, firstHistory, secondHistory]

private theorem initial_support (privateCoin : PMF Bool) (hc : false ∈ privateCoin.support) :
    state [] ∈ (law (policy privateCoin) source 0).support := by
  simp only [law, ObservedProcess.stateLaw, PMF.bind_pure]
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨false, hc, ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨false, by simp [source, InteractionFilter.fair], rfl⟩

private theorem reached (privateCoin : PMF Bool) (hc : false ∈ privateCoin.support) :
    secondHistory ∈ ((law (policy privateCoin) source 2).map State.history).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨state secondHistory, ?_, rfl⟩
  rw [law_succ]
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨state firstHistory, ?_, by simp [second_step]⟩
  rw [law_succ]
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  exact ⟨state [], initial_support privateCoin hc, by simp [first_step]⟩

/-- The actual two-turn posterior is common to every private query law reaching this branch. -/
theorem actual_filter (privateCoin : PMF Bool) (hc : false ∈ privateCoin.support) :
    ((PMF.conditionalSnd ((law (policy privateCoin) source 2).map fun s =>
      (s.history, (s.policyState, s.sourceState))) secondHistory).map Prod.snd) true = 1 / 3 := by
  rw [source_posterior (policy privateCoin) source 2 secondHistory (reached privateCoin hc),
    second_filter]
  exact InteractionFilter.first_filter

-- The second query responds to the first reply, rather than following a fixed query schedule.
example : (policy InteractionFilter.fair).choose [(false, true)] false = PMF.pure (true, false) ∧
    (policy InteractionFilter.fair).choose firstHistory false = PMF.pure (false, false) := by
  constructor <;> rfl

/-- Fresh selection randomness changes private state before receiving the source response. -/
def freshPolicy : Policy Bool Bool Bool where
  initial := PMF.pure false
  choose history _ := InteractionFilter.fair.map fun fresh =>
    ((if history = [] then false else fresh), fresh)
  update _ c _ _ := PMF.pure c

-- The first actual private bit is freshly sampled during selection, despite pure initialization.
example : (law freshPolicy source 1).map State.policyState = InteractionFilter.fair := by
  simp [law, initialLaw, ObservedProcess.stateLaw, step, freshPolicy, source,
    PMF.map_bind, PMF.bind_map, Function.comp_def]

-- These executions have different private query distributions and the same reached source filter.
example :
    ((PMF.conditionalSnd ((law (policy InteractionFilter.fair) source 2).map fun s =>
      (s.history, (s.policyState, s.sourceState))) secondHistory).map Prod.snd) true = 1 / 3 ∧
    ((PMF.conditionalSnd ((law (policy (PMF.pure false)) source 2).map fun s =>
      (s.history, (s.policyState, s.sourceState))) secondHistory).map Prod.snd) true = 1 / 3 := by
  constructor
  · exact actual_filter InteractionFilter.fair (by simp [InteractionFilter.fair])
  · exact actual_filter (PMF.pure false) (by simp)

end CslibFrontierTests.InteractionProcess
