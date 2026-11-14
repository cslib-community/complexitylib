/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Interaction
public import CslibFrontier.Probability.PMF.ObservedProcess
public import CslibFrontier.Probability.PMF.SequentialHistory
public import CslibFrontier.Probability.StochasticDomination.Adapted
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic

/-!
# Iterated filtering of actual private interactions

The policy and source start from separately sampled private states. Each actual
transition samples a policy query, obtains a complete source reply and processes
that reply locally. The state retains the complete newest-first query/reply
history. Source filters are computed from the source and that history alone;
policy filters also use the policy's private sampler and local update.

`law_factorization` derives the complete actual state law from explicit public
histories and the two recursive filters. `source_posterior` identifies the source
filter at every reached actual history, uniformly across private policies.

This is a discrete finite-interaction model. It does not assume a posterior
product as input and does not model unbounded silent native computation.

## Main definitions

* `Source`, `Policy`, `State`: separated access and actual private storage.
* `law`: actual execution from independent initial samples.
* `Source.filter`, `Policy.filter`: recursive complete-history beliefs.
* `historyLaw`: explicit sequential history law with a policy-independent source kernel.

## Main results

* `law_factorization`, `histories_law`: complete actual execution and history laws.
* `private_posterior`, `source_posterior`: derived supported conditional private states.
-/

public section
noncomputable section
namespace Cslib.Probability.InteractionProcess

/-- Shared private source, with a complete reply containing every public observation. -/
structure Source (A B S : Type) where
  /-- Initial private source law, sampled independently of policy state. -/
  initial : PMF S
  /-- Actual reply and next source state, with no access to policy-private state. -/
  step : List (A × B) → S → A → PMF (B × S)

/-- Actual private query sampling and local response processing. -/
structure Policy (A B C : Type) where
  /-- Initial private policy law, sampled independently of source state. -/
  initial : PMF C
  /-- Query selection also retains its newly sampled private storage and coins. -/
  choose : List (A × B) → C → PMF (A × C)
  /-- Private processing sees the query and complete reply, but not source-private state. -/
  update : List (A × B) → C → A → B → PMF C

/-- Actual public history together with the two hidden private states. -/
structure State (A B C S : Type) where
  /-- Newest-first complete query/reply history. -/
  history : List (A × B)
  /-- Policy-private storage, including retained private coins. -/
  policyState : C
  /-- Source-private storage. -/
  sourceState : S

variable {A B C S : Type}

/-- Actual independent initialization, without a supplied posterior-factorization premise. -/
@[expose] def initialLaw (policy : Policy A B C) (source : Source A B S) :
    PMF (State A B C S) :=
  policy.initial.bind fun c => source.initial.map fun s => ⟨[], c, s⟩

/-- One actual interaction, retaining private-state correlations through the complete reply. -/
@[expose] def step (policy : Policy A B C) (source : Source A B S)
    (state : State A B C S) : PMF (State A B C S) :=
  (policy.choose state.history state.policyState).bind fun (query, selectedState) =>
    (source.step state.history state.sourceState query).bind fun (reply, nextSource) =>
      (policy.update state.history selectedState query reply).map fun nextPolicy =>
        ⟨(query, reply) :: state.history, nextPolicy, nextSource⟩

/-- Actual execution from its random independent initialization, using the existing
hidden-state process. -/
@[expose] def law (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    PMF (State A B C S) :=
  (initialLaw policy source).bind (ObservedProcess.stateLaw (step policy source) n)

@[simp] theorem law_zero (policy : Policy A B C) (source : Source A B S) :
    law policy source 0 = initialLaw policy source := by
  simp only [law, ObservedProcess.stateLaw, PMF.bind_pure]

/-- The actual mixed-initial process advances by its actual transition. -/
theorem law_succ (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    law policy source (n + 1) = (law policy source n).bind (step policy source) := by
  simp only [law, ObservedProcess.stateLaw, PMF.bind_bind]

/-- Source belief from a complete history, with the usual null-observation completion. -/
def Source.filter (source : Source A B S) : List (A × B) → PMF S
  | [] => source.initial
  | (query, reply) :: history =>
    PMF.conditionalSnd ((source.filter history).bind fun s => source.step history s query) reply

/-- The source's actual next reply and next private state under its history filter. -/
@[expose] def Source.draw (source : Source A B S) (history : List (A × B)) (query : A) :
    PMF (B × S) :=
  (source.filter history).bind fun s => source.step history s query

@[simp] theorem Source.filter_nil (source : Source A B S) : source.filter [] = source.initial := by
  simp only [Source.filter]

/-- The common source filter updates using only the complete query/reply observation. -/
@[simp] theorem Source.filter_cons (source : Source A B S) (history : List (A × B))
    (query : A) (reply : B) :
    source.filter ((query, reply) :: history) =
      PMF.conditionalSnd (source.draw history query) reply := by
  simp only [Source.filter, Source.draw]

/-- Private policy belief after each complete query/reply history. -/
def Policy.filter (policy : Policy A B C) : List (A × B) → PMF C
  | [] => policy.initial
  | (query, reply) :: history =>
    (PMF.conditionalSnd ((policy.filter history).bind (policy.choose history)) query).bind fun c =>
        policy.update history c query reply

/-- Actual query paired with the policy state that selected it, under the history filter. -/
@[expose] def Policy.queryLaw (policy : Policy A B C) (history : List (A × B)) : PMF (A × C) :=
  (policy.filter history).bind (policy.choose history)

@[simp] theorem Policy.filter_nil (policy : Policy A B C) : policy.filter [] = policy.initial := by
  simp only [Policy.filter]

/-- Policy filtering conditions on its chosen query, then processes the actual reply. -/
@[simp] theorem Policy.filter_cons (policy : Policy A B C) (history : List (A × B))
    (query : A) (reply : B) :
    policy.filter ((query, reply) :: history) =
      (PMF.conditionalSnd (policy.queryLaw history) query).bind fun c =>
        policy.update history c query reply := by
  simp only [Policy.filter, Policy.queryLaw]

/-- Candidate conditional private-state product; the execution theorem derives this invariant. -/
@[expose] def privateLaw (policy : Policy A B C) (source : Source A B S)
    (history : List (A × B)) : PMF (C × S) :=
  (policy.filter history).bind fun c => (source.filter history).map (c, ·)

/-- Query/reply kernel with one common source response law across policies. -/
@[expose] def recordKernel (policy : Policy A B C) (source : Source A B S)
    (history : List (A × B)) : PMF (A × B) :=
  ((policy.queryLaw history).map Prod.fst).bind fun query =>
    ((source.draw history query).map Prod.fst).map (query, ·)

/-- Sequential public histories generated by the explicit filtered query/reply kernel. -/
@[expose] def historyLaw (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    PMF (List (A × B)) :=
  (PMF.seqProcess (fun _ h => recordKernel policy source (PMF.seqHistory h)) n).map PMF.seqHistory

@[simp] theorem historyLaw_zero (policy : Policy A B C) (source : Source A B S) :
    historyLaw policy source 0 = PMF.pure [] := by
  simp only [historyLaw, PMF.seqProcess, PMF.pure_map, PMF.seqHistory_zero]

/-- The explicit filtered history process appends one actual query/reply. -/
theorem historyLaw_succ (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    historyLaw policy source (n + 1) = (historyLaw policy source n).bind fun history =>
      (recordKernel policy source history).map fun record => record :: history := by
  conv_lhs => rw [historyLaw, PMF.seqProcess, PMF.map_bind]
  simp only [PMF.map_comp, PMF.seqHistory_snoc, Function.comp_def]
  rw [historyLaw, PMF.bind_map]
  rfl

/-- Actual interaction preserves the filtered private product and records the
complete public observation. No conditional product is supplied as a hypothesis. -/
theorem step_privateLaw (policy : Policy A B C) (source : Source A B S)
    (history : List (A × B)) :
    (privateLaw policy source history).bind (fun (c, s) => step policy source ⟨history, c, s⟩) =
      (recordKernel policy source history).bind fun record =>
        (privateLaw policy source (record :: history)).map fun (c, s) =>
          (⟨record :: history, c, s⟩ : State A B C S) := by
  let embed : ((A × B) × (C × S)) → State A B C S :=
    fun ⟨record, ⟨c, s⟩⟩ => ⟨record :: history, c, s⟩
  have he : (privateLaw policy source history).bind
      (fun (c, s) => step policy source ⟨history, c, s⟩) =
      ((PMF.queryResponse (policy.queryLaw history) (source.draw history)).bind
        (fun ⟨⟨query, reply⟩, ⟨localState, sourceState⟩⟩ =>
          (policy.update history localState query reply).map fun next =>
            ((query, reply), (next, sourceState)))).map embed := by
    simp only [privateLaw, step, PMF.queryResponse, Policy.queryLaw, Source.draw,
      PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, embed]
    apply PMF.bind_congr_on_support
    intro c _
    exact PMF.bind_comm _ _ _
  rw [he, PMF.queryResponse_update_disintegrate (policy.queryLaw history)
    (source.draw history) (fun query reply c => policy.update history c query reply), PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro record _
  rcases record with ⟨query, reply⟩
  simp only [privateLaw, Policy.filter_cons, Source.filter_cons,
    PMF.map_comp, PMF.map_bind, Function.comp_def, embed]

/-- Full actual finite execution factors through the explicit public history law
and the recursively derived policy/source private product. -/
theorem law_factorization (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    law policy source n = (historyLaw policy source n).bind fun history =>
      (privateLaw policy source history).map fun (c, s) =>
        (⟨history, c, s⟩ : State A B C S) := by
  induction n with
  | zero =>
    rw [law_zero, historyLaw_zero, PMF.pure_bind]
    simp only [initialLaw, privateLaw, Policy.filter_nil, Source.filter_nil,
      PMF.map_bind, PMF.map_comp, Function.comp_def]
  | succ n ih =>
    rw [law_succ, ih, PMF.bind_bind]
    calc
      _ = (historyLaw policy source n).bind (fun history =>
          (recordKernel policy source history).bind fun record =>
            (privateLaw policy source (record :: history)).map fun (c, s) =>
              (⟨record :: history, c, s⟩ : State A B C S)) := by
        apply PMF.bind_congr_on_support
        intro history _
        rw [PMF.bind_map]
        exact step_privateLaw policy source history
      _ = _ := by
        rw [historyLaw_succ, PMF.bind_bind]
        apply PMF.bind_congr_on_support
        intro history _
        rw [PMF.bind_map]
        rfl

/-- The explicit filtered history process is exactly the actual complete interaction history. -/
theorem histories_law (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    (law policy source n).map State.history = historyLaw policy source n := by
  rw [law_factorization, PMF.map_bind]
  have he (history : List (A × B)) :
      ((privateLaw policy source history).map (fun (c, s) =>
        (⟨history, c, s⟩ : State A B C S))).map State.history = PMF.pure history := by
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  simp only [he, PMF.bind_pure]

/-- Conditioning actual execution on a reached complete history yields the derived
private-state product, rather than assuming that product as a representation premise. -/
theorem private_posterior (policy : Policy A B C) (source : Source A B S)
    (n : ℕ) (history : List (A × B))
    (hh : history ∈ ((law policy source n).map State.history).support) :
    PMF.conditionalSnd ((law policy source n).map fun state =>
      (state.history, (state.policyState, state.sourceState))) history =
        privateLaw policy source history := by
  rw [histories_law] at hh
  have he : (law policy source n).map (fun state =>
      (state.history, (state.policyState, state.sourceState))) =
      (historyLaw policy source n).bind fun h => (privateLaw policy source h).map (h, ·) := by
    rw [law_factorization, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
  rw [he]
  exact PMF.conditionalSnd_bind_pair _ _ history hh

/-- The source posterior at every supported actual complete history depends only on
that history and the source, uniformly over private policies and finite horizons. -/
theorem source_posterior (policy : Policy A B C) (source : Source A B S)
    (n : ℕ) (history : List (A × B))
    (hh : history ∈ ((law policy source n).map State.history).support) :
    (PMF.conditionalSnd ((law policy source n).map fun state =>
      (state.history, (state.policyState, state.sourceState))) history).map Prod.snd =
        source.filter history := by
  rw [private_posterior policy source n history hh]
  simp only [privateLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_id _

end Cslib.Probability.InteractionProcess
