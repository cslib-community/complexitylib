/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Interaction.Process
import CslibFrontier.Probability.PMF.Bind

/-!
# Actual private selection before a source response

Query selection runs against the actual policy state and saves the fresh private
state returned by `choose`. It neither samples the source nor replaces its hidden
state. The complete selection law factors through the actual history law, the
joint query/policy-state law and the source's recursive history filter. This is
derived from actual independent initialization and execution; no conditional
product or representation identity is a premise.

## Main definitions

* `Selected`: complete history, selected query, fresh policy state and unchanged source state.
* `Selected.policyView`: retain the selected policy checkpoint while erasing source state.
* `select`, `selectionLaw`: actual pre-response selection from a state or finite execution.

## Main results

* `selectionLaw_factorization`: the actual selected law uses the fixed source history filter.
* `selectionLaw_joint_factorization`: joint policy-view/source law from that same fixed filter.
-/

public section
noncomputable section
namespace Cslib.Probability.InteractionProcess

/-- The actual checkpoint after private query selection and before source sampling. -/
structure Selected (A B C S : Type) where
  /-- Complete newest-first query/reply history preceding the new selection. -/
  history : List (A × B)
  /-- Query chosen before the source response. -/
  query : A
  /-- Fresh private state returned jointly with the selected query. -/
  policyState : C
  /-- Actual source-private state, unchanged by selection. -/
  sourceState : S

variable {A B C S : Type}

/-- Retain the selected history, query and fresh policy storage, erasing only source state. -/
@[expose] def Selected.policyView (selected : Selected A B C S) : Selected A B C Unit :=
  ⟨selected.history, selected.query, selected.policyState, ()⟩

/-- Run the policy's actual private choice, retaining both newly selected storage
and the existing source state without making a source draw. -/
@[expose] def select (policy : Policy A B C) (state : State A B C S) :
    PMF (Selected A B C S) :=
  (policy.choose state.history state.policyState).map fun (query, nextPolicy) =>
    ⟨state.history, query, nextPolicy, state.sourceState⟩

/-- The pre-response selected law after the given number of actual interactions. -/
@[expose] def selectionLaw (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    PMF (Selected A B C S) :=
  (law policy source n).bind (select policy)

/-- Actual selection preserves the source history filter and the correlation
between the selected query and fresh policy state. No source response is sampled. -/
theorem selectionLaw_factorization (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    selectionLaw policy source n = (historyLaw policy source n).bind fun history =>
      (policy.queryLaw history).bind fun (query, nextPolicy) =>
        (source.filter history).map fun privateState =>
          (⟨history, query, nextPolicy, privateState⟩ : Selected A B C S) := by
  rw [selectionLaw, law_factorization]
  simp only [privateLaw, select, Policy.queryLaw, PMF.bind_bind, PMF.bind_map,
    PMF.map_bind, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro history _
  apply PMF.bind_congr_on_support
  intro c _
  exact PMF.bind_comm _ _ _

/-- The actual joint selected policy view and source state is obtained by sampling
the view, then the fixed source filter at its retained history. This supports
further coarsening of policy-side observations without another normalization proof. -/
theorem selectionLaw_joint_factorization
    (policy : Policy A B C) (source : Source A B S) (n : ℕ) :
    (selectionLaw policy source n).map
        (fun selected => (selected.policyView, selected.sourceState)) =
      ((selectionLaw policy source n).map Selected.policyView).bind fun view =>
        (source.filter view.history).map (view, ·) := by
  simp only [selectionLaw_factorization, PMF.map_bind, PMF.map_comp, Function.comp_def,
    Selected.policyView, Function.const_def, PMF.map_const, PMF.bind_bind, PMF.pure_bind]

end Cslib.Probability.InteractionProcess
