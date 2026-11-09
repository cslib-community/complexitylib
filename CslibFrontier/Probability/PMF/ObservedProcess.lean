/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Disintegration
import Mathlib.Tactic

/-!
# Behavioral representation of an observed discrete hidden-state process

The hidden process is executed first. Its actual path laws construct the posterior
at each complete observation history, including harmless null-history completion.
The resulting history-dependent behavioral kernels have exactly the observed
path laws. Private state and observation types can be infinite; these remain
PMF, rather than general measurable-space, semantics.

## Main results

* `public_eq_observed`: equality of entire observed prefix laws.
* `private_hidden`: the private path retains the original state marginal.
* `public_current`: the latest public observation has the actual state observation law.
-/

public section
noncomputable section
namespace Cslib.Probability.ObservedProcess
variable {S H : Type}

/-- Current private state and the complete public observation history, newest first. -/
structure Path (S H : Type) where
  /-- Hidden state, never replaced by a fresh independent sample. -/
  hidden : S
  /-- Observations, including the initial one. -/
  observations : List H

/-- Actual hidden-state law after n transitions. -/
@[expose] def stateLaw (step : S → PMF S) : ℕ → S → PMF S
  | 0, s => PMF.pure s
  | n + 1, s => (stateLaw step n s).bind step

/-- Actual hidden state together with all observed states, retaining correlations. -/
@[expose] def privateLaw (step : S → PMF S) (observe : S → H) : ℕ → S → PMF (Path S H)
  | 0, s => PMF.pure ⟨s, [observe s]⟩
  | n + 1, s => (privateLaw step observe n s).bind fun path =>
    (step path.hidden).map fun next => ⟨next, observe next :: path.observations⟩

/-- The behavioral next-observation-history kernel derived from the actual private
prefix law. It conditions on the complete observed prefix, not merely its last item. -/
@[expose] def nextHistory (step : S → PMF S) (observe : S → H) (n : ℕ) (s : S)
    (history : List H) : PMF (List H) :=
  (PMF.posterior (privateLaw step observe n s) Path.observations history).bind fun path =>
    (step path.hidden).map fun next => observe next :: history

/-- Public behavioral process using the constructed history-dependent kernels. -/
@[expose] def publicLaw (step : S → PMF S) (observe : S → H) : ℕ → S → PMF (List H)
  | 0, s => PMF.pure [observe s]
  | n + 1, s => (publicLaw step observe n s).bind (nextHistory step observe n s)

/-- Retaining observed paths does not change the original private-state law. -/
theorem private_hidden (step : S → PMF S) (observe : S → H) (n : ℕ) (s : S) :
    (privateLaw step observe n s).map Path.hidden = stateLaw step n s := by
  induction n with
  | zero => simp [privateLaw, stateLaw]
  | succ n ih =>
    simp only [privateLaw, stateLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [← ih, PMF.bind_map]
    congr 1
    funext path
    exact PMF.map_id _

/-- The constructed behavioral kernels preserve the complete public path law,
without a representation hypothesis or finite private-state/observation assumption. -/
theorem public_eq_observed (step : S → PMF S) (observe : S → H) (n : ℕ) (s : S) :
    publicLaw step observe n s = (privateLaw step observe n s).map Path.observations := by
  induction n with
  | zero => simp [publicLaw, privateLaw]
  | succ n ih =>
    rw [publicLaw, ih]
    change ((privateLaw step observe n s).map Path.observations).bind
      (fun history => (PMF.posterior (privateLaw step observe n s) Path.observations history).bind
        (fun path => (step path.hidden).map (fun next => observe next :: history))) = _
    rw [PMF.posterior_bind]
    simp [privateLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The latest observation is the actual state observation, while the preceding
observations remain available to the behavioral kernel. -/
theorem public_current (step : S → PMF S) (observe : S → H) (n : ℕ) (s : S) :
    (publicLaw step observe n s).map (fun history => history.headD (observe s)) =
      (stateLaw step n s).map observe := by
  rw [public_eq_observed]
  cases n with
  | zero => simp [privateLaw, stateLaw]
  | succ n =>
    rw [stateLaw, ← private_hidden step observe n s, PMF.bind_map]
    simp [privateLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

end Cslib.Probability.ObservedProcess
