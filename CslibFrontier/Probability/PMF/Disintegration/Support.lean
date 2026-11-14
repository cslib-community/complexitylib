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
# Supported atoms of discrete posteriors

A positive-mass observation conditions onto its actual fiber. Null observations
retain the prior completion and are deliberately excluded from this claim.

## Main results

* `mem_support_of_posterior`: positive observed atoms retain only prior-supported fiber points.
* `support_posterior_subset`: every posterior completion stays within prior support.
-/

public section
noncomputable section
namespace Cslib.Probability.PMF
variable {S H : Type*}

/-- Supported posterior points at positive-mass observations belong to the
original prior support and to the exact observed fiber. -/
theorem mem_support_of_posterior (prior : PMF S) (observe : S → H) (h : H)
    (hh : h ∈ (prior.map observe).support) (s : S)
    (hs : s ∈ (posterior prior observe h).support) : s ∈ prior.support ∧ observe s = h := by
  have hn : prior.map observe h * posterior prior observe h s ≠ 0 := mul_ne_zero hh hs
  rw [posterior_factor] at hn
  split_ifs at hn with he
  · exact ⟨hn, he⟩
  · exact (hn rfl).elim

/-- Conditioning never creates an unsupported private state. This includes null
observations, whose completion is the original prior rather than a new point mass. -/
theorem support_posterior_subset (prior : PMF S) (observe : S → H) (h : H) :
    (posterior prior observe h).support ⊆ prior.support := by
  classical
  intro s hs
  by_cases hh : h ∈ (prior.map observe).support
  · exact (mem_support_of_posterior prior observe h hh s hs).1
  · have hp : h ∉ (prior.bind fun s => PMF.pure (observe s)).support := hh
    simpa only [posterior, dite_eq_right hp] using hs

end Cslib.Probability.PMF
