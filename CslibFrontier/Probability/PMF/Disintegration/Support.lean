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

end Cslib.Probability.PMF
