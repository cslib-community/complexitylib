/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
import Batteries.Data.Fin.Lemmas

/-!
# The first successful IID trial

Map `Fin.findSome?` over a finite tuple of independent `Option`-valued trials. Failure means that
every trial returned `none`, so its mass is the one-trial failure mass raised to the tuple length.

## Main definitions

This module adds no definitions; it composes `PMF.iid` with `Fin.findSome?`.

## Main results

* `Cslib.Probability.PMF.map_findSome_iid_apply_none`: exact failure mass of the first-success
  map over IID trials.

## References

The identity is the elementary product rule for independent failures.
-/

public section

namespace Cslib.Probability.PMF

variable {α : Type*}

/-- The first-success map over `K` IID `Option`-valued trials fails with mass `μ none ^ K`. -/
theorem map_findSome_iid_apply_none (μ : PMF (Option α)) (K : ℕ) :
    (iid μ K).map Fin.findSome? none = (μ none) ^ K := by
  rw [PMF.map_apply, tsum_eq_single (fun _ : Fin K => (none : Option α))]
  · simp
  · intro attempts hne
    split_ifs with h
    · exact (hne (funext (Fin.findSome?_eq_none_iff.mp h))).elim
    · rfl

end Cslib.Probability.PMF
