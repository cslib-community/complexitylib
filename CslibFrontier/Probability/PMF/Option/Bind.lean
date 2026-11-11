/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.Option

/-!
# Stochastic continuations of optional distributions

A successful-part density law composes with an arbitrary randomized continuation. The
failure contribution is retained separately, without conditioning or renormalization.

## Main results

* `bind_option_apply_of_some`: propagate a scaled successful-part law through `PMF.bind`.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

/-- If successful atoms of `μ` are `mass` times those of `ν`, any stochastic continuation has
the corresponding scaled successful contribution plus the actual failure contribution.
No positivity or finite-mass premise is needed. -/
theorem bind_option_apply_of_some {α β : Type*} (μ : PMF (Option α)) (ν : PMF α)
    (mass : ℝ≥0∞) (h : ∀ a, μ (some a) = mass * ν a)
    (k : Option α → PMF β) (b : β) :
    (μ.bind k) b = μ none * k none b + mass * (ν.bind (fun a => k (some a))) b := by
  rw [PMF.bind_apply, tsum_option_eq, PMF.bind_apply]
  simp_rw [h, mul_assoc]
  rw [ENNReal.tsum_mul_left]

end Cslib.Probability.PMF
