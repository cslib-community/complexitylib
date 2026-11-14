/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.ObservedProcess

/-!
# Mapping discrete hidden-state processes

An exact one-step simulation transports every finite-horizon state law. The map
may forget hidden state; neither injectivity nor termination is required.

## Main results

* `stateLaw_map`: exact one-step simulations transport finite-horizon state laws.
-/

public section
noncomputable section
namespace Cslib.Probability.ObservedProcess
variable {S T : Type}

/-- A map commuting with each actual transition commutes with the entire finite
state law, without any halting or injectivity premise. -/
theorem stateLaw_map (stepS : S → PMF S) (stepT : T → PMF T) (f : S → T)
    (hstep : ∀ s, (stepS s).map f = stepT (f s)) (n : ℕ) (s : S) :
    (stateLaw stepS n s).map f = stateLaw stepT n (f s) := by
  induction n with
  | zero => simp [stateLaw]
  | succ n ih =>
    rw [stateLaw, PMF.map_bind, stateLaw, ← ih, PMF.bind_map]
    simp only [hstep]
    rfl

end Cslib.Probability.ObservedProcess
