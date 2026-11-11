/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Feedback
import CslibFrontier.Probability.PMF.Bind

/-!
# One source turn of native feedback under a mixed environment

## Main results

* `Feedback.run_one_mixture`: one-query execution preserves a fresh oracle mixture.

There is no corresponding whole-policy mixture assertion for multiple adaptive
turns; fresh choices must be made separately at each actual query.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.Feedback
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution
variable {Private I : Type}

/-- At most one actual call is made. The terminal local computation does not
sample the environment a second time. Initial stopping is preserved as well. -/
theorem run_one_mixture (μ : PMF I) (envs : I → Environment Unit Private)
    (state : RuntimeControl.State) (channels : Unit → Channel Bool)
    (memory : Memory Unit Private) (request : RuntimeControl.State → List Bool) :
    run (fun q memory => μ.bind fun i => envs i q memory) 1 state channels memory request =
      μ.bind fun i => run (envs i) 1 state channels memory request := by
  by_cases hs : RuntimeControl.stopped state = true
  · simp [run, hs]
  · simp only [run, hs, Bool.false_eq_true, ite_false,
      PMF.monad_bind_eq_bind, PMF.bind_bind]

end Cslib.Probability.StochasticOracle.NativeRetention.Feedback
