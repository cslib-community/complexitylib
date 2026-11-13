/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Security
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Languages.Probabilistic.Simulation.CloseTo

/-!
# Statistical error under stateful oracle replacement

Replacing a handler costs at most the program's query budget times the per-unit statistical
error. The hypothesis compares joint reply/state laws from every identical starting state;
the conclusion retains the complete joint result/final-state law. No coupling, finite state
space or independence between calls is required. This is the identity-relation case of
`OracleComp.closeTo_run_interpret_simulation`, which also relates the two states through a
probabilistic map.

The existing `OracleComp.IsCostBounded` allows calls that cost zero. Such calls may still change
the shared state, but their handlers must be statistically identical. For example, charging only
signing calls leaves shared hash-cache operations uncharged without removing their effects.

## Main results

* `Cslib.OracleComp.IsCostBounded.closeTo_runWith`: cost-weighted stateful replacement.
-/

public section

namespace Cslib.OracleComp.IsCostBounded

open Interactive Probability
open scoped ENNReal

/-- Pointwise replacement of joint reply/state laws accumulates error according to the existing
query-cost budget. The premise holds for every query and every starting state, including states
outside either execution's support. The final state is retained in the conclusion. -/
theorem closeTo_runWith {ι α σ : Type} {spec : OracleSpec ι} {cost : ι → ℕ}
    {program : OracleComp spec α} {n : ℕ} (h : IsCostBounded cost program n)
    {left right : (q : ι) → StateT σ PMF (spec q)} {ε : ℝ≥0∞}
    (hstep : ∀ q s, CloseTo (left q s) (right q s) (cost q * ε)) (s : σ) :
    CloseTo (runWith left program s) (runWith right program s) (n * ε) := by
  have hstep' : ∀ q s, CloseTo ((left q s).bind fun x => (PMF.pure x.2).map (x.1, ·))
      ((PMF.pure s).bind (right q)) (cost q * ε) := fun q s => by
    simpa only [PMF.pure_map, PMF.pure_bind, Prod.mk.eta, PMF.bind_pure] using hstep q s
  simpa only [runWith, PMF.pure_map, PMF.pure_bind, Prod.mk.eta, PMF.bind_pure] using
    closeTo_run_interpret_simulation cost left right PMF.pure ε hstep' program h s

end Cslib.OracleComp.IsCostBounded
