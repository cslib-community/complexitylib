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

/-!
# Statistical error under stateful oracle replacement

Replacing a handler costs at most the program's query budget times the per-unit statistical
error. The hypothesis compares joint reply/state laws from every identical starting state;
the conclusion retains the complete joint result/final-state law. No coupling, finite state
space or independence between calls is required.

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
  induction h generalizing s with
  | pure a n =>
    simpa only [runWith_pure] using (CloseTo.refl (PMF.pure (a, s))).mono (by positivity)
  | liftBind q cont n _ ih =>
    simp only [runWith_bind, runWith_query]
    have hc := (hstep q s).bind fun out _ => ih out.1 out.2
    simpa only [Nat.cast_add, add_mul, add_comm] using hc

end Cslib.OracleComp.IsCostBounded
