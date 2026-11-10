/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Game.Statistical

/-!
# Finite statistical distance and all-event closeness

The finite-PMF metric is half the L1 distance. Its bounds imply the existing all-event `CloseTo`
relation, whose bind laws also apply when a continuation produces values in an infinite type.

## Main results

* `Cslib.Interactive.closeTo_of_dist_le`: finite statistical distance bounds all events.
* `Cslib.Interactive.closeTo_of_dist_le_ofReal`: real-valued finite statistical distance bounds
  `CloseTo` via `ENNReal.ofReal`.

This bridge is shared by finite-source hashing and approximate sampling. It is moved unchanged
from the Lyubashevsky efficiency module, which publicly reexports it.
-/

@[expose] public section

namespace Cslib.Interactive

open Probability Probability.PMF Crypto
open scoped ENNReal NNReal Cslib.Probability.PMF

/-- Finite-support statistical distance bounds `CloseTo` on all events. -/
theorem closeTo_of_dist_le {α : Type} [Fintype α] {μ ν : PMF α} {ε : ℝ≥0}
    (h : dist μ ν ≤ ε) : CloseTo μ ν ε := by
  classical
  refine Game.closeTo_of_advantage_decide_le fun E => ?_
  rw [Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  exact (PMF.dist_map_le μ ν _).trans h

/-- Real-valued finite-support statistical distance bounds `CloseTo` via `ENNReal.ofReal`,
using nonnegativity of `dist` to avoid a separate `0 ≤ ε` premise. -/
theorem closeTo_of_dist_le_ofReal {α : Type} [Fintype α] {μ ν : PMF α} {ε : ℝ}
    (h : dist μ ν ≤ ε) : CloseTo μ ν (ENNReal.ofReal ε) := by
  let ε' : ℝ≥0 := ⟨ε, dist_nonneg.trans h⟩
  rw [show ENNReal.ofReal ε = (ε' : ℝ≥0∞) from @ENNReal.ofReal_coe_nnreal ε']
  exact closeTo_of_dist_le (ε := ε') h

end Cslib.Interactive
