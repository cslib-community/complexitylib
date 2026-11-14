/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Coin

/-!
# Complementing a Bernoulli coin

Negating the sampled Boolean complements its success parameter, using the
existing central symmetry of the unit interval. This includes parameters zero and one.
-/

public section
namespace Cslib.Probability.PMF
open scoped unitInterval

/-- Negation sends a coin with parameter `p` to a coin with parameter `1 - p`. -/
theorem coin_map_not (p : I) : (coin p).map Bool.not = coin (σ p) := by
  ext b
  cases b <;> simp [PMF.map_apply, coin_apply, unitInterval.coe_symm_eq]

end Cslib.Probability.PMF
