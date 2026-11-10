/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to Cslib/Crypto/Game.lean)

public import CslibFrontier.Crypto.Game

/-!
# Comparing success probabilities

A bound on the mass of `true` in one experiment transfers to its success probability, without
unfolding `succProbability` or discharging the finiteness of a probability mass by hand.

## Main results

* `Cslib.Crypto.Game.succProbability_mono`: success probability is monotone in the mass of
  `true`.
-/

public section

namespace Cslib.Crypto.Game

/-- Success probability is monotone in the mass of `true`. -/
theorem succProbability_mono {g₁ g₂ : Game} (h : g₁ true ≤ g₂ true) :
    g₁.succProbability ≤ g₂.succProbability :=
  ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) h

end Cslib.Crypto.Game
