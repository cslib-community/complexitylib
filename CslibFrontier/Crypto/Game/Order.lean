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
unfolding `succProbability` or discharging the finiteness of a probability mass by hand. A bound on
the distinguishing advantage of two experiments bounds one success probability by the other.

## Main results

* `Cslib.Crypto.Game.succProbability_mono`: success probability is monotone in the mass of
  `true`.
* `Cslib.Crypto.Game.succProbability_le_add_of_advantage_le`,
  `Cslib.Crypto.Game.coe_succProbability_le_add_of_advantage_le`: bound a game's success probability
  by another game's success probability plus their distinguishing advantage.
-/

public section

namespace Cslib.Crypto.Game

/-- Success probability is monotone in the mass of `true`. -/
theorem succProbability_mono {g₁ g₂ : Game} (h : g₁ true ≤ g₂ true) :
    g₁.succProbability ≤ g₂.succProbability :=
  ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) h

open scoped NNReal

/-- Bounding `advantage g₀ g₁ ≤ B` bounds `succProbability g₀ ≤ succProbability g₁ + B`. -/
theorem succProbability_le_add_of_advantage_le {g₀ g₁ : Game} {B : ℝ≥0}
    (h : advantage g₀ g₁ ≤ B) :
    succProbability g₀ ≤ succProbability g₁ + B := by
  have htri := advantage_triangle g₀ g₁ (PMF.pure false)
  rw [advantage_pure_false, advantage_pure_false, add_comm] at htri
  exact htri.trans (add_le_add le_rfl h)

/-- Real-valued version of `succProbability_le_add_of_advantage_le`. -/
theorem coe_succProbability_le_add_of_advantage_le {g₀ g₁ : Game} {B : ℝ}
    (h : (advantage g₀ g₁ : ℝ) ≤ B) :
    (succProbability g₀ : ℝ) ≤ (succProbability g₁ : ℝ) + B := by
  have htri := NNReal.coe_le_coe.mpr
    (succProbability_le_add_of_advantage_le (g₀ := g₀) (g₁ := g₁) le_rfl)
  rw [NNReal.coe_add] at htri
  exact htri.trans (add_le_add le_rfl h)

end Cslib.Crypto.Game
