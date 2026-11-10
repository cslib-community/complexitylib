/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Finiteness

/-! # `finiteness` on bounds about discrete distributions, and `Game.succProbability_mono` -/

namespace CslibFrontierTests.PMFFiniteness

open scoped ENNReal

variable {α ι G : Type*}

-- The mass of an outcome.
example (p : PMF α) (a : α) : p a ≠ ∞ := by finiteness

-- The probability of an event, also as `< ∞`.
example (p : PMF α) (s : Set α) : p.toOuterMeasure s < ∞ := by finiteness

-- A finite sum of masses and event probabilities.
example (p : PMF α) (q : ι → PMF Bool) (s : Finset ι) (e : Set α) :
    p.toOuterMeasure e + ∑ i ∈ s, q i true ≠ ∞ := by finiteness

-- A union bound with a counting factor and an inverse cardinality.
example [Fintype G] [Nonempty G] (c n : ℕ) (p : PMF Bool) :
    (c : ℝ≥0∞) * n * (Fintype.card G : ℝ≥0∞)⁻¹ + 2 * p true ≠ ∞ := by finiteness

-- A side condition of `ENNReal.toReal_add`.
example (p q : PMF Bool) :
    (p true + q true).toReal = (p true).toReal + (q true).toReal :=
  ENNReal.toReal_add (by finiteness) (by finiteness)

-- An unbounded factor is outside the rules: `finiteness` fails instead of guessing.
example (x : ℝ≥0∞) (p : PMF α) (a : α) : x * p a ≠ ∞ ∨ True := by
  fail_if_success (left; finiteness)
  exact Or.inr trivial

-- A finite sum of event probabilities.
example (p : PMF α) (B : ι → Set α) (s : Finset ι) :
    ∑ j ∈ s, p.toOuterMeasure (B j) ≠ ∞ := by finiteness

-- A factor known finite from a hypothesis.
example (x : ℝ≥0∞) (hx : x ≠ ∞) (p : PMF α) (a : α) : x * p a ≠ ∞ := by finiteness

-- Comparing success probabilities reduces to comparing the masses of `true`.
example (g₁ g₂ : Cslib.Crypto.Game) (h : g₁ true ≤ g₂ true) :
    g₁.succProbability ≤ g₂.succProbability := by
  apply Cslib.Crypto.Game.succProbability_mono
  exact h

end CslibFrontierTests.PMFFiniteness
