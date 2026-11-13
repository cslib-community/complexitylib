/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Map

/-!
# Composing multiplicative bounds on discrete distributions

## Main results

* `Cslib.Probability.PMF.mul_map_apply_le`: deterministic maps preserve lower density bounds.
* `Cslib.Probability.PMF.bind_apply_le_mul_of_le_mul`,
  `Cslib.Probability.PMF.mul_bind_apply_le_of_mul_le`: density bounds multiply under sequential
  sampling, including when the second distribution depends on the first result.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- A deterministic map preserves a pointwise lower density bound. -/
theorem mul_map_apply_le {p q : PMF α} {c : ℝ≥0∞} (h : ∀ a, c * q a ≤ p a)
    (f : α → β) (b : β) : c * q.map f b ≤ p.map f b := by
  classical
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun a => ?_
  split_ifs
  · exact h a
  · simp

/-- Upper density factors for the initial draw and every continuation multiply. -/
theorem bind_apply_le_mul_of_le_mul {p q : PMF α} {f g : α → PMF β} {c d : ℝ≥0∞}
    (hp : ∀ a, p a ≤ c * q a) (hf : ∀ a b, f a b ≤ d * g a b) (b : β) :
    p.bind f b ≤ (c * d) * q.bind g b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun a => ?_
  calc
    p a * f a b ≤ (c * q a) * (d * g a b) := mul_le_mul' (hp a) (hf a b)
    _ = c * d * (q a * g a b) := by ac_rfl

/-- Lower density factors for the initial draw and every continuation multiply. -/
theorem mul_bind_apply_le_of_mul_le {p q : PMF α} {f g : α → PMF β} {c d : ℝ≥0∞}
    (hp : ∀ a, c * q a ≤ p a) (hf : ∀ a b, d * g a b ≤ f a b) (b : β) :
    (c * d) * q.bind g b ≤ p.bind f b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun a => ?_
  calc
    c * d * (q a * g a b) = (c * q a) * (d * g a b) := by ac_rfl
    _ ≤ p a * f a b := mul_le_mul' (hp a) (hf a b)

end Cslib.Probability.PMF
