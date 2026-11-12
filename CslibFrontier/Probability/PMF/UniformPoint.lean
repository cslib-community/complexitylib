/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bool

/-!
# Hitting a point with a uniform draw

A uniform draw from a nonempty finite type `α` equals a fixed point `a` with probability
`(Fintype.card α)⁻¹` (`uniformOfFintype_bind_decide_eq_apply_true`). More generally, a Boolean
test that accepts at most one value accepts a uniform draw with probability at most
`(Fintype.card α)⁻¹` (`uniformOfFintype_bind_pure_apply_true_le`). Guessing games use this
bound: an adversary whose view is independent of a uniform secret guesses it with probability at
most `1 / |α|`, and so does any test comparing the secret with an injective image of the draw.

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_bind_decide_eq_apply_true`: a uniform draw equals a
  fixed point with probability `(Fintype.card α)⁻¹`.
* `Cslib.Probability.PMF.uniformOfFintype_bind_pure_apply_true_le`: a test accepting at most one
  value accepts a uniform draw with probability at most `(Fintype.card α)⁻¹`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*} [Fintype α] [Nonempty α]

/-- A uniform draw from `α` equals a fixed `a` with probability `(Fintype.card α)⁻¹`. -/
theorem uniformOfFintype_bind_decide_eq_apply_true [DecidableEq α] (a : α) :
    ((uniformOfFintype α).bind fun x => PMF.pure (decide (a = x))) true =
      (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [PMF.bind_apply, tsum_eq_single a fun x hx => by simp [Ne.symm hx]]
  simp [uniformOfFintype_apply]

/-- A Boolean test that accepts at most one value accepts a uniform draw from `α` with
probability at most `(Fintype.card α)⁻¹`. -/
theorem uniformOfFintype_bind_pure_apply_true_le {E : α → Bool}
    (hE : {x | E x = true}.Subsingleton) :
    ((uniformOfFintype α).bind fun x => PMF.pure (E x)) true ≤ (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  by_cases h : ∃ a, E a = true
  · obtain ⟨a, ha⟩ := h
    rw [← uniformOfFintype_bind_decide_eq_apply_true a]
    exact map_true_mono _ fun x _ hx => decide_eq_true (hE ha hx)
  · simp [not_exists.mp h]

end Cslib.Probability.PMF
