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
# Hitting a point with a draw

Testing a draw from `μ` for equality with a fixed point `a` accepts with probability `μ a`
(`bind_pure_decide_eq_apply_true`, `map_decide_eq_apply_true`). The unprimed bind form and the
uniform form test `a = x`; `bind_pure_decide_eq_apply_true'` and the map form test `x = a`. For a
uniform draw from a nonempty finite type `α` this is `(Fintype.card α)⁻¹`
(`uniformOfFintype_bind_decide_eq_apply_true`). More generally, a Boolean test that accepts at most
one value accepts a uniform draw with probability at most `(Fintype.card α)⁻¹`
(`uniformOfFintype_bind_pure_apply_true_le`), and so does a set with at most one member
(`toOuterMeasure_uniformOfFintype_le_of_subsingleton`). Guessing games use this bound: an
adversary whose view is independent of a uniform secret guesses it with probability at most
`1 / |α|`, and so does any test comparing the secret with an injective image of the draw.

## Main results

* `Cslib.Probability.PMF.bind_pure_decide_eq_apply_true`,
  `Cslib.Probability.PMF.map_decide_eq_apply_true`: an equality test against a fixed point accepts
  with the point's probability.
* `Cslib.Probability.PMF.uniformOfFintype_bind_decide_eq_apply_true`: a uniform draw equals a
  fixed point with probability `(Fintype.card α)⁻¹`.
* `Cslib.Probability.PMF.uniformOfFintype_bind_pure_apply_true_le`: a test accepting at most one
  value accepts a uniform draw with probability at most `(Fintype.card α)⁻¹`.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_subsingleton`: a uniform draw lands
  in a set with at most one member with probability at most `(Fintype.card α)⁻¹`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

section Point

variable {β : Type*} [DecidableEq β]

/-- Testing a draw from `μ` for equality with a fixed `a` accepts with probability `μ a`. -/
theorem bind_pure_decide_eq_apply_true (μ : PMF β) (a : β) :
    (μ.bind fun x => PMF.pure (decide (a = x))) true = μ a := by
  rw [PMF.bind_apply, tsum_eq_single a fun x hx => by simp [Ne.symm hx]]
  simp

/-- `bind_pure_decide_eq_apply_true` with the comparison written the other way round. -/
theorem bind_pure_decide_eq_apply_true' (μ : PMF β) (a : β) :
    (μ.bind fun x => PMF.pure (decide (x = a))) true = μ a := by
  simpa only [@eq_comm _ a] using bind_pure_decide_eq_apply_true μ a

/-- `bind_pure_decide_eq_apply_true` for the pushforward of `μ` under the equality test. -/
theorem map_decide_eq_apply_true (μ : PMF β) (a : β) :
    (μ.map fun x => decide (x = a)) true = μ a := by
  rw [PMF.map, Function.comp_def, bind_pure_decide_eq_apply_true']

end Point

variable {α : Type*} [Fintype α] [Nonempty α]

/-- A uniform draw from `α` equals a fixed `a` with probability `(Fintype.card α)⁻¹`. -/
theorem uniformOfFintype_bind_decide_eq_apply_true [DecidableEq α] (a : α) :
    ((uniformOfFintype α).bind fun x => PMF.pure (decide (a = x))) true =
      (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [bind_pure_decide_eq_apply_true, uniformOfFintype_apply]

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

/-- A uniform draw from `α` lands in a set with at most one member with probability at most
`(Fintype.card α)⁻¹`. -/
theorem toOuterMeasure_uniformOfFintype_le_of_subsingleton {s : Set α} (hs : s.Subsingleton) :
    (uniformOfFintype α).toOuterMeasure s ≤ (Fintype.card α : ℝ≥0∞)⁻¹ := by
  obtain rfl | ⟨a, rfl⟩ := hs.eq_empty_or_singleton
  · simp
  · rw [PMF.toOuterMeasure_apply_singleton, uniformOfFintype_apply]

end Cslib.Probability.PMF
