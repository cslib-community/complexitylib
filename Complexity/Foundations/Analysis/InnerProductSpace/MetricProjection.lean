/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`)

public import Complexity.Init
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Metric projection onto a complete convex set

For a nonempty complete convex set `K` in a real inner product space, every point `y` has a
unique nearest point in `K` (`exists_norm_eq_iInf_of_complete_convex` in Mathlib).
`metricProjection K y` chooses it. Mathlib names this map only for subspaces
(`Submodule.orthogonalProjection`), so here it is defined for arbitrary convex sets. When `K` is
empty, incomplete or nonconvex the value is unspecified and every lemma below assumes all three
hypotheses.

## Main definitions

* `Cslib.metricProjection K y`: the nearest point of `K` to `y`.

## Main results

* `Cslib.metricProjection_mem`, `Cslib.norm_sub_metricProjection`: the projection lies in `K` and
  attains `⨅ w : K, ‖y - w‖`.
* `Cslib.inner_sub_metricProjection_le_zero`: the variational inequality
  `⟪y - Π y, z - Π y⟫ ≤ 0` for `z ∈ K`.
* `Cslib.metricProjection_eq_iff`: a point of `K` is the projection iff it satisfies the
  variational inequality.
* `Cslib.metricProjection_eq_self`: points of `K` are fixed.
* `Cslib.norm_metricProjection_sub_le`: the Pythagorean inequality `‖Π y - z‖ ≤ ‖y - z‖` for
  `z ∈ K`, [Hazan2022] Theorem 2.1.
* `Cslib.lipschitzWith_metricProjection`: the projection is nonexpansive.

## References

* [Hazan2022]
-/

public section

open scoped RealInnerProductSpace

namespace Cslib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The metric projection onto `K`: a point of `K` nearest to `y`. It is well defined (and unique)
when `K` is nonempty, complete and convex; otherwise its value is unspecified. -/
noncomputable def metricProjection (K : Set E) (y : E) : E :=
  open Classical in
  if h : ∃ x ∈ K, ‖y - x‖ = ⨅ w : K, ‖y - w‖ then h.choose else y

variable {K : Set E}

theorem metricProjection_spec (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) (y : E) :
    metricProjection K y ∈ K ∧ ‖y - metricProjection K y‖ = ⨅ w : K, ‖y - w‖ := by
  have h := exists_norm_eq_iInf_of_complete_convex hne hc hK y
  simp only [metricProjection, h, ↓reduceDIte]
  exact h.choose_spec

theorem metricProjection_mem (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) (y : E) :
    metricProjection K y ∈ K :=
  (metricProjection_spec hne hc hK y).1

theorem norm_sub_metricProjection (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K)
    (y : E) : ‖y - metricProjection K y‖ = ⨅ w : K, ‖y - w‖ :=
  (metricProjection_spec hne hc hK y).2

/-- The variational inequality characterizing the projection. -/
theorem inner_sub_metricProjection_le_zero (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) (y : E) {z : E} (hz : z ∈ K) :
    ⟪y - metricProjection K y, z - metricProjection K y⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hK (metricProjection_mem hne hc hK y)).mp
    (norm_sub_metricProjection hne hc hK y) z hz

/-- A point of `K` is the projection of `y` iff it satisfies the variational inequality. -/
theorem metricProjection_eq_iff (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K)
    {y x : E} (hx : x ∈ K) :
    metricProjection K y = x ↔ ∀ z ∈ K, ⟪y - x, z - x⟫ ≤ 0 := by
  refine ⟨fun h => h ▸ fun z hz => inner_sub_metricProjection_le_zero hne hc hK y hz,
    fun h => ?_⟩
  set p := metricProjection K y
  have h1 : ⟪y - p, x - p⟫ ≤ 0 := inner_sub_metricProjection_le_zero hne hc hK y hx
  have h2 := h p (metricProjection_mem hne hc hK y)
  have hsum : ‖p - x‖ ^ 2 = ⟪y - p, x - p⟫ + ⟪y - x, p - x⟫ := by
    rw [← real_inner_self_eq_norm_sq, show y - x = (y - p) + (p - x) by abel, inner_add_left,
      show x - p = -(p - x) by abel, inner_neg_right]
    ring
  have hp : ‖p - x‖ ^ 2 ≤ 0 := by linarith
  have : ‖p - x‖ = 0 := by nlinarith [norm_nonneg (p - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Pythagoras for projections ([Hazan2022] Theorem 2.1): projecting onto `K` does not increase
the distance to any point of `K`. -/
theorem norm_metricProjection_sub_le (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) (y : E) {z : E} (hz : z ∈ K) :
    ‖metricProjection K y - z‖ ≤ ‖y - z‖ := by
  set x := metricProjection K y
  have h := inner_sub_metricProjection_le_zero hne hc hK y hz
  have hsq : ‖y - z‖ ^ 2 = ‖y - x‖ ^ 2 + ‖x - z‖ ^ 2 - 2 * ⟪y - x, z - x⟫ := by
    rw [show y - z = (y - x) - (z - x) by abel, norm_sub_sq_real, norm_sub_rev z x]
    ring
  have h2 : ‖x - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by nlinarith [sq_nonneg ‖y - x‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- Points of `K` are fixed by the projection. -/
theorem metricProjection_eq_self (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K)
    {y : E} (hy : y ∈ K) : metricProjection K y = y := by
  have h := norm_metricProjection_sub_le hne hc hK y hy
  rw [sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The projection is nonexpansive: `‖Π y - Π y'‖ ≤ ‖y - y'‖`. -/
theorem norm_metricProjection_sub_metricProjection_le (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) (y y' : E) :
    ‖metricProjection K y - metricProjection K y'‖ ≤ ‖y - y'‖ := by
  set p := metricProjection K y
  set p' := metricProjection K y'
  have h1 : ⟪y - p, p' - p⟫ ≤ 0 :=
    inner_sub_metricProjection_le_zero hne hc hK y (metricProjection_mem hne hc hK y')
  have h2 : ⟪y' - p', p - p'⟫ ≤ 0 :=
    inner_sub_metricProjection_le_zero hne hc hK y' (metricProjection_mem hne hc hK y)
  -- `‖p - p'‖² ≤ ⟪y - y', p - p'⟫ ≤ ‖y - y'‖ ‖p - p'‖`
  have hkey : ‖p - p'‖ ^ 2 ≤ ⟪y - y', p - p'⟫ := by
    have e : ⟪y - y', p - p'⟫ = ‖p - p'‖ ^ 2 - ⟪y - p, p' - p⟫ - ⟪y' - p', p - p'⟫ := by
      rw [← real_inner_self_eq_norm_sq,
        show y - y' = (y - p) - (y' - p') + (p - p') by abel, inner_add_left, inner_sub_left,
        show p - p' = -(p' - p) by abel, inner_neg_right, inner_neg_right]
      ring
    linarith
  have hcs := real_inner_le_norm (y - y') (p - p')
  rcases (norm_nonneg (p - p')).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact norm_nonneg _
  · nlinarith

/-- The projection is `1`-Lipschitz. -/
theorem lipschitzWith_metricProjection (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) : LipschitzWith 1 (metricProjection K) :=
  LipschitzWith.of_dist_le_mul fun y y' => by
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
      norm_metricProjection_sub_metricProjection_le hne hc hK y y'

end Cslib
