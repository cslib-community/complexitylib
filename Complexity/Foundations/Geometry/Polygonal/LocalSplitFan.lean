/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.Germs
public import Complexity.Foundations.Geometry.Polygonal.Segment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Straight fans inside a round local neighborhood

From any point strictly inside a real planar ball, the segments to distinct points on its
boundary meet only at that interior point. In particular their outgoing arguments are
distinct. Neither the interior point nor the circle is required to have rational coordinates.

An affine real coordinate separates two such fans and their connector when each block lies
strictly beyond its own fan center. These are direct statements about all real parameters;
they do not assert that a given circular block has such separating data.
-/

public section

namespace Cslib.Polygonal

private theorem lineMap_mem_ball {z a b : ℂ} {ρ t : ℝ}
    (ha : a ∈ Metric.ball z ρ) (hb : b ∈ Metric.closedBall z ρ)
    (ht : t ∈ Set.Ico 0 1) : AffineMap.lineMap a b t ∈ Metric.ball z ρ := by
  have hρ : ρ ≠ 0 := ne_of_gt ((dist_nonneg : 0 ≤ dist a z).trans_lt ha)
  rw [← interior_closedBall z hρ] at ha ⊢
  rw [AffineMap.lineMap_apply_module]
  exact (convex_closedBall z ρ).combo_interior_self_mem_interior ha hb
    (sub_pos.mpr ht.2) ht.1 (sub_add_cancel 1 t)

/-- A spoke from an interior point meets the cut circle only at its boundary end.
The parameter is an arbitrary real number in the full unit interval. -/
theorem lineMap_sphere_parameter {z a b : ℂ} {ρ t : ℝ}
    (ha : a ∈ Metric.ball z ρ) (hb : b ∈ Metric.sphere z ρ)
    (ht : t ∈ Set.Icc 0 1) (hp : AffineMap.lineMap a b t ∈ Metric.sphere z ρ) :
    t = 1 := by
  by_contra hne
  have hlt : t < 1 := lt_of_le_of_ne ht.2 hne
  have h := lineMap_mem_ball ha (Metric.sphere_subset_closedBall hb) ⟨ht.1, hlt⟩
  exact (ne_of_lt h) (Metric.mem_sphere.mp hp)

/-- Two different boundary ports of a round ball have spokes meeting only at their
common interior center. No bound on the angular span of the ports is needed. -/
theorem fan_contact {z a p q : ℂ} {ρ s t : ℝ}
    (ha : a ∈ Metric.ball z ρ) (hp : p ∈ Metric.sphere z ρ)
    (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap a p s = AffineMap.lineMap a q t) : s = 0 ∧ t = 0 := by
  have one_side {p q : ℂ} {s t : ℝ} (hp : p ∈ Metric.sphere z ρ)
      (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q)
      (hs : 0 ≤ s) (hst : s ≤ t)
      (heq : AffineMap.lineMap a p s = AffineMap.lineMap a q t) : t = 0 := by
    by_contra ht0
    have htpos : 0 < t := lt_of_le_of_ne (hs.trans hst) (Ne.symm ht0)
    have hvec : s • (p - a) = t • (q - a) := by
      simpa only [AffineMap.lineMap_apply_module', add_left_inj] using heq
    have hparam : AffineMap.lineMap a p (s / t) = q := by
      rw [AffineMap.lineMap_apply_module', div_eq_inv_mul, mul_smul, hvec,
        inv_smul_smul₀ (ne_of_gt htpos), sub_add_cancel]
    have hst1 : s / t = 1 := lineMap_sphere_parameter ha hp
      ⟨div_nonneg hs htpos.le, (div_le_one htpos).mpr hst⟩ (hparam ▸ hq)
    rw [hst1, AffineMap.lineMap_apply_one] at hparam
    exact hpq hparam
  rcases le_total s t with hst | hts
  · have ht0 := one_side hp hq hpq hs.1 hst heq
    exact ⟨le_antisymm (hst.trans ht0.le) hs.1, ht0⟩
  · have hs0 := one_side hq hp hpq.symm ht.1 hts heq.symm
    exact ⟨hs0, le_antisymm (hts.trans hs0.le) ht.1⟩

/-- Distinct round-boundary ports have distinct actual arguments when seen from any
interior point. This is the geometric injectivity needed after moving a fan center. -/
theorem arg_sub_injective_on_sphere {z a p q : ℂ} {ρ : ℝ}
    (ha : a ∈ Metric.ball z ρ) (hp : p ∈ Metric.sphere z ρ)
    (hq : q ∈ Metric.sphere z ρ)
    (heq : ((p - a).arg : Real.Angle) = ((q - a).arg : Real.Angle)) : p = q := by
  by_contra hpq
  have hpa : p - a ≠ 0 := by
    intro h
    have h' : p = a := sub_eq_zero.mp h
    rw [h'] at hp
    exact (ne_of_lt ha) (Metric.mem_sphere.mp hp)
  have hqa : q - a ≠ 0 := by
    intro h
    have h' : q = a := sub_eq_zero.mp h
    rw [h'] at hq
    exact (ne_of_lt ha) (Metric.mem_sphere.mp hq)
  obtain ⟨s, hs, t, ht, hst⟩ := exists_small_smul_eq_of_arg_eq hpa hqa
    (Complex.arg_coe_angle_eq_iff.mp heq) (by norm_num : (0 : ℝ) < 1)
  have hpoint : AffineMap.lineMap a p s = AffineMap.lineMap a q t := by
    simpa only [AffineMap.lineMap_apply_module', add_left_inj] using hst
  have hzero := fan_contact ha hp hq hpq ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hpoint
  exact (ne_of_gt hs.1) hzero.1

/-- An affine separating coordinate keeps a spoke beyond its fan center. -/
theorem fan_coordinate_le (f : ℂ →ᵃ[ℝ] ℝ) {a p : ℂ} (hp : f a < f p)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : f a ≤ f (AffineMap.lineMap a p t) := by
  rw [f.apply_lineMap, AffineMap.lineMap_apply_ring']
  nlinarith [mul_nonneg ht.1 (sub_pos.mpr hp).le]

/-- Oppositely separated spokes cannot meet, for any real segment parameters. -/
theorem split_spokes_ne (f : ℂ →ᵃ[ℝ] ℝ) {a b p q : ℂ}
    (hab : f b < f a) (hp : f a < f p) (hq : f q < f b)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    AffineMap.lineMap a p s ≠ AffineMap.lineMap b q t := by
  intro heq
  have hleft := fan_coordinate_le f hp hs
  have hright := fan_coordinate_le (-f) (by simpa using hq) ht
  change -f b ≤ -f (AffineMap.lineMap b q t) at hright
  rw [heq] at hleft
  linarith

/-- A spoke beyond one connector end meets the connector only at that end. -/
theorem split_connector_contact (f : ℂ →ᵃ[ℝ] ℝ) {a b p : ℂ}
    (hab : f b < f a) (hp : f a < f p)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap a p s = AffineMap.lineMap a b t) : s = 0 ∧ t = 0 := by
  have hcoord := congrArg f heq
  rw [f.apply_lineMap, f.apply_lineMap, AffineMap.lineMap_apply_ring',
    AffineMap.lineMap_apply_ring'] at hcoord
  have hs0 : s = 0 := by nlinarith [hs.1, ht.1]
  have ht0 : t = 0 := by rw [hs0, zero_mul, zero_add] at hcoord; nlinarith
  exact ⟨hs0, ht0⟩

end Cslib.Polygonal
