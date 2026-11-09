/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayOrder
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Circle chords and affine separation

The midpoint of a chord is an interior point of the circle. The two open circular
arcs cut out by its endpoints are exactly the two strict affine half-planes of the
chord. This works for both major and minor arcs, including a diameter.
-/

public section

namespace Cslib.Polygonal

/-- The open upper half-plane is the strict angle interval from zero to pi. -/
theorem sbtw_zero_arg_pi_iff (w : ℂ) :
    sbtw (0 : Real.Angle) (w.arg : Real.Angle) (Real.pi : Real.Angle) ↔ 0 < w.im := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hi | hi
    · have ha := Complex.arg_neg_iff.mpr hi
      have hrev := (sbtw_angle_of_lt_of_span_lt ha Real.pi_pos
        (by linarith [Complex.neg_pi_lt_arg w])).cyclic_right
      exact h.not_sbtw hrev
    · by_cases hr : 0 ≤ w.re
      · have ha := Complex.arg_eq_zero_iff.mpr ⟨hr, hi⟩
        rw [ha, Real.Angle.coe_zero] at h
        exact sbtw_irrefl_left h
      · have ha := Complex.arg_eq_pi_iff.mpr ⟨lt_of_not_ge hr, hi⟩
        rw [ha] at h
        exact sbtw_irrefl_right h
  · intro hi
    have h₀ : 0 < w.arg := by
      have hnonneg := Complex.arg_nonneg_iff.mpr hi.le
      have hne : w.arg ≠ 0 := fun h => hi.ne' (Complex.arg_eq_zero_iff.mp h).2
      exact lt_of_le_of_ne hnonneg hne.symm
    have hπ : w.arg < Real.pi := by
      have hne : w.arg ≠ Real.pi := fun h => hi.ne' (Complex.arg_eq_pi_iff.mp h).2
      exact lt_of_le_of_ne (Complex.arg_le_pi w) hne
    simpa only [Real.Angle.coe_zero] using
      sbtw_angle_of_lt_of_span_lt h₀ hπ (by linarith [Real.pi_pos])

/-- Two distinct points on a circle have a chord midpoint strictly inside it. -/
theorem midpoint_mem_ball_of_mem_sphere {z p q : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q) :
    midpoint ℝ p q ∈ Metric.ball z ρ := by
  have hρ : ρ ≠ 0 := by
    intro h
    rw [h, Metric.sphere_zero] at hp hq
    exact hpq ((Set.mem_singleton_iff.mp hp).trans (Set.mem_singleton_iff.mp hq).symm)
  rw [← interior_closedBall z hρ]
  exact (strictConvex_closedBall ℝ z ρ).openSegment_subset
    (Metric.sphere_subset_closedBall hp) (Metric.sphere_subset_closedBall hq) hpq
    (midpoint_mem_openSegment p q)

/-- The signed coordinate perpendicular to a chord, scaled so its normal has unit
coordinate. The first endpoint fixes the sign; its counterclockwise arc is positive. -/
@[expose] noncomputable def chordCoordinate (p q : ℂ) : ℂ →ᵃ[ℝ] ℝ :=
  { toFun := fun x => ((x - midpoint ℝ p q) / (p - midpoint ℝ p q)).im
    linear := Complex.imCLM.toLinearMap.comp
      (LinearMap.mulRight ℝ (p - midpoint ℝ p q)⁻¹)
    map_vadd' := by
      intro x y
      simp only [vadd_eq_add, Complex.add_im, div_eq_mul_inv,
        add_sub_assoc, add_mul, Complex.add_im]
      rfl }

/-- A circle arc has exactly the sign of its chord's affine coordinate. All real
coordinates are retained, with no angular-span restriction. -/
theorem sbtw_arg_iff_chordCoordinate_pos {z p q x : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ)
    (hx : x ∈ Metric.sphere z ρ) (hpq : p ≠ q) (hpx : p ≠ x) (hxq : x ≠ q) :
    sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
      ((q - z).arg : Real.Angle) ↔ 0 < chordCoordinate p q x := by
  let m := midpoint ℝ p q
  have hm : m ∈ Metric.ball z ρ := midpoint_mem_ball_of_mem_sphere hp hq hpq
  have hρ : 0 < ρ := (dist_nonneg : 0 ≤ dist m z).trans_lt hm
  have hpm : p - m ≠ 0 := by
    intro h
    have h' : p = m := sub_eq_zero.mp h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp (h' ▸ hm)
  have hxm : x - m ≠ 0 := by
    intro h
    have h' : x = m := sub_eq_zero.mp h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hx (h' ▸ hm)
  have hqm : q - m = -(p - m) := by
    simp only [m, right_sub_midpoint, left_sub_midpoint, ← smul_neg, neg_sub]
  have horder := sbtw_arg_sub_iff_of_mem_ball (Metric.mem_ball_self hρ) hm
    hp hx hq hpx hxq hpq
  rw [horder, hqm, Complex.arg_neg_coe_angle hpm]
  have htranslate := sbtw_angle_add_right_iff
    (0 : Real.Angle) (((x - m).arg : Real.Angle) - (p - m).arg) Real.pi
    ((p - m).arg : Real.Angle)
  simp only [zero_add, sub_add_cancel, add_comm (Real.pi : Real.Angle)] at htranslate
  rw [htranslate, ← Complex.arg_div_coe_angle hxm hpm, sbtw_zero_arg_pi_iff]
  rfl

/-- Reversing the oriented chord reverses its affine coordinate. -/
theorem chordCoordinate_swap (p q : ℂ) : chordCoordinate q p = -chordCoordinate p q := by
  ext x
  change ((x - midpoint ℝ q p) / (q - midpoint ℝ q p)).im =
    -((x - midpoint ℝ p q) / (p - midpoint ℝ p q)).im
  rw [midpoint_comm q p]
  have hq : q - midpoint ℝ p q = -(p - midpoint ℝ p q) := by
    simp only [right_sub_midpoint, left_sub_midpoint, ← smul_neg, neg_sub]
  rw [hq, div_neg, Complex.neg_im]

/-- Offset the chord midpoint in its oriented normal direction. -/
@[expose] noncomputable def chordOffset (p q : ℂ) (t : ℝ) : ℂ :=
  midpoint ℝ p q + t • (Complex.I * (p - midpoint ℝ p q))

/-- A finite collection on the two open arcs of a circle admits arbitrarily small
opposite interior offsets strictly separated from their assigned ports. Either port set
may be empty. The offsets and affine separator are constructed from the circle and gaps. -/
theorem exists_split_offsets_of_circle_gaps {z p q : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q)
    (A B : Finset ℂ)
    (hA : ∀ x ∈ A, x ∈ Metric.sphere z ρ ∧
      sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((q - z).arg : Real.Angle))
    (hB : ∀ x ∈ B, x ∈ Metric.sphere z ρ ∧
      sbtw ((q - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((p - z).arg : Real.Angle)) {bound : ℝ} (hbound : 0 < bound) :
    ∃ ε ∈ Set.Ioo 0 bound,
      chordOffset p q ε ∈ Metric.ball z ρ ∧ chordOffset p q (-ε) ∈ Metric.ball z ρ ∧
      chordCoordinate p q (chordOffset p q (-ε)) <
        chordCoordinate p q (chordOffset p q ε) ∧
      (∀ x ∈ A, chordCoordinate p q (chordOffset p q ε) < chordCoordinate p q x) ∧
      (∀ x ∈ B, chordCoordinate p q x < chordCoordinate p q (chordOffset p q (-ε))) := by
  classical
  let m := midpoint ℝ p q
  let n := Complex.I * (p - m)
  let f := chordCoordinate p q
  have hm : m ∈ Metric.ball z ρ := midpoint_mem_ball_of_mem_sphere hp hq hpq
  have hpm : p - m ≠ 0 := by
    intro h
    have h' : p = m := sub_eq_zero.mp h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp (h' ▸ hm)
  have hpos : ∀ x ∈ A, 0 < f x := by
    intro x hx
    have h := hA x hx
    exact (sbtw_arg_iff_chordCoordinate_pos hp hq h.1 hpq
      (fun heq => sbtw_irrefl_left (heq ▸ h.2))
      (fun heq => sbtw_irrefl_right (heq ▸ h.2))).mp h.2
  have hneg : ∀ x ∈ B, f x < 0 := by
    intro x hx
    have h := hB x hx
    have hsign := (sbtw_arg_iff_chordCoordinate_pos hq hp h.1 hpq.symm
      (fun heq => sbtw_irrefl_left (heq ▸ h.2))
      (fun heq => sbtw_irrefl_right (heq ▸ h.2))).mp h.2
    rw [chordCoordinate_swap] at hsign
    change 0 < -f x at hsign
    linarith
  have hcoord (t : ℝ) : f (m + t • n) = t := by
    change ((m + t • (Complex.I * (p - m)) - m) / (p - m)).im = t
    rw [add_sub_cancel_left, Complex.real_smul]
    simp only [← mul_assoc, mul_div_cancel_right₀ _ hpm, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
  have hplus : ContinuousAt (fun t : ℝ => m + t • n) 0 := by fun_prop
  have hminus : ContinuousAt (fun t : ℝ => m + (-t) • n) 0 := by fun_prop
  have hpball : ∀ᶠ t in nhds (0 : ℝ), m + t • n ∈ Metric.ball z ρ :=
    hplus.eventually (Metric.isOpen_ball.mem_nhds (by simpa using hm))
  have hmball : ∀ᶠ t in nhds (0 : ℝ), m + (-t) • n ∈ Metric.ball z ρ :=
    hminus.eventually (Metric.isOpen_ball.mem_nhds (by simpa using hm))
  have hAP : ∀ᶠ t in nhds (0 : ℝ), ∀ x ∈ A, t < f x :=
    (Filter.eventually_all_finset A).mpr fun x hx =>
      continuousAt_id.eventually_lt continuousAt_const (hpos x hx)
  have hBP : ∀ᶠ t in nhds (0 : ℝ), ∀ x ∈ B, f x < -t :=
    (Filter.eventually_all_finset B).mpr fun x hx =>
      continuousAt_const.eventually_lt continuousAt_id.neg (by simpa using hneg x hx)
  have hlocal := hpball.and (hmball.and (hAP.and hBP))
  obtain ⟨δ, hδ, hδlocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  let ε := min δ bound / 2
  have hε : 0 < ε := div_pos (lt_min hδ hbound) (by norm_num)
  have hεδ : ε < δ := by
    have h := min_le_left δ bound
    dsimp [ε]
    linarith
  have hεbound : ε < bound := by
    have h := min_le_right δ bound
    dsimp [ε]
    linarith
  have heps : dist ε (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact hεδ
  obtain ⟨ha, hb, hA', hB'⟩ := hδlocal heps
  refine ⟨ε, ⟨hε, hεbound⟩, ha, hb, ?_, ?_, ?_⟩
  · change f (m + (-ε) • n) < f (m + ε • n)
    rw [hcoord, hcoord]
    linarith
  · change ∀ x ∈ A, f (m + ε • n) < f x
    rw [hcoord]
    exact hA'
  · change ∀ x ∈ B, f x < f (m + (-ε) • n)
    rw [hcoord]
    exact hB'

end Cslib.Polygonal
