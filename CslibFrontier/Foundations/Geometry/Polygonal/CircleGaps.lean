/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.CircleChord
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Gaps separating two finite circular blocks

Real angle representatives in a single turn determine two actual gap points on the
circle. Finite extrema choose the second gap internally. Empty blocks retain the
specified cut: when one block is empty, both gaps lie in that block's empty slot.
-/

public section

namespace Cslib.Polygonal

/-- Cutting before two real representatives in one turn turns their circular order
into their strict linear order. Equal representatives give no strict betweenness. -/
theorem sbtw_angle_cut_iff_lt {cut a b : ℝ}
    (ha : a ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hb : b ∈ Set.Ioo cut (cut + 2 * Real.pi)) :
    sbtw (cut : Real.Angle) (a : Real.Angle) (b : Real.Angle) ↔ a < b := by
  refine ⟨fun h => ?_, fun hab => sbtw_angle_of_lt_of_span_lt ha.1 hab (by linarith [hb.2])⟩
  by_contra hn
  rcases lt_or_eq_of_le (le_of_not_gt hn) with hba | hba
  · have hrev := sbtw_angle_of_lt_of_span_lt hb.1 hba (by linarith [ha.2])
    exact h.not_sbtw hrev.cyclic_left
  · rw [hba] at h
    exact sbtw_irrefl_right h

/-- Two finite linearly ordered blocks in one open turn admit an intervening cut,
even when either block is empty. The original cut is retained. -/
theorem exists_gap_between_finite_blocks (A B : Finset ℂ) (θ : ℂ → ℝ) (cut : ℝ)
    (hA : ∀ x ∈ A, θ x ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hB : ∀ x ∈ B, θ x ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hAB : ∀ x ∈ A, ∀ y ∈ B, θ x < θ y) :
    ∃ gap ∈ Set.Ioo cut (cut + 2 * Real.pi),
      (∀ x ∈ A, θ x < gap) ∧ (∀ y ∈ B, gap < θ y) := by
  classical
  let L := insert cut (A.image θ)
  let U := insert (cut + 2 * Real.pi) (B.image θ)
  have hL : L.Nonempty := ⟨cut, Finset.mem_insert_self _ _⟩
  have hU : U.Nonempty := ⟨cut + 2 * Real.pi, Finset.mem_insert_self _ _⟩
  have hlt : L.sup' hL id < U.inf' hU id := by
    apply (Finset.sup'_lt_iff hL).mpr
    intro a ha
    apply (Finset.lt_inf'_iff hU).mpr
    intro b hb
    rcases Finset.mem_insert.mp ha with rfl | ha <;>
      rcases Finset.mem_insert.mp hb with rfl | hb
    · exact lt_add_of_pos_right _ Real.two_pi_pos
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      exact (hB y hy).1
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact (hA x hx).2
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      exact hAB x hx y hy
  obtain ⟨gap, hlo, hhi⟩ := exists_between hlt
  refine ⟨gap, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (Finset.le_sup' id (Finset.mem_insert_self cut (A.image θ))).trans_lt hlo
  · exact hhi.trans_le (Finset.inf'_le id
      (Finset.mem_insert_self (cut + 2 * Real.pi) (B.image θ)))
  · intro x hx
    exact (Finset.le_sup' id (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨x, hx, rfl⟩))).trans_lt hlo
  · intro y hy
    exact hhi.trans_le (Finset.inf'_le id (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))

/-- Boundary point with the prescribed real angle representative and radius. -/
@[expose] noncomputable def circlePoint (z : ℂ) (ρ θ : ℝ) : ℂ :=
  z + (ρ : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)

/-- The parameterized circle point lies on its actual real metric sphere. -/
theorem circlePoint_mem_sphere (z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    circlePoint z ρ θ ∈ Metric.sphere z ρ := by
  rw [Metric.mem_sphere, dist_eq_norm, circlePoint, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hρ, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.norm_cos_add_sin_mul_I, mul_one]

/-- The point's literal argument is the prescribed angle, without a principal-cut
restriction on the real representative. -/
theorem arg_circlePoint_sub (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    ((circlePoint z ρ θ - z).arg : Real.Angle) = (θ : Real.Angle) := by
  rw [circlePoint, add_sub_cancel_left]
  simpa only [Real.Angle.cos_coe, Real.Angle.sin_coe] using
    Complex.arg_mul_cos_add_sin_mul_I_coe_angle hρ (θ : Real.Angle)

/-- Two finite contiguous blocks on a real circle supply their own two separating
gap points. The input records only their actual angle representatives and order.
It supplies no geometric separator, center or connector. -/
theorem exists_circle_gaps_of_finite_blocks {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (A B : Finset ℂ) (θ : ℂ → ℝ) (cut : ℝ)
    (hA : ∀ x ∈ A, x ∈ Metric.sphere z ρ ∧
      θ x ∈ Set.Ioo cut (cut + 2 * Real.pi) ∧
      ((x - z).arg : Real.Angle) = (θ x : Real.Angle))
    (hB : ∀ x ∈ B, x ∈ Metric.sphere z ρ ∧
      θ x ∈ Set.Ioo cut (cut + 2 * Real.pi) ∧
      ((x - z).arg : Real.Angle) = (θ x : Real.Angle))
    (hAB : ∀ x ∈ A, ∀ y ∈ B, θ x < θ y) :
    ∃ gap ∈ Set.Ioo cut (cut + 2 * Real.pi),
      ∃ p ∈ Metric.sphere z ρ, ∃ q ∈ Metric.sphere z ρ,
      ((p - z).arg : Real.Angle) = (cut : Real.Angle) ∧
      ((q - z).arg : Real.Angle) = (gap : Real.Angle) ∧ p ≠ q ∧
      (∀ x ∈ A, θ x < gap) ∧ (∀ x ∈ B, gap < θ x) ∧
      (∀ x ∈ A, sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((q - z).arg : Real.Angle)) ∧
      (∀ x ∈ B, sbtw ((q - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((p - z).arg : Real.Angle)) := by
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  obtain ⟨gap, hgap, hAgap, hBgap⟩ := exists_gap_between_finite_blocks A B θ cut
    (fun x hx => (hA x hx).2.1) (fun x hx => (hB x hx).2.1) hAB
  refine ⟨gap, hgap, circlePoint z ρ cut, circlePoint_mem_sphere z hρ.le cut,
    circlePoint z ρ gap, circlePoint_mem_sphere z hρ.le gap,
    arg_circlePoint_sub z hρ cut, arg_circlePoint_sub z hρ gap, ?_, hAgap, hBgap, ?_, ?_⟩
  · intro heq
    have hang := congrArg (fun x : ℂ => ((x - z).arg : Real.Angle)) heq
    rw [arg_circlePoint_sub z hρ, arg_circlePoint_sub z hρ] at hang
    have hreal : cut = gap := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := 2 * Real.pi) ⟨le_rfl, by linarith [Real.pi_pos]⟩
      ⟨hgap.1.le, hgap.2⟩).mp hang
    exact hgap.1.ne hreal
  · intro x hx
    rw [arg_circlePoint_sub z hρ, arg_circlePoint_sub z hρ, (hA x hx).2.2]
    exact sbtw_angle_of_lt_of_span_lt (hA x hx).2.1.1 (hAgap x hx) (by linarith [hgap.2])
  · intro x hx
    rw [arg_circlePoint_sub z hρ, arg_circlePoint_sub z hρ, (hB x hx).2.2]
    simpa only [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero] using
      sbtw_angle_of_lt_of_span_lt (hBgap x hx) (hB x hx).2.1.2
        (by linarith [hgap.1])

end Cslib.Polygonal
