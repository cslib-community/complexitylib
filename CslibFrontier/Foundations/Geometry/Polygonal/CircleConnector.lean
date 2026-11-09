/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.CircleGaps

/-!
# Connector insertion in a prescribed circle gap

Opposite small normal offsets of a chord midpoint have a straight connector. At each
offset, that connector occupies the complementary gap of its assigned circular block.
The order statements compare actual complex arguments in the fixed orientation.
-/

public section

namespace Cslib.Polygonal

private theorem same_gap_origin {p q t x y : Real.Angle}
    (hx : sbtw p x q) (hy : sbtw p y q) (ht : sbtw q t p) :
    sbtw t x y ↔ sbtw p x y := by
  have forward {x y : Real.Angle} (hy : sbtw p y q) (hxy : sbtw p x y) : sbtw t x y :=
    ((hy.cyclic_left.trans_left ht).cyclic_left).trans_left hxy
  refine ⟨fun h => ?_, forward hy⟩
  apply sbtw_iff_not_btw.mpr
  intro hbad
  have hb : btw p y x := hbad.cyclic_right
  have hs : sbtw p y x := hb.sbtw_of_not_btw (fun hother => by
    rcases hb.antisymm hother with heq | heq | heq
    · exact sbtw_irrefl_left (heq ▸ hy)
    · exact sbtw_irrefl_right (heq ▸ h)
    · exact sbtw_irrefl_left (heq ▸ hx))
  exact h.not_sbtw (forward hx hs).cyclic_left

/-- Reversing the chord interchanges positive and negative normal offsets. -/
theorem chordOffset_swap (p q : ℂ) (t : ℝ) :
    chordOffset q p t = chordOffset p q (-t) := by
  have hq : q - midpoint ℝ p q = -(p - midpoint ℝ p q) := by
    simp only [right_sub_midpoint, left_sub_midpoint, ← smul_neg, neg_sub]
  simp only [chordOffset, midpoint_comm q p, hq, mul_neg, smul_neg, neg_smul]

private theorem normal_complementary {p q : ℂ} (hpq : p ≠ q) :
    sbtw ((q - midpoint ℝ p q).arg : Real.Angle)
      ((-(Complex.I * (p - midpoint ℝ p q))).arg : Real.Angle)
      ((p - midpoint ℝ p q).arg : Real.Angle) := by
  have hd : p - midpoint ℝ p q ≠ 0 := fun h => hpq
    ((left_eq_midpoint_iff (R := ℝ)).mp (sub_eq_zero.mp h))
  have hq : q - midpoint ℝ p q = -(p - midpoint ℝ p q) := by
    simp only [right_sub_midpoint, left_sub_midpoint, ← smul_neg, neg_sub]
  rw [hq, Complex.arg_neg_coe_angle hd, ← neg_mul,
    Complex.arg_mul_coe_angle (neg_ne_zero.mpr Complex.I_ne_zero) hd, Complex.arg_neg_I]
  have h := (sbtw_angle_of_lt_of_span_lt (by linarith [Real.pi_pos] :
      -(Real.pi / 2) < 0) Real.pi_pos (by linarith [Real.pi_pos])).cyclic_right
  have htranslate := sbtw_angle_add_right_iff (Real.pi : Real.Angle)
    (-(Real.pi / 2) : ℝ) 0 ((p - midpoint ℝ p q).arg : Real.Angle)
  simpa only [zero_add, Real.Angle.coe_zero,
    add_comm (Real.pi : Real.Angle) ((p - midpoint ℝ p q).arg : Real.Angle)] using
    htranslate.mpr h

/-- At all sufficiently small offsets, the connector's outgoing direction has the
same position relative to two ports as the specified start of their circular block.
The strict circle gaps supply this position; no connector-order premise is used. -/
theorem eventually_connector_order_of_circle_arc {z p q x y : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ)
    (hx : x ∈ Metric.sphere z ρ) (hy : y ∈ Metric.sphere z ρ)
    (hpq : p ≠ q) (hxy : x ≠ y)
    (hpxq : sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
      ((q - z).arg : Real.Angle))
    (hpyq : sbtw ((p - z).arg : Real.Angle) ((y - z).arg : Real.Angle)
      ((q - z).arg : Real.Angle)) :
    ∀ᶠ t in nhds (0 : ℝ),
      sbtw ((-(Complex.I * (p - midpoint ℝ p q))).arg : Real.Angle)
        ((x - chordOffset p q t).arg : Real.Angle)
        ((y - chordOffset p q t).arg : Real.Angle) ↔
      sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((y - z).arg : Real.Angle) := by
  let m := midpoint ℝ p q
  let n := Complex.I * (p - m)
  have hm : m ∈ Metric.ball z ρ := midpoint_mem_ball_of_mem_sphere hp hq hpq
  have hρ : 0 < ρ := (dist_nonneg : 0 ≤ dist m z).trans_lt hm
  have hne (w : ℂ) (hw : w ∈ Metric.sphere z ρ) : w - m ≠ 0 := by
    intro h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hw ((sub_eq_zero.mp h).symm ▸ hm)
  have hpx : p ≠ x := fun h => sbtw_irrefl_left (h ▸ hpxq)
  have hxq : x ≠ q := fun h => sbtw_irrefl_right (h ▸ hpxq)
  have hpy : p ≠ y := fun h => sbtw_irrefl_left (h ▸ hpyq)
  have hyq : y ≠ q := fun h => sbtw_irrefl_right (h ▸ hpyq)
  have hxmid := (sbtw_arg_sub_iff_of_mem_ball (Metric.mem_ball_self hρ) hm
    hp hx hq hpx hxq hpq).mp hpxq
  have hymid := (sbtw_arg_sub_iff_of_mem_ball (Metric.mem_ball_self hρ) hm
    hp hy hq hpy hyq hpq).mp hpyq
  have ht : sbtw ((q - m).arg : Real.Angle) ((-n).arg : Real.Angle)
      ((p - m).arg : Real.Angle) := normal_complementary hpq
  have htx : ((-n).arg : Real.Angle) ≠ ((x - m).arg : Real.Angle) := by
    intro heq
    rw [← heq] at hxmid
    exact ht.not_sbtw hxmid
  have hty : ((-n).arg : Real.Angle) ≠ ((y - m).arg : Real.Angle) := by
    intro heq
    rw [← heq] at hymid
    exact ht.not_sbtw hymid
  have hxyarg : ((x - m).arg : Real.Angle) ≠ ((y - m).arg : Real.Angle) :=
    fun heq => hxy (arg_sub_injective_on_sphere hm hx hy heq)
  have hcont (w : ℂ) (hw : w ∈ Metric.sphere z ρ) :
      ContinuousAt (fun t : ℝ => ((w - chordOffset p q t).arg : Real.Angle)) 0 := by
    apply (Complex.continuousAt_arg_coe_angle (by simpa [chordOffset] using hne w hw)).comp
    unfold chordOffset
    fun_prop
  have hlocal := eventually_sbtw_angle_iff (f := fun _ : ℝ => ((-n).arg : Real.Angle))
    continuousAt_const (hcont x hx) (hcont y hy)
    (by simpa only [chordOffset, zero_smul, add_zero, m] using htx)
    (by simpa only [chordOffset, zero_smul, add_zero, m] using hxyarg)
    (by simpa only [chordOffset, zero_smul, add_zero, m] using hty)
  have horder := (same_gap_origin hxmid hymid ht).trans
    (sbtw_arg_sub_iff_of_mem_ball hm (Metric.mem_ball_self hρ) hp hx hy hpx hxy hpy)
  filter_upwards [hlocal] with t ht'
  exact ht'.trans (by simpa [chordOffset, m, n] using horder)

/-- Finite circle gaps determine two separated interior fans and a connector in the
exact complementary gap at each center. Empty blocks impose no spurious order condition.
All separation and connector orders are proved from the two actual circle arcs. -/
theorem exists_split_fans_of_circle_gaps {z p q : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q)
    (A B : Finset ℂ)
    (hA : ∀ x ∈ A, x ∈ Metric.sphere z ρ ∧
      sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((q - z).arg : Real.Angle))
    (hB : ∀ x ∈ B, x ∈ Metric.sphere z ρ ∧
      sbtw ((q - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((p - z).arg : Real.Angle)) :
    ∃ a ∈ Metric.ball z ρ, ∃ b ∈ Metric.ball z ρ,
      chordCoordinate p q b < chordCoordinate p q a ∧
      (∀ x ∈ A, chordCoordinate p q a < chordCoordinate p q x) ∧
      (∀ x ∈ B, chordCoordinate p q x < chordCoordinate p q b) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        (sbtw ((b - a).arg : Real.Angle) ((x - a).arg : Real.Angle)
          ((y - a).arg : Real.Angle) ↔
        sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
          ((y - z).arg : Real.Angle))) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y →
        (sbtw ((a - b).arg : Real.Angle) ((x - b).arg : Real.Angle)
          ((y - b).arg : Real.Angle) ↔
        sbtw ((q - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
          ((y - z).arg : Real.Angle))) := by
  classical
  let n := Complex.I * (p - midpoint ℝ p q)
  have hqn : -(Complex.I * (q - midpoint ℝ q p)) = n := by
    have hq' : q - midpoint ℝ p q = -(p - midpoint ℝ p q) := by
      simp only [right_sub_midpoint, left_sub_midpoint, ← smul_neg, neg_sub]
    simp only [midpoint_comm q p, hq', mul_neg, neg_neg, n]
  have hleft : ∀ᶠ t in nhds (0 : ℝ), ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      (sbtw ((-n).arg : Real.Angle) ((x - chordOffset p q t).arg : Real.Angle)
        ((y - chordOffset p q t).arg : Real.Angle) ↔
      sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((y - z).arg : Real.Angle)) := by
    apply (Filter.eventually_all_finset A).mpr
    intro x hx
    apply (Filter.eventually_all_finset A).mpr
    intro y hy
    by_cases hxy : x = y
    · exact Filter.Eventually.of_forall fun _ hne => False.elim (hne hxy)
    · exact (eventually_connector_order_of_circle_arc hp hq (hA x hx).1 (hA y hy).1
        hpq hxy (hA x hx).2 (hA y hy).2).mono fun _ h _ => h
  have hright : ∀ᶠ t in nhds (0 : ℝ), ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      (sbtw (n.arg : Real.Angle) ((x - chordOffset p q (-t)).arg : Real.Angle)
        ((y - chordOffset p q (-t)).arg : Real.Angle) ↔
      sbtw ((q - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((y - z).arg : Real.Angle)) := by
    apply (Filter.eventually_all_finset B).mpr
    intro x hx
    apply (Filter.eventually_all_finset B).mpr
    intro y hy
    by_cases hxy : x = y
    · exact Filter.Eventually.of_forall fun _ hne => False.elim (hne hxy)
    · have h := eventually_connector_order_of_circle_arc hq hp (hB x hx).1 (hB y hy).1
        hpq.symm hxy (hB x hx).2 (hB y hy).2
      simp only [hqn, chordOffset_swap p q] at h
      exact h.mono fun _ h _ => h
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp (hleft.and hright)
  obtain ⟨ε, hε, ha, hb, hsep, hpa, hpb⟩ :=
    exists_split_offsets_of_circle_gaps hp hq hpq A B hA hB hδ
  have hεlocal : dist ε (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]
    exact hε.2
  obtain ⟨hAorder, hBorder⟩ := hlocal hεlocal
  have hconn : chordOffset p q (-ε) - chordOffset p q ε = (2 * ε) • (-n) := by
    change (midpoint ℝ p q + (-ε) • n) - (midpoint ℝ p q + ε • n) = (2 * ε) • (-n)
    module
  have hconn' : chordOffset p q ε - chordOffset p q (-ε) = (2 * ε) • n := by
    change (midpoint ℝ p q + ε • n) - (midpoint ℝ p q + (-ε) • n) = (2 * ε) • n
    module
  refine ⟨chordOffset p q ε, ha, chordOffset p q (-ε), hb, hsep, hpa, hpb, ?_, ?_⟩
  · rw [hconn, Complex.real_smul, Complex.arg_real_mul _ (mul_pos (by norm_num) hε.1)]
    exact hAorder
  · rw [hconn', Complex.real_smul, Complex.arg_real_mul _ (mul_pos (by norm_num) hε.1)]
    exact hBorder

/-- Two finite consecutive blocks of actual circle ports determine separated interior
fans and a straight connector in their prescribed insertion slots. Only the actual
circle, its port order and its specified cut are inputs; all gap points, centers,
the affine separator and connector order are chosen and proved internally. -/
theorem exists_split_fans_of_finite_blocks {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (A B : Finset ℂ) (θ : ℂ → ℝ) (cut : ℝ)
    (hA : ∀ x ∈ A, x ∈ Metric.sphere z ρ ∧
      θ x ∈ Set.Ioo cut (cut + 2 * Real.pi) ∧
      ((x - z).arg : Real.Angle) = (θ x : Real.Angle))
    (hB : ∀ x ∈ B, x ∈ Metric.sphere z ρ ∧
      θ x ∈ Set.Ioo cut (cut + 2 * Real.pi) ∧
      ((x - z).arg : Real.Angle) = (θ x : Real.Angle))
    (hAB : ∀ x ∈ A, ∀ y ∈ B, θ x < θ y) :
    ∃ a ∈ Metric.ball z ρ, ∃ b ∈ Metric.ball z ρ, ∃ f : ℂ →ᵃ[ℝ] ℝ,
      f b < f a ∧ (∀ x ∈ A, f a < f x) ∧ (∀ x ∈ B, f x < f b) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        (sbtw ((b - a).arg : Real.Angle) ((x - a).arg : Real.Angle)
          ((y - a).arg : Real.Angle) ↔ θ x < θ y)) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y →
        (sbtw ((a - b).arg : Real.Angle) ((x - b).arg : Real.Angle)
          ((y - b).arg : Real.Angle) ↔ θ x < θ y)) := by
  obtain ⟨gap, hgap, p, hp, q, hq, hpangle, hqangle, hpq, _, hBgap, hAgaps, hBgaps⟩ :=
    exists_circle_gaps_of_finite_blocks hρ A B θ cut hA hB hAB
  obtain ⟨a, ha, b, hb, hsep, hpa, hpb, horderA, horderB⟩ :=
    exists_split_fans_of_circle_gaps hp hq hpq A B
      (fun x hx => ⟨(hA x hx).1, hAgaps x hx⟩)
      (fun x hx => ⟨(hB x hx).1, hBgaps x hx⟩)
  refine ⟨a, ha, b, hb, chordCoordinate p q, hsep, hpa, hpb, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := horderA x hx y hy hxy
    rw [hpangle, (hA x hx).2.2, (hA y hy).2.2] at h
    exact h.trans (sbtw_angle_cut_iff_lt (hA x hx).2.1 (hA y hy).2.1)
  · intro x hx y hy hxy
    have h := horderB x hx y hy hxy
    rw [hqangle, (hB x hx).2.2, (hB y hy).2.2] at h
    exact h.trans (sbtw_angle_cut_iff_lt
      ⟨hBgap x hx, by linarith [(hB x hx).2.1.2, hgap.1]⟩
      ⟨hBgap y hy, by linarith [(hB y hy).2.1.2, hgap.1]⟩)

end Cslib.Polygonal
