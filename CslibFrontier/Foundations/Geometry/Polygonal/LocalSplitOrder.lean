/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitFan
public import CslibFrontier.Foundations.Geometry.Polygonal.AngleOrder
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Circular order for moving local fan centers

Moving the center anywhere inside a circle preserves the literal circular order of its
distinct boundary ports. The proof uses local real representatives and convex connectedness
of the ball. The cut of the turn can be anywhere; no principal-argument branch or
rational-coordinate hypothesis is imposed. No ambient map or PL transport is assumed.
-/

public section

namespace Cslib.Polygonal

/-- Three distinct real representatives in any one turn have exactly their cyclic
linear order as angles. In particular the cut may cross the principal argument branch. -/
theorem sbtw_angle_iff_cyclic_lt {cut a b c : ℝ}
    (ha : a ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hb : b ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hc : c ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw (a : Real.Angle) (b : Real.Angle) (c : Real.Angle) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  have forward {a b c : ℝ} (ha : a ∈ Set.Ioo cut (cut + 2 * Real.pi))
      (hb : b ∈ Set.Ioo cut (cut + 2 * Real.pi))
      (hc : c ∈ Set.Ioo cut (cut + 2 * Real.pi))
      (h : (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)) :
      sbtw (a : Real.Angle) (b : Real.Angle) (c : Real.Angle) := by
    rcases h with ⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩
    · exact sbtw_angle_of_lt_of_span_lt hab hbc (by linarith [ha.1, hc.2])
    · exact (sbtw_angle_of_lt_of_span_lt hbc hca (by linarith [hb.1, ha.2])).cyclic_right
    · exact (sbtw_angle_of_lt_of_span_lt hca hab (by linarith [hc.1, hb.2])).cyclic_left
  refine ⟨fun h => ?_, forward ha hb hc⟩
  by_contra hn
  have hrev : (c < b ∧ b < a) ∨ (b < a ∧ a < c) ∨ (a < c ∧ c < b) := by
    rcases lt_or_gt_of_ne hab with h | h <;>
      rcases lt_or_gt_of_ne hbc with k | k <;>
      rcases lt_or_gt_of_ne hac with l | l <;> tauto
  exact h.not_sbtw (forward hc hb ha hrev)

private theorem eventually_real_order {X : Type*} [TopologicalSpace X] {x : X}
    {f g : X → ℝ} (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hne : f x ≠ g x) :
    ∀ᶠ y in nhds x, f y ≠ g y ∧ (f y < g y ↔ f x < g x) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hf.eventually_lt hg hlt).mono fun _ hy => ⟨hy.ne, iff_of_true hy hlt⟩
  · exact (hg.eventually_lt hf hgt).mono fun _ hy =>
      ⟨hy.ne.symm, iff_of_false (not_lt.mpr hy.le) (not_lt.mpr hgt.le)⟩

/-- Strict order of three distinct continuously varying angles is stable in a
neighborhood. The proof chooses its own common argument cut and includes principal-branch
crossings; pairwise distinctness is required only at the point under consideration. -/
theorem eventually_sbtw_angle_iff {X : Type*} [TopologicalSpace X] {x : X}
    {f g h : X → Real.Angle} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hh : ContinuousAt h x) (hfg : f x ≠ g x) (hgh : g x ≠ h x) (hfh : f x ≠ h x) :
    ∀ᶠ y in nhds x, sbtw (f y) (g y) (h y) ↔ sbtw (f x) (g x) (h x) := by
  let cut := (-Real.pi + min (f x).toReal (min (g x).toReal (h x).toReal)) / 2
  have hcut : -Real.pi < cut := by
    have ha := Real.Angle.neg_pi_lt_toReal (f x)
    have hb := Real.Angle.neg_pi_lt_toReal (g x)
    have hc := Real.Angle.neg_pi_lt_toReal (h x)
    have hm := lt_min ha (lt_min hb hc)
    dsimp [cut]
    linarith
  have hmin : cut < min (f x).toReal (min (g x).toReal (h x).toReal) := by
    have hm := lt_min (Real.Angle.neg_pi_lt_toReal (f x))
      (lt_min (Real.Angle.neg_pi_lt_toReal (g x)) (Real.Angle.neg_pi_lt_toReal (h x)))
    dsimp [cut]
    linarith
  have hfa : (f x).toReal ∈ Set.Ioo cut (cut + 2 * Real.pi) := by
    refine ⟨hmin.trans_le (min_le_left _ _), ?_⟩
    linarith [Real.Angle.toReal_le_pi (f x)]
  have hga : (g x).toReal ∈ Set.Ioo cut (cut + 2 * Real.pi) := by
    refine ⟨hmin.trans_le ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
    linarith [Real.Angle.toReal_le_pi (g x)]
  have hha : (h x).toReal ∈ Set.Ioo cut (cut + 2 * Real.pi) := by
    refine ⟨hmin.trans_le ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
    linarith [Real.Angle.toReal_le_pi (h x)]
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let lift : Real.Angle → ℝ := fun θ => (AddCircle.equivIco (2 * Real.pi) cut θ).val
  have hlift (θ : Real.Angle) : ((lift θ : ℝ) : Real.Angle) = θ :=
    AddCircle.coe_equivIco
  have hupper (θ : Real.Angle) : lift θ < cut + 2 * Real.pi :=
    (AddCircle.equivIco (2 * Real.pi) cut θ).property.2
  have hat (θ : Real.Angle) (hθ : θ.toReal ∈ Set.Ioo cut (cut + 2 * Real.pi)) :
      lift θ = θ.toReal := by
    calc
      lift θ = lift (θ.toReal : Real.Angle) := congrArg lift (Real.Angle.coe_toReal θ).symm
      _ = θ.toReal := AddCircle.equivIco_coe_of_mem ⟨hθ.1.le, hθ.2⟩
  have hcont (θ : Real.Angle) (hθ : θ.toReal ∈ Set.Ioo cut (cut + 2 * Real.pi)) :
      ContinuousAt lift θ := by
    have hθcut : θ ≠ (cut : Real.Angle) := by
      intro heq
      have hre := congrArg Real.Angle.toReal heq
      rw [Real.Angle.toReal_coe_eq_self_iff.mpr
        ⟨hcut, hθ.1.le.trans (Real.Angle.toReal_le_pi θ)⟩] at hre
      exact (ne_of_gt hθ.1) hre
    exact continuousAt_subtype_val.comp (AddCircle.continuousAt_equivIco _ _ hθcut)
  have hF := (hcont (f x) hfa).comp hf
  have hG := (hcont (g x) hga).comp hg
  have hH := (hcont (h x) hha).comp hh
  have hFG : lift (f x) ≠ lift (g x) := by
    intro heq
    exact hfg ((hlift _).symm.trans ((congrArg (fun r : ℝ => (r : Real.Angle)) heq).trans
      (hlift _)))
  have hGH : lift (g x) ≠ lift (h x) := by
    intro heq
    exact hgh ((hlift _).symm.trans ((congrArg (fun r : ℝ => (r : Real.Angle)) heq).trans
      (hlift _)))
  have hFH : lift (f x) ≠ lift (h x) := by
    intro heq
    exact hfh ((hlift _).symm.trans ((congrArg (fun r : ℝ => (r : Real.Angle)) heq).trans
      (hlift _)))
  have hFl : cut < lift (f x) := by rw [hat _ hfa]; exact hfa.1
  have hGl : cut < lift (g x) := by rw [hat _ hga]; exact hga.1
  have hHl : cut < lift (h x) := by rw [hat _ hha]; exact hha.1
  filter_upwards [eventually_real_order hF hG hFG, eventually_real_order hG hH hGH,
    eventually_real_order hH hF hFH.symm, continuousAt_const.eventually_lt hF hFl,
    continuousAt_const.eventually_lt hG hGl, continuousAt_const.eventually_lt hH hHl]
    with y hfg' hgh' hhf' hfl hgl hhl
  have hy := sbtw_angle_iff_cyclic_lt ⟨hfl, hupper _⟩ ⟨hgl, hupper _⟩
    ⟨hhl, hupper _⟩ hfg'.1 hgh'.1 hhf'.1.symm
  have hx := sbtw_angle_iff_cyclic_lt ⟨hFl, hupper _⟩ ⟨hGl, hupper _⟩
    ⟨hHl, hupper _⟩ hFG hGH hFH
  simp only [Function.comp_apply, hlift] at hy hx
  simp only [Function.comp_apply] at hfg' hgh' hhf'
  rw [hy, hx]
  simp only [hfg'.2, hgh'.2, hhf'.2]

/-- Moving a fan center anywhere inside its cut circle preserves the literal circular
order of three distinct boundary ports. This includes all argument branches and makes no
semicircle assumption about the ports. It concerns finite straight spokes, not an ambient
homeomorphism or a topological drawing theorem. -/
theorem sbtw_arg_sub_iff_of_mem_ball {z a b p q r : ℂ} {ρ : ℝ}
    (ha : a ∈ Metric.ball z ρ) (hb : b ∈ Metric.ball z ρ)
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ)
    (hr : r ∈ Metric.sphere z ρ) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    sbtw ((p - a).arg : Real.Angle) ((q - a).arg : Real.Angle) ((r - a).arg : Real.Angle) ↔
      sbtw ((p - b).arg : Real.Angle) ((q - b).arg : Real.Angle)
        ((r - b).arg : Real.Angle) := by
  let X := {x : ℂ // x ∈ Metric.ball z ρ}
  let direction (p : ℂ) (x : X) : Real.Angle := (p - x.val).arg
  have hdir (p : ℂ) (hp : p ∈ Metric.sphere z ρ) : Continuous (direction p) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hpx : p - x.val ≠ 0 := by
      intro heq
      have hmem : p ∈ Metric.ball z ρ := (sub_eq_zero.mp heq).symm ▸ x.property
      exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp hmem
    have hsub : ContinuousAt (fun y : X => p - y.val) x :=
      continuousAt_const.sub continuousAt_subtype_val
    have hangle := (Complex.continuousAt_arg_coe_angle hpx).comp (x := x) hsub
    exact hangle
  let order (x : X) : Prop := sbtw (direction p x) (direction q x) (direction r x)
  have hlocal : IsLocallyConstant order := by
    apply (IsLocallyConstant.iff_eventually_eq order).mpr
    intro x
    have hpq' : direction p x ≠ direction q x :=
      fun heq => hpq (arg_sub_injective_on_sphere x.property hp hq heq)
    have hqr' : direction q x ≠ direction r x :=
      fun heq => hqr (arg_sub_injective_on_sphere x.property hq hr heq)
    have hpr' : direction p x ≠ direction r x :=
      fun heq => hpr (arg_sub_injective_on_sphere x.property hp hr heq)
    exact (eventually_sbtw_angle_iff (hdir p hp).continuousAt (hdir q hq).continuousAt
      (hdir r hr).continuousAt hpq' hqr' hpr').mono fun _ heq => propext heq
  let : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp
    (convex_ball z ρ).isPreconnected
  exact Iff.of_eq (hlocal.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩)

end Cslib.Polygonal
