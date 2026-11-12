/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Clockwise order of ports on a horizontal line

The rays from the origin to `(x,1)`, for positive `x`, run clockwise as `x` increases.
The order is proved for the actual complex arguments in the fixed plane.
-/

public section

namespace Cslib.Polygonal

/-- The argument of a positive horizontal port lies in the first quadrant. -/
theorem arg_port_mem {x : ℝ} (hx : 0 < x) :
    (⟨x, 1⟩ : ℂ).arg ∈ Set.Ioo 0 (Real.pi / 2) := by
  refine ⟨?_, Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hx)⟩
  exact lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr (by norm_num)) (by
    intro h
    have htan := Complex.tan_arg (⟨x, 1⟩ : ℂ)
    rw [← h, Real.tan_zero] at htan
    exact (one_div_ne_zero (ne_of_gt hx)) htan.symm)

private theorem arg_port_eq_arctan {x : ℝ} (hx : 0 < x) :
    (⟨x, 1⟩ : ℂ).arg = Real.arctan (1 / x) := by
  have h := arg_port_mem hx
  rw [← Complex.tan_arg (⟨x, 1⟩ : ℂ), Real.arctan_tan]
  · linarith [h.1, Real.pi_pos]
  · exact h.2

/-- Moving a positive port to the right strictly decreases its actual real argument. -/
theorem arg_port_strictAnti : StrictAntiOn (fun x : ℝ => (⟨x, 1⟩ : ℂ).arg) (Set.Ioi 0) := by
  intro x hx y hy hxy
  dsimp only
  rw [arg_port_eq_arctan hx, arg_port_eq_arctan hy, Real.arctan_lt_arctan_iff]
  exact one_div_lt_one_div_of_lt hx hxy

/-- Increasing real arguments within one turn have their literal counterclockwise order. -/
theorem sbtw_angle_of_lt {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c)
    (hc : c < 2 * Real.pi) : sbtw (a : Real.Angle) (b : Real.Angle) (c : Real.Angle) := by
  have hp := Real.two_pi_pos
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨hp⟩
  rw [sbtw_iff_not_btw]
  change ¬btw (c : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
    (b : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
    (a : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
  rw [QuotientAddGroup.btw_coe_iff]
  have hb : toIcoMod hp c b = b + 2 * Real.pi := by
    apply (toIcoMod_eq_iff hp).mpr
    refine ⟨⟨by linarith, by linarith⟩, -1, ?_⟩
    simp only [neg_one_zsmul]
    ring
  have hac : toIocMod hp c a = a + 2 * Real.pi := by
    apply (toIocMod_eq_iff hp).mpr
    refine ⟨⟨by linarith, by linarith⟩, -1, ?_⟩
    simp only [neg_one_zsmul]
    ring
  rw [hb, hac]
  linarith

/-- Positive ports in increasing order give the required reversed argument triple. -/
theorem clockwise_ports {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    sbtw ((⟨c, 1⟩ : ℂ).arg : Real.Angle) ((⟨b, 1⟩ : ℂ).arg : Real.Angle)
      ((⟨a, 1⟩ : ℂ).arg : Real.Angle) := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  apply sbtw_angle_of_lt (arg_port_mem hc).1.le
    (arg_port_strictAnti hb hc hbc) (arg_port_strictAnti ha hb hab)
  linarith [(arg_port_mem ha).2, Real.pi_pos]

/-- Distinct positive ports have different geometric ray directions. -/
theorem direction_port_injective {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (heq : ((⟨a, 1⟩ : ℂ).arg : Real.Angle) = ((⟨b, 1⟩ : ℂ).arg : Real.Angle)) :
    a = b := by
  have harg := congrArg Real.Angle.toReal heq
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
    Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩] at harg
  exact arg_port_strictAnti.injOn ha hb harg

/-- All distinct positive ports have precisely the cyclic clockwise order of their
horizontal coordinates, with no reflection or choice of a new orientation. -/
theorem clockwise_ports_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw ((⟨c, 1⟩ : ℂ).arg : Real.Angle) ((⟨b, 1⟩ : ℂ).arg : Real.Angle)
      ((⟨a, 1⟩ : ℂ).arg : Real.Angle) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  have forward {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
      (h : (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)) :
      sbtw ((⟨z, 1⟩ : ℂ).arg : Real.Angle) ((⟨y, 1⟩ : ℂ).arg : Real.Angle)
        ((⟨x, 1⟩ : ℂ).arg : Real.Angle) := by
    rcases h with ⟨hxy, hyz⟩ | ⟨hyz, hzx⟩ | ⟨hzx, hxy⟩
    · exact clockwise_ports hx hxy hyz
    · exact (clockwise_ports hy hyz hzx).cyclic_left
    · exact (clockwise_ports hz hzx hxy).cyclic_right
  refine ⟨fun h => ?_, forward ha hb hc⟩
  by_contra hn
  have hrev : (c < b ∧ b < a) ∨ (b < a ∧ a < c) ∨ (a < c ∧ c < b) := by
    rcases lt_or_gt_of_ne hab with h | h <;>
      rcases lt_or_gt_of_ne hbc with k | k <;>
      rcases lt_or_gt_of_ne hac with l | l <;> tauto
  exact h.not_sbtw (forward hc hb ha hrev)

end Cslib.Polygonal
