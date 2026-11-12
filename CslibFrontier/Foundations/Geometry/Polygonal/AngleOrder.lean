/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Circular order within one real turn

Increasing real representatives whose span is less than a full turn retain their strict
circular order as angles. This graph-free fact supports horizontal ports and moving fans
without requiring the same argument cut.
-/

public section

namespace Cslib.Polygonal

/-- Increasing real representatives with span less than a full turn give the literal
counterclockwise strict angle order, without a principal-argument cut restriction. -/
theorem sbtw_angle_of_lt_of_span_lt {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hspan : c - a < 2 * Real.pi) :
    sbtw (a : Real.Angle) (b : Real.Angle) (c : Real.Angle) := by
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
  have ha : toIocMod hp c a = a + 2 * Real.pi := by
    apply (toIocMod_eq_iff hp).mpr
    refine ⟨⟨by linarith, by linarith⟩, -1, ?_⟩
    simp only [neg_one_zsmul]
    ring
  rw [hb, ha]
  linarith

end Cslib.Polygonal
