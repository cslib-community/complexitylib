/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitRestriction

/-!
# Outgoing germs after independent cuts

Each outgoing germ is multiplied by the positive width of its retained end segment.
This includes one-segment routes, where the opposite cut also changes that width.
-/

public section

namespace Cslib.Polygonal.Route

/-- Independent cuts scale each outgoing germ by its retained segment width. -/
theorem germ_cutEnds (p : Route) (s t : ℝ) (side : Bool) :
    (p.cutEnds s t).germ side =
      (p.cutUpper t (p.endSegment side) - p.cutLower s (p.endSegment side)) • p.germ side := by
  have h : (p.cutEnds s t).germ side =
      (p.cutEnds s t).eval ((p.cutEnds s t).endSegment side) (endTime side 1) -
        (p.cutEnds s t).eval ((p.cutEnds s t).endSegment side) (endTime side 0) := by
    rw [eval_near_end, eval_near_end]
    simp
  rw [h]
  cases side
  · simp only [endSegment, endTime, Bool.false_eq_true, ↓reduceIte]
    apply (congrArg₂ (fun x y : ℂ => x - y)
      (p.eval_cutEnds s t 0 1) (p.eval_cutEnds s t 0 0)).trans
    simp only [cutTime,
      eval, AffineMap.lineMap_apply_module', germ, Bool.false_eq_true, ↓reduceIte,
      start, Fin.castSucc_zero]
    module
  · simp only [endSegment, endTime, ↓reduceIte, sub_self, sub_zero]
    apply (congrArg₂ (fun x y : ℂ => x - y)
      (p.eval_cutEnds s t (Fin.last p.bends) 0)
      (p.eval_cutEnds s t (Fin.last p.bends) 1)).trans
    simp only [cutTime,
      eval, AffineMap.lineMap_apply_module', germ, ↓reduceIte, finish, Fin.succ_last]
    module

/-- Valid independent cuts preserve each literal outgoing argument. -/
theorem arg_germ_cutEnds (p : Route) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t < 1) (side : Bool) :
    ((p.cutEnds s t).germ side).arg = (p.germ side).arg := by
  rw [germ_cutEnds, Complex.real_smul,
    Complex.arg_real_mul _ (sub_pos.mpr (p.cut_bounds hs ht hst _).2.1)]

end Cslib.Polygonal.Route
