/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.Analysis.Complex.Arg

/-!
# Outgoing segments and small intersections of equal planar rays

These elementary geometric lemmas relate actual polygonal segments to their outgoing
germs. Equal nonzero arguments yield common points at arbitrarily small positive segment
parameters; no disk or isotopy provider is assumed.

## Main results

* `Cslib.Polygonal.exists_small_smul_eq_of_arg_eq`: equal rays meet at small positive parameters.
* `Cslib.Polygonal.Route.eval_near_end`: actual interpolation along an outgoing germ.
* `Cslib.Polygonal.Route.position_near_end_mem`: these parameters are inside the whole route.
-/

public section

namespace Cslib.Polygonal

/-- Two nonzero complex vectors with the same argument have equal positive scalar multiples
with both scalars smaller than any prescribed positive bound. -/
theorem exists_small_smul_eq_of_arg_eq {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (harg : u.arg = v.arg) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s ∈ Set.Ioo 0 δ, ∃ t ∈ Set.Ioo 0 δ, s • u = t • v := by
  obtain ⟨a, b, ha, hb, hab⟩ := (Complex.sameRay_of_arg_eq harg).exists_pos hu hv
  have hk : 0 < a + b + 1 := by linarith
  have hsmall (c : ℝ) (hc : 0 < c) (hck : c < a + b + 1) :
      δ / (a + b + 1) * c ∈ Set.Ioo 0 δ := by
    constructor
    · exact mul_pos (div_pos hδ hk) hc
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hk]
      exact mul_lt_mul_of_pos_left hck hδ
  refine ⟨δ / (a + b + 1) * a, hsmall a ha (by linarith),
    δ / (a + b + 1) * b, hsmall b hb (by linarith), ?_⟩
  rw [mul_smul, mul_smul, hab]

namespace Route

variable (p : Route)

/-- First segment at the first end; last segment at the last end. -/
@[expose] def endSegment (b : Bool) : Fin p.segments := if b then Fin.last p.bends else 0

/-- Local outgoing time converted to the orientation of a listed segment. -/
@[expose] def endTime (b : Bool) (t : ℝ) : ℝ := if b then 1 - t else t

/-- Conversion to listed-segment time preserves the unit parameter interval. -/
theorem endTime_mem (b : Bool) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    endTime b t ∈ Set.Icc 0 1 := by
  cases b
  · exact ht
  · constructor <;> dsimp [endTime] <;> linarith [ht.1, ht.2]

/-- The actual segment at outgoing time `t` is the endpoint plus `t` times its germ. -/
theorem eval_near_end (b : Bool) (t : ℝ) :
    p.eval (p.endSegment b) (endTime b t) = p.endpoint b + t • p.germ b := by
  cases b
  · simp [eval, endSegment, endTime, endpoint, germ, start, AffineMap.lineMap_apply_module',
      add_comm]
  · simp only [eval, endSegment, endTime, ↓reduceIte, AffineMap.lineMap_apply_one_sub,
      endpoint, germ, finish, Fin.succ_last]
    rw [AffineMap.lineMap_apply_module', add_comm]

/-- The global parameter of a point on an outgoing segment, including the final segment's
reversed local orientation. -/
theorem position_near_end (b : Bool) (t : ℝ) :
    p.position (p.endSegment b) (endTime b t) =
      if b then (p.segments : ℝ) - t else t := by
  cases b <;> simp [position, endSegment, endTime, segments]; ring

/-- A strictly internal outgoing time is strictly internal to the entire chain. -/
theorem position_near_end_mem (b : Bool) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    p.position (p.endSegment b) (endTime b t) ∈ Set.Ioo 0 (p.segments : ℝ) := by
  have hn : (1 : ℝ) ≤ p.segments := by exact_mod_cast Nat.le_add_left 1 p.bends
  rw [position_near_end]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [ht.1, ht.2]

/-- Strictly internal outgoing parameters are neither end of the entire route. -/
theorem not_atEnd_near_end (b c : Bool) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ¬p.AtEnd (p.endSegment b) (endTime b t) c := by
  have h := p.position_near_end_mem b ht
  cases c <;> dsimp [AtEnd] <;> linarith [h.1, h.2]

end Route
end Cslib.Polygonal
