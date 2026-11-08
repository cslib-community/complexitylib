/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.Route

/-!
# Single-segment polygonal routes

The one-segment constructor and simplicity criterion connect finite route data to
Mathlib's actual real affine segment. In particular a one-segment loop is not simple.
-/

public section

namespace Cslib.Polygonal.Route

/-- One actual real planar segment, including its two distinct parameter ends. -/
@[expose] def line (a b : ℂ) : Route where
  bends := 0
  point := fun i => if i = 0 then a else b

/-- The first end of a single-segment route. -/
@[simp] theorem start_line (a b : ℂ) : (line a b).start = a := rfl

/-- The last end of a single-segment route. -/
@[simp] theorem finish_line (a b : ℂ) : (line a b).finish = b := rfl

/-- Evaluating the single-segment route is Mathlib's full real affine interpolation. -/
theorem eval_line (a b : ℂ) (i : Fin (line a b).segments) (t : ℝ) :
    (line a b).eval i t = AffineMap.lineMap a b t := by
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  rfl

/-- A segment joining distinct points is a simple polygonal route. -/
theorem isSimple_line {a b : ℂ} (hab : a ≠ b) : (line a b).IsSimple := by
  intro i j s t _ _ heq
  left
  rw [eval_line, eval_line] at heq
  have hst : s = t := AffineMap.lineMap_injective ℝ hab heq
  have hij : i = j := Subsingleton.elim (α := Fin 1) _ _
  rw [hij, hst]

/-- Nondegeneracy is necessary as well as sufficient, even if a route is allowed to close. -/
theorem isSimple_line_iff (a b : ℂ) : (line a b).IsSimple ↔ a ≠ b :=
  ⟨fun h => h.segment_ne 0, isSimple_line⟩

end Cslib.Polygonal.Route
