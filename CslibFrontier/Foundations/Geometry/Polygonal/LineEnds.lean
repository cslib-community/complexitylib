/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Segment

/-!
# Ends and outgoing germs of a single planar segment

Both end tags refer to the literal orientation from the first named point to the second.
-/

public section

namespace Cslib.Polygonal.Route

/-- A single segment reaches its tagged end exactly at the corresponding unit time. -/
theorem atEnd_line_iff (a b : ℂ) (i : Fin (line a b).segments) (t : ℝ) (side : Bool) :
    (line a b).AtEnd i t side ↔ t = if side then 1 else 0 := by
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  cases side <;> simp [AtEnd, position, line, segments]

/-- The two outgoing germs of a single segment retain their opposite orientations. -/
theorem germ_line (a b : ℂ) (side : Bool) :
    (line a b).germ side = if side then a - b else b - a := by
  cases side <;> rfl

end Cslib.Polygonal.Route
