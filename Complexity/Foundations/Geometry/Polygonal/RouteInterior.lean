/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.Route
import Mathlib.Tactic.Linarith

/-!
# Interior parameters of polygonal routes

An interior parameter of any listed segment lies strictly between the two original
route ends. This separates actual segment interiors from permitted loop closure contacts.
-/

public section

namespace Cslib.Polygonal.Route

/-- An interior segment parameter is never either original route end. -/
theorem not_atEnd_of_mem_Ioo (p : Route) (i : Fin p.segments)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) (tag : Bool) : ¬p.AtEnd i t tag := by
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi1 : (i.val : ℝ) + 1 ≤ p.segments := by exact_mod_cast i.isLt
  cases tag <;> simp only [AtEnd, position, Bool.false_eq_true, ↓reduceIte]
  · linarith [ht.1]
  · linarith [ht.2]

end Cslib.Polygonal.Route
