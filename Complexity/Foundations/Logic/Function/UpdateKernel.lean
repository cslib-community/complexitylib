/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib Logic/Function/Basic)

public import Complexity.Init
public import Mathlib.Logic.Function.Basic

/-!
# The kernel of a one-point identification

Updating the identity at `b` to `a` identifies just those two points. No distinctness,
finiteness or injectivity premise is required. This elementary original identity supports
comparison of actual source labels with their dense incidence names.
-/

public section

namespace Function

/-- A one-point update of the identity equates precisely equal points or the selected pair. -/
theorem update_id_apply_eq_iff {α : Sort*} [DecidableEq α] (a b x y : α) :
    update id b a x = update id b a y ↔
      x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  by_cases hx : x = b <;> by_cases hy : y = b <;>
    simp only [update_apply, hx, hy, ite_true, ite_false, id_eq] <;> grind

end Function
