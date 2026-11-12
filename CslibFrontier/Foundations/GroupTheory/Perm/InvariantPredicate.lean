/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Basic

/-!
# Predicates invariant under a transposition

`Equiv.predicate_swap` says that interchanging two points with equivalent predicate membership
preserves membership everywhere. The predicate need not be constant or decidable, and the
points need not exhaust its carrier. This proof is relocated unchanged from component face
surgery so vertex-identification clients can reuse it through an ordinary import.
-/

public section

namespace Equiv

variable {α : Type}

/-- A transposition preserves any predicate agreeing on its two interchanged points. -/
theorem predicate_swap [DecidableEq α] (p : α → Prop) (a b : α)
    (hab : p a ↔ p b) (x : α) : p (swap a b x) ↔ p x := by
  by_cases hxa : x = a
  · subst x; simpa only [swap_apply_left] using hab.symm
  · by_cases hxb : x = b
    · subst x; simpa only [swap_apply_right] using hab
    · rw [swap_apply_of_ne_of_ne hxa hxb]

end Equiv
