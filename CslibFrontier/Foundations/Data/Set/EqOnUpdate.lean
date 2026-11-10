/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Set/Function.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Set.Function

/-!
# Agreement on a set after updating a function

Two functions that agree on a set `s` still agree on `insert i s` after both are updated at `i`
to the same value (`Set.EqOn.update_insert`). The pebble games of finite-variable logic use this
to move a pebble in two positions that agree on the placed pebbles.

## Main results

* `Set.EqOn.update_insert`: updating two functions that agree on `s` at `i` to the same value
  gives functions that agree on `insert i s`.
-/

public section

namespace Set

variable {ι α : Type*} [DecidableEq ι]

/-- Updating two functions that agree on `s` at `i` to the same value gives functions that agree on
`insert i s`. -/
theorem EqOn.update_insert {s : Set ι} {f g : ι → α} (h : EqOn f g s) (i : ι) (c : α) :
    EqOn (Function.update f i c) (Function.update g i c) (insert i s) := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
  · rw [Function.update_of_ne hji, Function.update_of_ne hji]
    exact h ((mem_insert_iff.1 hj).resolve_left hji)

end Set
