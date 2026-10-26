/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
import Mathlib.Data.List.GetD

/-!
# Defaulted last-element lookup

The default is unused for a nonempty list. The proof is moved from the path semantics.

## Main results

* `List.getLastD_eq_getElem`.
-/

@[expose] public section

namespace List

/-- A nonempty list's defaulted last lookup is its final indexed element. -/
theorem getLastD_eq_getElem {α : Type*} (xs : List α) (d : α) (hne : xs ≠ []) :
    xs.getLastD d = xs[xs.length - 1]'(by cases xs <;> simp_all) := by
  induction xs generalizing d with
  | nil => exact False.elim (hne rfl)
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      rw [List.getLastD_cons, ih a (List.cons_ne_nil _ _)]
      simp only [List.length_cons, Nat.add_sub_cancel, List.getElem_cons_succ]


end List
