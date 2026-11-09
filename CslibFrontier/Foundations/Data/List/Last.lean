/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Init.Data.List.Lemmas

/-!
# Defaulted last-element lookup

The default is unused for a nonempty list. This indexed form follows from the core last-element
lookup API. The default of an append is threaded through its left part, which is how the endpoint
of a concatenated walk is computed.

## Main results

* `List.getLastD_eq_getElem`.
* `List.getLastD_append`.
-/

@[expose] public section

namespace List

/-- A nonempty list's defaulted last lookup is its final indexed element. -/
theorem getLastD_eq_getElem {α : Type*} (xs : List α) (d : α) (hne : xs ≠ []) :
    xs.getLastD d = xs[xs.length - 1]'(by cases xs <;> simp_all) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
  exact List.getLast_eq_getElem hne

/-- The defaulted last element of an append: the right part's, with the left part's as default. -/
theorem getLastD_append {α : Type*} (l₁ l₂ : List α) (d : α) :
    (l₁ ++ l₂).getLastD d = l₂.getLastD (l₁.getLastD d) := by
  induction l₁ generalizing d with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append, List.getLastD_cons, ih]

end List
