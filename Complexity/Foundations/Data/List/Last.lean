/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
import Init.Data.List.Lemmas

/-!
# Defaulted last-element lookup

The default is unused for a nonempty list. This indexed form follows from the core last-element
lookup API.

## Main results

* `List.getLastD_eq_getElem`.
-/

@[expose] public section

namespace List

/-- A nonempty list's defaulted last lookup is its final indexed element. -/
theorem getLastD_eq_getElem {α : Type*} (xs : List α) (d : α) (hne : xs ≠ []) :
    xs.getLastD d = xs[xs.length - 1]'(by cases xs <;> simp_all) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
  exact List.getLast_eq_getElem hne

end List
