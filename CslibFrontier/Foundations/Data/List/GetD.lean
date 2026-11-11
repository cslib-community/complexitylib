/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/GetD.lean`)

public import CslibFrontier.Init
import Mathlib.Data.List.GetD

/-!
# Membership of in-range defaulted lookups

A defaulted lookup `l.getD i d` at an index `i < l.length` returns an entry of `l`. Statements
that read lists with `getD` use this to apply a property of all entries; the general case, where
the lookup may return the default, is `List.getD_mem_or`.

## Main results

* `List.getD_mem`: `l.getD i d ∈ l` for `i < l.length`.
-/

public section

namespace List

/-- An in-range defaulted lookup returns an entry of the list, whatever the default. -/
theorem getD_mem {α : Type*} (d : α) {l : List α} {i : ℕ} (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [getD_eq_getElem _ _ hi]
  exact getElem_mem hi

end List
