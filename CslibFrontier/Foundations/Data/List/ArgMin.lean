/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/MinMax.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.MinMax

/-!
# The first minimizer of a nonempty list

Mathlib's `List.argmin f l` is `none` exactly on the empty list. Algorithms that select a
cheapest candidate usually need the positive form, and often read the choice off with a
default through `Option.getD`. This file provides those forms.

## Main results

* `List.exists_argmin_eq_some`: a nonempty list has a first minimizer.
* `List.getD_argmin_mem`: on a nonempty list, the minimizer read with any default is a member.
* `List.getD_argmin_le`: the minimizer read with any default is at most every member.
-/

public section

namespace List

variable {α β : Type*} [LinearOrder β] {f : α → β} {l : List α}

/-- A nonempty list has a first minimizer. -/
theorem exists_argmin_eq_some (hl : l ≠ []) : ∃ m, l.argmin f = some m :=
  Option.ne_none_iff_exists'.1 (mt argmin_eq_none.1 hl)

/-- On a nonempty list, the first minimizer read with any default is a member of the list. -/
theorem getD_argmin_mem (hl : l ≠ []) (d : α) : (l.argmin f).getD d ∈ l := by
  obtain ⟨m, hm⟩ := exists_argmin_eq_some (f := f) hl
  rw [hm, Option.getD_some]
  exact argmin_mem hm

/-- The first minimizer read with any default is at most every member of the list. -/
theorem getD_argmin_le {x : α} (hx : x ∈ l) (d : α) : f ((l.argmin f).getD d) ≤ f x := by
  obtain ⟨m, hm⟩ := exists_argmin_eq_some (f := f) (ne_nil_of_mem hx)
  rw [hm, Option.getD_some]
  exact le_of_mem_argmin hx hm

end List
