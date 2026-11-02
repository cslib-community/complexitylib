/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic

/-!
# `filterMap` as a filter followed by a map

`l.filterMap f` keeps the elements on which `f` is defined and maps them by `f`, read with any
default (`List.filterMap_eq_map_filter`). This is the form that list combinators which filter and
map separately compute.

## Main results

* `List.filterMap_eq_map_filter`: `l.filterMap f` is `l.filter (f · |>.isSome)` mapped by
  `(f · |>.getD d)`.
-/

public section

namespace List

/-- `filterMap` is a filter by definedness followed by a map, read with any default. -/
theorem filterMap_eq_map_filter {α β : Type*} (l : List α) (f : α → Option β) (d : β) :
    l.filterMap f = (l.filter fun a => (f a).isSome).map fun a => (f a).getD d := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : f a <;> simp [h, ih]

end List
