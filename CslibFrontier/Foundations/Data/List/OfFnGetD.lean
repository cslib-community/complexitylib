/-
Copyright (c) 2026 Jonathan Katz, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.List.GetD

/-!
# Tabulating a list by defaulted lookup

Reading every index of a list of length `n` with `List.getD` and tabulating the result over
`Fin n` gives back the list. These are the `getD` forms of core's `List.ofFn_getElem` and
Mathlib's `List.ofFn_getElem_eq_map`, for when the length is only known to be `n`.

## Main results

* `List.ofFn_getD_eq_of_length`: `List.ofFn (fun i : Fin n => l.getD i d) = l` when
  `l.length = n`.
* `List.ofFn_getD_eq_map_of_length`: the same after applying `f` to every entry.
-/

public section

namespace List

variable {α β : Type*}

/-- Tabulating the defaulted lookups of a list of length `n` over `Fin n` gives back the list. -/
theorem ofFn_getD_eq_of_length (d : α) {n : ℕ} {l : List α} (hl : l.length = n) :
    ofFn (fun i : Fin n => l.getD i d) = l := by
  refine ext_getElem (by simp [hl]) fun i _ hi => ?_
  simp [getElem?_eq_getElem hi]

/-- Tabulating `f` of the defaulted lookups of a list of length `n` over `Fin n` maps `f` over
the list. -/
theorem ofFn_getD_eq_map_of_length (f : α → β) (d : α) {n : ℕ} {l : List α}
    (hl : l.length = n) : ofFn (fun i : Fin n => f (l.getD i d)) = l.map f := by
  conv_rhs => rw [← ofFn_getD_eq_of_length d hl]
  rw [map_ofFn]
  rfl

end List
