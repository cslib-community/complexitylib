/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Operations

/-!
# First-occurrence indices under injective maps on a list

`List.idxOf_map_injOn` preserves the first occurrence of a member when the map is
injective only on the elements that occur. Repeated elements are allowed, and the map
may behave arbitrarily outside the list. Membership of the searched value is required.
The proof is relocated unchanged from CNF compaction's relabeling API.
-/

public section

namespace List

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- An injection on occurring elements preserves the first-occurrence index of a member. -/
theorem idxOf_map_injOn (l : List V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ l}) {v : V} (hv : v ∈ l) :
    (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons a l ih =>
    by_cases h : a = v
    · subst a
      simp
    · have hv' : v ∈ l := List.mem_of_ne_of_mem (Ne.symm h) hv
      have hfa : f a ≠ f v := fun heq => h (hf (by simp) hv heq)
      rw [List.map_cons, List.idxOf_cons_ne _ hfa, List.idxOf_cons_ne _ h]
      exact congrArg Nat.succ (ih
        (fun _ hx _ hy => hf (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem a hy)) hv')

end List
