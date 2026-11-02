/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Mathlib.Data.List.Perm.Basic

/-!
# Lifting a permutation through `List.map`

If `l` is a permutation of `l'.map f`, some permutation of `l'` maps onto `l` exactly. This
reorders a list of objects to follow a given order of their images: for example, the trees of a
forest in the order in which a linked list visits their roots.

## Main results

* `List.Perm.exists_perm_map_eq`: the lifted permutation.
-/

@[expose] public section

namespace List

/-- If `l` is a permutation of `l'.map f`, some permutation of `l'` maps onto `l` exactly. -/
theorem Perm.exists_perm_map_eq {α β : Type*} {f : α → β} :
    ∀ {l : List β} {l' : List α}, l.Perm (l'.map f) → ∃ l'' : List α, l''.Perm l' ∧ l''.map f = l
  | [], l', h => ⟨[], by simpa using (List.perm_nil.mp h.symm).symm, rfl⟩
  | b :: l, l', h => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (h.subset List.mem_cons_self)
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
    have hl : l.Perm ((l₁ ++ l₂).map f) := (List.perm_cons (f a)).mp (h.trans (by simp))
    obtain ⟨l'', hp, rfl⟩ := exists_perm_map_eq hl
    exact ⟨a :: l'', (hp.cons a).trans List.perm_middle.symm, rfl⟩

end List
