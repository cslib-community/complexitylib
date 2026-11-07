/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Data/Fintype/Perm.lean`)

public import Complexity.Init
public import Mathlib.Data.Fintype.Perm

/-!
# Counting the permutations that fix a set

The permutations of a finite type `α` that fix every point of a set `U` are the permutations of
the complement of `U`, so there are `(#α - #U)!` of them
(`Equiv.Perm.card_filter_forall_eq_self`).

## Main results

* `Equiv.Perm.card_filter_forall_eq_self`: `(#α - #U)!` permutations fix every point of `U`.
-/

public section

open Finset
open scoped Nat

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The permutations fixing a set** of a finite type `α` number `(#α - #U)!`. -/
theorem card_filter_forall_eq_self (U : Finset α) :
    #{τ : Perm α | ∀ u ∈ U, τ u = u} = (Fintype.card α - U.card)! := by
  rw [← Fintype.card_subtype]
  calc Fintype.card {τ : Perm α // ∀ u ∈ U, τ u = u}
      = Fintype.card (Perm {a : α // a ∉ U}) :=
        Fintype.card_congr ((Equiv.subtypeEquivRight fun τ => by
          simp only [not_not]).trans (Perm.subtypeEquivSubtypePerm (· ∉ U)).symm)
    _ = (Fintype.card α - U.card)! := by
        rw [Fintype.card_perm, Fintype.card_subtype, filter_not, card_sdiff_of_subset
          (subset_univ _), filter_mem_eq_inter, univ_inter, card_univ]

end Equiv.Perm
