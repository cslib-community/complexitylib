/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib.Algebra.BigOperators.Group.Finset.Piecewise)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products and sums over an updated function

Changing one argument of a function changes only the matching factor of a product (or summand of
a sum) whose factors depend on the arguments one at a time
(`Finset.prod_apply_update_of_mem`). Unlike Mathlib's `Finset.prod_update_of_mem`, the factors may
apply a different map `g j` to each argument and the arguments may have dependent types, and the
untouched factors are collected over `s.erase i`, the form produced by `Finset.mul_prod_erase`.

## Main results

* `Finset.prod_apply_update_of_mem`, `Finset.sum_apply_update_of_mem`: for `i ∈ s`,
  `∏ j ∈ s, g j (Function.update f i b j) = g i b * ∏ j ∈ s.erase i, g j (f j)`.
-/

public section

namespace Finset

/-- Changing the argument at `i ∈ s` changes only the `i`-th factor of a product whose `j`-th
factor depends only on the `j`-th argument. -/
@[to_additive /-- Changing the argument at `i ∈ s` changes only the `i`-th summand of a sum whose
`j`-th summand depends only on the `j`-th argument. -/]
theorem prod_apply_update_of_mem {ι M : Type*} {α : ι → Type*} [CommMonoid M] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∈ s) (g : ∀ j, α j → M) (f : ∀ j, α j) (b : α i) :
    ∏ j ∈ s, g j (Function.update f i b j) = g i b * ∏ j ∈ s.erase i, g j (f j) := by
  rw [← mul_prod_erase s _ hi, Function.update_self]
  congr 1
  exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]

end Finset
