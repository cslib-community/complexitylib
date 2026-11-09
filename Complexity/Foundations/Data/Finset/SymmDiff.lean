/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Order.SymmDiff

/-!
# Symmetric difference on finsets and finite types

This module gathers algebraic and combinatorial properties of symmetric difference on finite sets:

* In a generalized Boolean algebra `b ↦ a ∆ b` is an involution, so over a finite generalized
  Boolean algebra the product of `f (a ∆ b)` over all `b` is the product of `f b` over all `b`
  (`Fintype.prod_symmDiff`, `Fintype.sum_symmDiff`).
* Symmetric difference of a finset with a singleton: `s ∆ {t}` removes `t` if present and inserts
  it otherwise (`Finset.symmDiff_singleton_eq`), bounding the cardinality by `s.card + 1`
  (`Finset.card_symmDiff_singleton_le`). In general `#(s ∆ t) ≤ #s + #t`
  (`Finset.card_symmDiff_le`).
* Summing over `s ∆ {t}` adds `val t` when elements have order at most 2, in particular in the
  Boolean ring `Bool` (`Finset.sum_symmDiff_singleton`).

## Main results

* `Fintype.prod_symmDiff`, `Fintype.sum_symmDiff`: reindexing a product or a sum by a symmetric
  difference.
* `Finset.symmDiff_singleton_eq`: symmetric difference with a singleton as conditional erase/insert.
* `Finset.mem_symmDiff_singleton`: membership in `s ∆ {t}`.
* `Finset.card_symmDiff_le`, `Finset.card_symmDiff_singleton_le`: cardinality bounds for `s ∆ t`
  and `s ∆ {t}`.
* `Finset.sum_symmDiff_singleton`: summing over `s ∆ {t}` adds `val t` in `Bool`.
-/

@[expose] public section

open scoped symmDiff BigOperators

namespace Fintype

variable {α M : Type*} [Fintype α] [GeneralizedBooleanAlgebra α] [CommMonoid M]

/-- Reindexing a product over a finite generalized Boolean algebra by the involution
`b ↦ a ∆ b`. -/
@[to_additive /-- Reindexing a sum over a finite generalized Boolean algebra by the involution
`b ↦ a ∆ b`. -/]
theorem prod_symmDiff (a : α) (f : α → M) : ∏ b, f (symmDiff a b) = ∏ b, f b :=
  Equiv.prod_comp (Function.Involutive.toPerm _ (symmDiff_right_involutive a)) f

end Fintype

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Adding `t` to a finset by symmetric difference removes it if present and inserts it
otherwise. -/
theorem symmDiff_singleton_eq (s : Finset α) (t : α) :
    s ∆ {t} = if t ∈ s then s.erase t else insert t s := by
  ext z
  by_cases hz : z = t
  · subst hz
    split_ifs with h <;> simp [Finset.mem_symmDiff, h]
  · split_ifs <;> simp [Finset.mem_symmDiff, hz]

/-- An element belongs to `s ∆ {t}` if and only if its membership in `s` differs from equality
with `t`. -/
theorem mem_symmDiff_singleton {s : Finset α} {t z : α} : z ∈ s ∆ {t} ↔ (z ∈ s ↔ z ≠ t) := by
  rw [symmDiff_singleton_eq]
  by_cases hz : z = t
  · subst hz
    split_ifs with ht <;> simp [ht]
  · split_ifs with ht <;> simp [hz]

/-- The cardinality of `s ∆ t` is at most `s.card + t.card`. -/
theorem card_symmDiff_le (s t : Finset α) : (s ∆ t).card ≤ s.card + t.card :=
  (card_le_card symmDiff_subset_union).trans (card_union_le _ _)

/-- The cardinality of `s ∆ {t}` is at most `s.card + 1`. -/
theorem card_symmDiff_singleton_le (s : Finset α) (t : α) :
    (s ∆ {t}).card ≤ s.card + 1 := by
  rw [symmDiff_singleton_eq]
  split_ifs with h
  · exact Finset.card_erase_le.trans (Nat.le_succ _)
  · exact Finset.card_insert_le _ _

/-- In an additive commutative monoid where every element has order at most 2, summing over
`s ∆ {t}` adds `val t`. -/
theorem sum_symmDiff_singleton_of_add_self {M : Type*} [AddCommMonoid M]
    (h_self : ∀ x : M, x + x = 0) (s : Finset α) (t : α) (val : α → M) :
    ∑ i ∈ s ∆ {t}, val i = ∑ i ∈ s, val i + val t := by
  rw [symmDiff_singleton_eq]
  split_ifs with ht
  · rw [← Finset.add_sum_erase s val ht, add_comm (val t), add_assoc, h_self, add_zero]
  · rw [Finset.sum_insert ht, add_comm]

/-- Summing a Boolean-valued function over `s ∆ {t}` adds `val t` in the Boolean ring. -/
theorem sum_symmDiff_singleton (s : Finset α) (t : α) (val : α → Bool) :
    ∑ i ∈ s ∆ {t}, val i = ∑ i ∈ s, val i + val t :=
  sum_symmDiff_singleton_of_add_self (fun _ => BooleanRing.add_self _) s t val

end Finset

