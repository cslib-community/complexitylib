/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `GroupTheory/Perm/` or `Combinatorics/Enumerative/`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Finset.Max

/-!
# The orders putting an element last

Reading a permutation `σ` of a finite linear order as an order of its elements, every order puts
exactly one element of a nonempty set `S` last, and composing with the transposition of `i` and
`j` exchanges the orders putting `i` last among `S` and those putting `j` last. So each `i ∈ S` is
last among `S` for a `1 / #S` fraction of the orders
(`Equiv.Perm.card_mul_card_filter_forall_le_eq_factorial`).

## Main results

* `Equiv.Perm.card_filter_forall_le_eq`: symmetry between elements of `S` being placed last.
* `Equiv.Perm.card_mul_card_filter_forall_le_eq_factorial`: each element of `S` is placed last by a
  `1 / #S` fraction of all permutations.
-/

public section

open Finset

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] {S : Finset α}

omit [Fintype α] in
/-- Composing an order putting `b ∈ S` last among `S` with the transposition of `a ∈ S` and `b`
puts `a` last. -/
private theorem forall_le_mul_swap {σ : Perm α} {a b : α} (ha : a ∈ S) (hb : b ∈ S)
    (hσ : ∀ u ∈ S, σ u ≤ σ b) : ∀ u ∈ S, (σ * swap a b) u ≤ (σ * swap a b) a := by
  intro u hu
  simp only [coe_mul, Function.comp_apply, swap_apply_left]
  refine hσ _ ?_
  rcases eq_or_ne u a with rfl | hua
  · rwa [swap_apply_left]
  rcases eq_or_ne u b with rfl | hub
  · rwa [swap_apply_right]
  rwa [swap_apply_of_ne_of_ne hua hub]

/-- As many orders put `j ∈ S` last among `S` as put `i ∈ S` last. -/
theorem card_filter_forall_le_eq {i j : α} (hi : i ∈ S) (hj : j ∈ S) :
    #{σ : Perm α | ∀ u ∈ S, σ u ≤ σ j} = #{σ : Perm α | ∀ u ∈ S, σ u ≤ σ i} := by
  refine card_nbij' (· * swap i j) (· * swap i j) (fun σ hσ => ?_) (fun σ hσ => ?_)
    (fun σ _ => by simp [mul_assoc]) (fun σ _ => by simp [mul_assoc])
  · exact mem_filter.2 ⟨mem_univ _, forall_le_mul_swap hi hj (mem_filter.1 hσ).2⟩
  · rw [swap_comm]
    exact mem_filter.2 ⟨mem_univ _, forall_le_mul_swap hj hi (mem_filter.1 hσ).2⟩

/-- **Each element of `S` is last among `S` for a `1 / #S` fraction of the orders.** -/
theorem card_mul_card_filter_forall_le_eq_factorial {i : α} (hi : i ∈ S) :
    #S * #{σ : Perm α | ∀ u ∈ S, σ u ≤ σ i} = (Fintype.card α).factorial := by
  set M : α → Finset (Perm α) := fun j => {σ | ∀ u ∈ S, σ u ≤ σ j}
  -- every order puts exactly one element of `S` last
  have hcover : S.biUnion M = univ := eq_univ_of_forall fun σ => by
    obtain ⟨j, hj, hmax⟩ := exists_max_image S (fun u => σ u) ⟨i, hi⟩
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨mem_univ σ, hmax⟩⟩
  have hdisj : (S : Set α).PairwiseDisjoint M := fun j hj j' hj' hne =>
    disjoint_left.2 fun σ h h' => hne (σ.injective (le_antisymm ((mem_filter.1 h').2 j hj)
      ((mem_filter.1 h).2 j' hj')))
  calc #S * #(M i)
      = ∑ j ∈ S, #(M j) := by
        rw [sum_congr rfl fun j hj => card_filter_forall_le_eq hi hj, sum_const, smul_eq_mul]
    _ = #(S.biUnion M) := (card_biUnion hdisj).symm
    _ = _ := by rw [hcover, card_univ, Fintype.card_perm]

end Equiv.Perm
