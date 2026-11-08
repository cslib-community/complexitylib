/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Finset.Max

/-!
# Extreme elements of uniform random orders

For any finite set `S` of size `k > 0` in `α` and any finite linear order `β`, a bijection
`σ : α ≃ β` puts each element `u ∈ S` least among `S` for exactly a `1 / k` fraction of all
bijections (`card_filter_least_mul_card`). By transposition symmetry, swapping `u` and `v`
in `α` gives a bijection between the orders putting `u` least and those putting `v` least.
Since every order has a unique minimum on the nonempty set `S`, these fibers partition `α ≃ β`.

The dual statements for greatest elements (`card_filter_greatest_mul_card`) and for permutations
(`card_filter_perm_least_mul_card`, `card_filter_perm_greatest_mul_card`,
`card_filter_perm_symm_greatest_mul_card`) follow immediately.

## Main results

* `Cslib.Probability.card_filter_least_mul_card`: each `u ∈ S` is minimal on `S` for a `1 / #S`
  fraction of the bijections `α ≃ β`.
* `Cslib.Probability.card_filter_greatest_mul_card`: each `u ∈ S` is maximal on `S` for a `1 / #S`
  fraction of the bijections `α ≃ β`.
* `Cslib.Probability.card_filter_perm_least_mul_card`,
  `Cslib.Probability.card_filter_perm_greatest_mul_card`,
  `Cslib.Probability.card_filter_perm_symm_greatest_mul_card`: permutation specializations.
-/

public section

open Finset

namespace Cslib.Probability

private theorem swap_least {α β : Type*} [DecidableEq α] [LinearOrder β]
    {S : Finset α} {a b : α} (hb : b ∈ S) {σ : α ≃ β}
    (hσ : ∀ w ∈ S, w ≠ a → σ a < σ w) :
    ∀ w ∈ S, w ≠ b → ((Equiv.swap a b).trans σ) b < ((Equiv.swap a b).trans σ) w := by
  intro w hw hwb
  simp only [Equiv.trans_apply, Equiv.swap_apply_right]
  by_cases hwa : w = a
  · rw [hwa, Equiv.swap_apply_left]
    exact hσ b hb (fun h => hwb (hwa.trans h.symm))
  · rw [Equiv.swap_apply_of_ne_of_ne hwa hwb]
    exact hσ w hw hwa

private theorem swap_greatest {α β : Type*} [DecidableEq α] [LinearOrder β]
    {S : Finset α} {a b : α} (hb : b ∈ S) {σ : α ≃ β}
    (hσ : ∀ w ∈ S, w ≠ a → σ w < σ a) :
    ∀ w ∈ S, w ≠ b → ((Equiv.swap a b).trans σ) w < ((Equiv.swap a b).trans σ) b := by
  intro w hw hwb
  simp only [Equiv.trans_apply, Equiv.swap_apply_right]
  by_cases hwa : w = a
  · rw [hwa, Equiv.swap_apply_left]
    exact hσ b hb (fun h => hwb (hwa.trans h.symm))
  · rw [Equiv.swap_apply_of_ne_of_ne hwa hwb]
    exact hσ w hw hwa

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [LinearOrder β]

/-- In a uniform random bijection `σ : α ≃ β` into a linear order `β`, each element of a nonempty
subset `S ⊆ α` is the least element of `S` for exactly a `1 / |S|` fraction of the bijections. -/
theorem card_filter_least_mul_card {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : α ≃ β => ∀ w ∈ S, w ≠ u → σ u < σ w).card * S.card =
      Fintype.card (α ≃ β) := by
  set E : α → Finset (α ≃ β) := fun x => univ.filter fun σ => ∀ w ∈ S, w ≠ x → σ x < σ w
  have hconj {a b : α} (hb : b ∈ S) {σ : α ≃ β} (hσ : σ ∈ E a) :
      (Equiv.swap a b).trans σ ∈ E b := by
    simp only [E, mem_filter, mem_univ, true_and] at hσ ⊢
    exact swap_least hb hσ
  have heq : ∀ x ∈ S, (E x).card = (E u).card := fun x hx =>
    card_nbij' (fun σ => (Equiv.swap x u).trans σ) (fun σ => (Equiv.swap u x).trans σ)
      (fun σ hσ => hconj hu hσ) (fun σ hσ => hconj hx hσ)
      (fun σ _ => by ext v; simp [Equiv.swap_comm u x])
      (fun σ _ => by ext v; simp [Equiv.swap_comm u x])
  have hcover : (univ : Finset (α ≃ β)) = S.biUnion E := by
    ext σ
    simp only [mem_univ, mem_biUnion, true_iff]
    obtain ⟨x, hx, hmin⟩ := S.exists_min_image σ ⟨u, hu⟩
    refine ⟨x, hx, ?_⟩
    simp only [E, mem_filter, mem_univ, true_and]
    exact fun w hw hwx => lt_of_le_of_ne (hmin w hw) (fun h => hwx (σ.injective h).symm)
  have hdisj : (S : Set α).PairwiseDisjoint E := by
    intro x _ y _ hxy
    refine disjoint_left.2 fun σ hx hy => ?_
    simp only [E, mem_filter, mem_univ, true_and] at hx hy
    exact lt_asymm (hx y ‹_› (Ne.symm hxy)) (hy x ‹_› hxy)
  have hcard : Fintype.card (α ≃ β) = (univ : Finset (α ≃ β)).card := card_univ.symm
  change (E u).card * S.card = _
  rw [hcard, hcover, card_biUnion hdisj, sum_congr rfl heq, sum_const, smul_eq_mul, mul_comm]

/-- In a uniform random bijection `σ : α ≃ β` into a linear order `β`, each element of a nonempty
subset `S ⊆ α` is the greatest element of `S` for exactly a `1 / |S|` fraction of the bijections. -/
theorem card_filter_greatest_mul_card {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : α ≃ β => ∀ w ∈ S, w ≠ u → σ w < σ u).card * S.card =
      Fintype.card (α ≃ β) := by
  set E : α → Finset (α ≃ β) := fun x => univ.filter fun σ => ∀ w ∈ S, w ≠ x → σ w < σ x
  have hconj {a b : α} (hb : b ∈ S) {σ : α ≃ β} (hσ : σ ∈ E a) :
      (Equiv.swap a b).trans σ ∈ E b := by
    simp only [E, mem_filter, mem_univ, true_and] at hσ ⊢
    exact swap_greatest hb hσ
  have heq : ∀ x ∈ S, (E x).card = (E u).card := fun x hx =>
    card_nbij' (fun σ => (Equiv.swap x u).trans σ) (fun σ => (Equiv.swap u x).trans σ)
      (fun σ hσ => hconj hu hσ) (fun σ hσ => hconj hx hσ)
      (fun σ _ => by ext v; simp [Equiv.swap_comm u x])
      (fun σ _ => by ext v; simp [Equiv.swap_comm u x])
  have hcover : (univ : Finset (α ≃ β)) = S.biUnion E := by
    ext σ
    simp only [mem_univ, mem_biUnion, true_iff]
    obtain ⟨x, hx, hmax⟩ := S.exists_max_image σ ⟨u, hu⟩
    refine ⟨x, hx, ?_⟩
    simp only [E, mem_filter, mem_univ, true_and]
    exact fun w hw hwx => lt_of_le_of_ne (hmax w hw) (fun h => hwx (σ.injective h))
  have hdisj : (S : Set α).PairwiseDisjoint E := by
    intro x _ y _ hxy
    refine disjoint_left.2 fun σ hx hy => ?_
    simp only [E, mem_filter, mem_univ, true_and] at hx hy
    exact lt_asymm (hy x ‹_› hxy) (hx y ‹_› (Ne.symm hxy))
  have hcard : Fintype.card (α ≃ β) = (univ : Finset (α ≃ β)).card := card_univ.symm
  change (E u).card * S.card = _
  rw [hcard, hcover, card_biUnion hdisj, sum_congr rfl heq, sum_const, smul_eq_mul, mul_comm]

omit [Fintype β] [DecidableEq β] [LinearOrder β] in
/-- In a uniform random permutation of a finite linear order `α`, each element of a nonempty
subset `S` is least among `S` for a `1 / |S|` fraction of the permutations. -/
theorem card_filter_perm_least_mul_card [LinearOrder α] {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : Equiv.Perm α => ∀ w ∈ S, w ≠ u → σ u < σ w).card * S.card =
      (Fintype.card α).factorial := by
  have := card_filter_least_mul_card (β := α) hu
  rwa [Fintype.card_perm] at this

omit [Fintype β] [DecidableEq β] [LinearOrder β] in
/-- In a uniform random permutation of a finite linear order `α`, each element of a nonempty
subset `S` is greatest among `S` for a `1 / |S|` fraction of the permutations. -/
theorem card_filter_perm_greatest_mul_card [LinearOrder α] {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : Equiv.Perm α => ∀ w ∈ S, w ≠ u → σ w < σ u).card * S.card =
      (Fintype.card α).factorial := by
  have := card_filter_greatest_mul_card (β := α) hu
  rwa [Fintype.card_perm] at this

omit [Fintype β] [DecidableEq β] [LinearOrder β] in
/-- In a uniform random permutation of a finite linear order `α`, each element of a nonempty
subset `S` is mapped to the greatest position by its inverse for a `1 / |S|` fraction of the
permutations. -/
theorem card_filter_perm_symm_greatest_mul_card [LinearOrder α] {S : Finset α} {u : α}
    (hu : u ∈ S) :
    (univ.filter fun π : Equiv.Perm α => ∀ w ∈ S, w ≠ u → π.symm w < π.symm u).card * S.card =
      (Fintype.card α).factorial := by
  have hequiv : (univ.filter fun π : Equiv.Perm α => ∀ w ∈ S, w ≠ u → π.symm w < π.symm u).card =
      (univ.filter fun σ : Equiv.Perm α => ∀ w ∈ S, w ≠ u → σ w < σ u).card := by
    refine card_nbij' (fun π => π.symm) (fun σ => σ.symm)
      (fun π hπ => by simpa using hπ) (fun σ hσ => by simpa using hσ)
      (fun π _ => π.symm_symm) (fun σ _ => σ.symm_symm)
  rw [hequiv]
  exact card_filter_perm_greatest_mul_card hu

end Cslib.Probability
