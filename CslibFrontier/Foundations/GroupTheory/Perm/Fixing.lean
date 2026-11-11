/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Data/Fintype/Perm.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Fintype

/-!
# Counting the permutations that fix a set

The permutations of a finite type `α` that fix every point of a set `U` are the permutations of
the complement of `U`, so there are `(#α - #U)!` of them
(`Equiv.Perm.card_filter_forall_eq_self`). More generally, if `f` is injective on `U`, then
`(#α - #U)!` permutations agree with `f` on `U`: composing with one such permutation `τ`
(`Equiv.extendSubtype`) matches them with the permutations fixing `U`.

## Main results

* `Equiv.Perm.card_filter_forall_eq_self`: `(#α - #U)!` permutations fix every point of `U`.
* `Equiv.Perm.card_filter_forall_eq_of_injOn`: `(#α - #U)!` permutations agree on `U` with a
  function injective on `U`.
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

/-- **The permutations extending an injective map** on a set `U` of a finite type `α` number
`(#α - #U)!`. -/
theorem card_filter_forall_eq_of_injOn (U : Finset α) (f : α → α) (hf : Set.InjOn f U) :
    #{σ : Perm α | ∀ u ∈ U, σ u = f u} = (Fintype.card α - U.card)! := by
  let e : {x // x ∈ U} ≃ {x // x ∈ U.image f} :=
    Equiv.ofBijective (fun x => ⟨f x, mem_image_of_mem f x.2⟩)
      ⟨fun a b h => Subtype.ext (hf a.2 b.2 (congrArg Subtype.val h)), fun ⟨y, hy⟩ => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        exact ⟨⟨x, hx⟩, rfl⟩⟩
  have hτ : ∀ u ∈ U, e.extendSubtype u = f u := fun u hu => extendSubtype_apply_of_mem e u hu
  rw [← card_filter_forall_eq_self U]
  refine card_bij (fun σ _ => e.extendSubtype⁻¹ * σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro u hu
    rw [Perm.mul_apply, hσ u hu, ← hτ u hu]
    exact Equiv.symm_apply_apply _ u
  · intro σ _ σ' _ h
    exact mul_left_cancel h
  · intro σ hσ
    refine ⟨e.extendSubtype * σ, ?_, by rw [inv_mul_cancel_left]⟩
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro u hu
    rw [Perm.mul_apply, hσ u hu, hτ u hu]

end Equiv.Perm
