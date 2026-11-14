/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate (Mathlib, finset order embedding decompositions)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Decomposing finite embeddings into subsets and permutations

Every embedding `f : Fin m ↪ Fin U` decomposes uniquely into its image `m`-subset
`S = Finset.univ.image f` and a permutation `π : Equiv.Perm (Fin m)` describing the order in which
`f` enumerates `S` relative to the canonical order embedding `S.orderEmbOfFin`.

## Main definitions

* `Finset.orderSubset`: order an `m`-element subset `S` of `Fin U` by a permutation `π`.
* `Finset.embSetPermEquiv`: bijection between embeddings `Fin m ↪ Fin U` and pairs `(S, π)` of a
  size-`m` subset and a permutation of `Fin m`.

## Main results

* `Finset.orderSubset_apply`: evaluation of `orderSubset S hS π`.
* `Finset.image_orderSubset`: the image of `orderSubset S hS π` is `S`.
* `Finset.card_image_orderSubset`: the cardinality of the image of `orderSubset` is `m`.
* `Finset.embSetPermEquiv_symm_apply`: the inverse of `embSetPermEquiv` is `orderSubset`.
* `Finset.embSetPermEquiv_fst`: the first component under `embSetPermEquiv` is the image finset.
-/

@[expose] public section

namespace Finset

/-- Order an `m`-element subset `S` of `Fin U` by permutation `π : Equiv.Perm (Fin m)`. -/
def orderSubset {U m : ℕ} (S : Finset (Fin U)) (hS : S.card = m) (π : Equiv.Perm (Fin m)) :
    Fin m ↪ Fin U :=
  π.toEmbedding.trans (S.orderEmbOfFin hS).toEmbedding

@[simp] theorem orderSubset_apply {U m : ℕ} (S : Finset (Fin U)) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) (r : Fin m) :
    orderSubset S hS π r = S.orderEmbOfFin hS (π r) := by rfl

@[simp] theorem image_orderSubset {U m : ℕ} (S : Finset (Fin U)) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) : Finset.univ.image (orderSubset S hS π) = S := by
  ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, orderSubset_apply]
  refine ⟨fun ⟨r, hr⟩ => hr ▸ Finset.orderEmbOfFin_mem S hS (π r), fun hx => ?_⟩
  obtain ⟨j, hj⟩ := (S.orderIsoOfFin hS).surjective ⟨x, hx⟩
  exact ⟨π.symm j, by simpa using congrArg Subtype.val hj⟩

theorem card_image_orderSubset {U m : ℕ} (S : Finset (Fin U)) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) : (Finset.univ.image (orderSubset S hS π)).card = m := by
  rw [image_orderSubset, hS]

/-- Bijection decomposing `f : Fin m ↪ Fin U` into its `m`-subset and relative order `π`. -/
noncomputable def embSetPermEquiv (U m : ℕ) :
    (Fin m ↪ Fin U) ≃ { S : Finset (Fin U) // S.card = m } × Equiv.Perm (Fin m) :=
  (Equiv.ofBijective (fun sp => orderSubset sp.1.val sp.1.property sp.2) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun ⟨⟨S₁, hS₁⟩, π₁⟩ ⟨⟨S₂, hS₂⟩, π₂⟩ heq => ?_, ?_⟩
    · dsimp only at heq
      have hS_eq : S₁ = S₂ := by
        rw [← image_orderSubset S₁ hS₁ π₁, ← image_orderSubset S₂ hS₂ π₂, heq]
      subst hS_eq; refine Prod.ext rfl (Equiv.ext fun r => ?_)
      exact (S₁.orderEmbOfFin hS₁).injective (congrArg (fun g : Fin m ↪ Fin U => g r) heq)
    · rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_embedding_eq, Fintype.card_fin,
        Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
      congr 1; simp [Fintype.card_fin])).symm

@[simp] theorem embSetPermEquiv_symm_apply (U m : ℕ)
    (S : { S : Finset (Fin U) // S.card = m }) (π : Equiv.Perm (Fin m)) :
    (embSetPermEquiv U m).symm (S, π) = orderSubset S.val S.property π := by rfl

@[simp] theorem embSetPermEquiv_fst (U m : ℕ) (f : Fin m ↪ Fin U) :
    ((embSetPermEquiv U m f).1 : Finset (Fin U)) = Finset.univ.image f := by
  conv_rhs => rw [← (embSetPermEquiv U m).symm_apply_apply f]
  rw [embSetPermEquiv_symm_apply, image_orderSubset]

end Finset

export Finset (orderSubset orderSubset_apply image_orderSubset card_image_orderSubset
  embSetPermEquiv embSetPermEquiv_symm_apply embSetPermEquiv_fst)
