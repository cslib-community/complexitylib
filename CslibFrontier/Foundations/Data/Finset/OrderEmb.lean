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

Every embedding `f : Fin m ↪ α` into a linear order `α` decomposes uniquely into its image
`m`-subset `S = Finset.univ.image f` and a permutation `π : Equiv.Perm (Fin m)` describing the
order in which `f` enumerates `S` relative to the canonical order embedding `S.orderEmbOfFin`.

## Main definitions

* `Finset.orderSubset`: order an `m`-element subset `S` of `α` by a permutation `π`.
* `Finset.embSetPermEquiv`: bijection between embeddings `Fin m ↪ α` and pairs `(S, π)` of a
  size-`m` subset and a permutation of `Fin m`.

## Main results

* `Finset.orderSubset_apply`: evaluation of `orderSubset S hS π`.
* `Finset.image_orderSubset`: the image of `orderSubset S hS π` is `S`.
* `Finset.card_image_orderSubset`: the cardinality of the image of `orderSubset` is `m`.
* `Finset.orderSubset_congr`: congruence for `orderSubset` under equal sets and permutations.
* `Finset.embSetPermEquiv_symm_apply`: the inverse of `embSetPermEquiv` is `orderSubset`.
* `Finset.embSetPermEquiv_fst`: the first component under `embSetPermEquiv` is the image finset.
* `Finset.orderSubset_eq_of_embSetPermEquiv_fst`: recover an embedding from its first component.
* `Finset.image_perm_trans`: the image finset is invariant under permuting the domain.
* `Finset.embSetPermEquiv_perm_trans`: composition with a permutation transforms the second
  component.
-/

public section

namespace Finset

variable {α : Type*} [LinearOrder α]

/-- Order an `m`-element subset `S` of `α` by permutation `π : Equiv.Perm (Fin m)`. -/
def orderSubset {m : ℕ} (S : Finset α) (hS : S.card = m) (π : Equiv.Perm (Fin m)) :
    Fin m ↪ α :=
  π.toEmbedding.trans (S.orderEmbOfFin hS).toEmbedding

@[simp] theorem orderSubset_apply {m : ℕ} (S : Finset α) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) (r : Fin m) :
    orderSubset S hS π r = S.orderEmbOfFin hS (π r) := by rfl

@[simp] theorem image_orderSubset {m : ℕ} (S : Finset α) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) : Finset.univ.image (orderSubset S hS π) = S := by
  ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, orderSubset_apply]
  refine ⟨fun ⟨r, hr⟩ => hr ▸ Finset.orderEmbOfFin_mem S hS (π r), fun hx => ?_⟩
  obtain ⟨j, hj⟩ := (S.orderIsoOfFin hS).surjective ⟨x, hx⟩
  exact ⟨π.symm j, by simpa using congrArg Subtype.val hj⟩

theorem card_image_orderSubset {m : ℕ} (S : Finset α) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) : (Finset.univ.image (orderSubset S hS π)).card = m := by
  rw [image_orderSubset, hS]

theorem orderSubset_congr {m : ℕ} {S₁ S₂ : Finset α} {h₁ : S₁.card = m}
    {h₂ : S₂.card = m} {π₁ π₂ : Equiv.Perm (Fin m)} (hS : S₁ = S₂) (hπ : π₁ = π₂) :
    orderSubset S₁ h₁ π₁ = orderSubset S₂ h₂ π₂ := by subst hS; subst hπ; rfl

/-- Bijection decomposing `f : Fin m ↪ α` into its `m`-subset and relative order `π`. -/
noncomputable def embSetPermEquiv (α : Type*) [Fintype α] [LinearOrder α] (m : ℕ) :
    (Fin m ↪ α) ≃ { S : Finset α // S.card = m } × Equiv.Perm (Fin m) :=
  (Equiv.ofBijective (fun sp => orderSubset sp.1.val sp.1.property sp.2) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun ⟨⟨S₁, hS₁⟩, π₁⟩ ⟨⟨S₂, hS₂⟩, π₂⟩ heq => ?_, ?_⟩
    · dsimp only at heq
      have hS_eq : S₁ = S₂ := by
        rw [← image_orderSubset S₁ hS₁ π₁, ← image_orderSubset S₂ hS₂ π₂, heq]
      subst hS_eq; refine Prod.ext rfl (Equiv.ext fun r => ?_)
      exact (S₁.orderEmbOfFin hS₁).injective (congrArg (fun g : Fin m ↪ α => g r) heq)
    · rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_embedding_eq, Fintype.card_fin,
        Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
      congr 1; simp)).symm

@[simp] theorem embSetPermEquiv_symm_apply {α : Type*} [Fintype α] [LinearOrder α] (m : ℕ)
    (S : { S : Finset α // S.card = m }) (π : Equiv.Perm (Fin m)) :
    (embSetPermEquiv α m).symm (S, π) = orderSubset S.val S.property π := by rfl

@[simp] theorem embSetPermEquiv_fst {α : Type*} [Fintype α] [LinearOrder α] (m : ℕ)
    (f : Fin m ↪ α) :
    ((embSetPermEquiv α m f).1 : Finset α) = Finset.univ.image f := by
  conv_rhs => rw [← (embSetPermEquiv α m).symm_apply_apply f]
  rw [embSetPermEquiv_symm_apply, image_orderSubset]

theorem orderSubset_eq_of_embSetPermEquiv_fst {α : Type*} [Fintype α] [LinearOrder α] {m : ℕ}
    {f : Fin m ↪ α} {S : Finset α} {hS : S.card = m}
    (hf : (embSetPermEquiv α m f).1 = ⟨S, hS⟩) :
    orderSubset S hS (embSetPermEquiv α m f).2 = f := by
  have : (embSetPermEquiv α m).symm (⟨S, hS⟩, (embSetPermEquiv α m f).2) = f := by
    have hpair : (⟨S, hS⟩, (embSetPermEquiv α m f).2) = embSetPermEquiv α m f :=
      Prod.ext hf.symm rfl
    rw [hpair, (embSetPermEquiv α m).symm_apply_apply]
  exact this

theorem image_perm_trans {α : Type*} [DecidableEq α] {m : ℕ} (γp : Equiv.Perm (Fin m))
    (f : Fin m ↪ α) :
    Finset.univ.image (γp.toEmbedding.trans f) = Finset.univ.image f := by
  ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨r, h⟩ => ⟨γp r, h⟩, fun ⟨r, h⟩ => ⟨γp.symm r, by simpa using h⟩⟩

theorem embSetPermEquiv_perm_trans {α : Type*} [Fintype α] [LinearOrder α] {m : ℕ}
    (γp : Equiv.Perm (Fin m)) (f : Fin m ↪ α) :
    (embSetPermEquiv α m (γp.toEmbedding.trans f)).2 = γp.trans (embSetPermEquiv α m f).2 := by
  set S := (embSetPermEquiv α m f).1
  have h0 : (embSetPermEquiv α m).symm (S, (embSetPermEquiv α m f).2) = f := by
    simpa only [S, Prod.mk.eta] using (embSetPermEquiv α m).symm_apply_apply f
  have hgf : (embSetPermEquiv α m).symm (S, γp.trans (embSetPermEquiv α m f).2) =
      γp.toEmbedding.trans f := by
    apply Function.Embedding.ext; intro r
    simpa [embSetPermEquiv_symm_apply] using congrArg (fun k : Fin m ↪ α => k (γp r)) h0
  exact (congrArg Prod.snd ((Equiv.symm_apply_eq (embSetPermEquiv α m)).mp hgf)).symm

end Finset
