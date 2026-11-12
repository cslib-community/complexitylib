/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Fintype/Sum.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Sum

/-!
# Extending embeddings of finite types

An embedding `x : α ↪ γ` into a finite type extends along an embedding `e : α ↪ β` whenever `β` is
at most as large as `γ` (`Function.Embedding.exists_extend_of_card_le`). The proof extends `x` to
an equivalence between `β` and a subset of `γ` of the same size, with
`Set.MapsTo.exists_equiv_extend_of_card_eq`, next to which it belongs in Mathlib.

## Main results

* `Function.Embedding.exists_extend_of_card_le`: extending an embedding along an embedding.
-/

public section

/-- An embedding `x : α ↪ γ` into a finite type extends along an embedding `e : α ↪ β` of
finite types, when `β` is at most as large as `γ`. -/
theorem Function.Embedding.exists_extend_of_card_le {α β γ : Type*} [Finite α] [Fintype β]
    [Fintype γ] (e : α ↪ β) (x : α ↪ γ) (h : Fintype.card β ≤ Fintype.card γ) :
    ∃ x' : β ↪ γ, ∀ a, x' (e a) = x a := by
  classical
  have := Fintype.ofFinite α
  rcases isEmpty_or_nonempty γ with hγ | hγ
  · have : IsEmpty β := Fintype.card_eq_zero_iff.mp (by simpa using h)
    have : IsEmpty α := Function.isEmpty e
    exact ⟨Function.Embedding.ofIsEmpty, isEmptyElim⟩
  have c : γ := Classical.choice hγ
  have hs : (Finset.univ.image x).card ≤ Fintype.card β := by
    rw [Finset.card_image_of_injective _ x.injective, Finset.card_univ]
    exact Fintype.card_le_of_embedding e
  obtain ⟨t, hst, -, ht⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ _) hs
    (by simpa using h)
  set f : β → γ := Function.extend e x fun _ => c
  have hf (a : α) : f (e a) = x a := e.injective.extend_apply _ _ a
  obtain ⟨g, hg⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq (s := Set.range e) (f := f)
    (t := t) ht.symm
    (by rintro _ ⟨a, rfl⟩; exact hst (by simp [hf]))
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab; simp only [hf] at hab; rw [x.injective hab])
  exact ⟨g.toEmbedding.trans (Function.Embedding.subtype _), fun a => by
    simp [hg (e a) ⟨a, rfl⟩, hf]⟩
