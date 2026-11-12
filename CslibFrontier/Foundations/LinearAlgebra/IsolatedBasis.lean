/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Weights that isolate a spanning set of coefficients

Let `D : M → A` be a family of vectors of an `F`-module `A`, indexed by a type `M` of
"monomials", and let `wt : M → ℕ` be a weight. The weight *isolates* a finite set `S` inside a
finite set `T` of indices if it is injective on `S` and every vector `D m` with `m ∈ T \ S` is a
linear combination of the vectors `D m'` with `m' ∈ S` of strictly smaller weight. This is the
basis isolating weight assignment of [AgrawalGurjarKorwarSaxena2015], Definition 5, for the
coefficients `D` of a polynomial over an algebra, with one difference: `Isolates` does not
require the vectors `D m`, `m ∈ S`, to be linearly independent, so `S` need not give a basis of
the span of the coefficients. The consequences drawn from the definition do not use
independence; the sets constructed here have at most `Module.finrank F A` elements.

## Main definitions

* `Cslib.Isolates`: the weight `wt` isolates the set `S` inside `T` for the family `D`.

## Main results

* `Cslib.Isolates.of_span_lt`: it is enough that every `D m` with `m ∈ T \ S` is in the span of
  the `D m'` with `m' ∈ T` of strictly smaller weight
  ([AgrawalGurjarKorwarSaxena2015], Observation 7).
* `Cslib.exists_isolates_of_injOn`: a weight injective on `T` isolates a set of at most
  `Module.finrank F A` elements.
* `Cslib.Isolates.mono_weight`: isolation survives a change of weight that preserves the strict
  order of the weights on `T` and is injective on `S`.
* `Cslib.exists_isolates_add`: for a product `D (m₁ + m₂) = D₁ m₁ * D₂ m₂` in an algebra, an
  additive weight isolating `S₁` in `T₁` and `S₂` in `T₂` and injective on `S₁ + S₂` isolates a
  small subset of `S₁ + S₂` in `T₁ + T₂`. This is the step of the proof of Lemma 8 of
  [AgrawalGurjarKorwarSaxena2015] that combines two factors.

## References

* [AgrawalGurjarKorwarSaxena2015], Definition 5 and Observation 7.
-/

public section

open scoped Pointwise

namespace Cslib

variable {F A M : Type*} [Field F]

section Module

variable [AddCommGroup A] [Module F A] {wt : M → ℕ} {D : M → A} {T S : Finset M}

variable (F) in
/-- The weight `wt` isolates the set `S` inside `T` for the family of vectors `D`: `S ⊆ T`, the
weight is injective on `S`, and every `D m` with `m ∈ T \ S` is in the span of the vectors `D m'`
with `m' ∈ S` of strictly smaller weight. The vectors `D m`, `m ∈ S`, are not required to be
linearly independent. -/
@[expose] def Isolates (wt : M → ℕ) (D : M → A) (T S : Finset M) : Prop :=
  S ⊆ T ∧ Set.InjOn wt S ∧
    ∀ m ∈ T, m ∉ S → D m ∈ Submodule.span F (D '' {m' | m' ∈ S ∧ wt m' < wt m})

/-- To isolate `S` inside `T` it is enough that every `D m` with `m ∈ T \ S` is in the span of
the vectors `D m'` with `m' ∈ T`, not necessarily in `S`, of strictly smaller weight. -/
theorem Isolates.of_span_lt (hS : S ⊆ T) (hinj : Set.InjOn wt S)
    (h : ∀ m ∈ T, m ∉ S → D m ∈ Submodule.span F (D '' {m' | m' ∈ T ∧ wt m' < wt m})) :
    Isolates F wt D T S := by
  refine ⟨hS, hinj, fun m => ?_⟩
  induction hk : wt m using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    subst hk
    intro hm hmS
    refine Submodule.span_le.2 ?_ (h m hm hmS)
    rintro _ ⟨m', ⟨hm', hlt⟩, rfl⟩
    by_cases hm'S : m' ∈ S
    · exact Submodule.subset_span ⟨m', ⟨hm'S, hlt⟩, rfl⟩
    · refine Submodule.span_mono (Set.image_mono ?_) (ih (wt m') hlt m' rfl hm' hm'S)
      exact fun x hx => ⟨hx.1, hx.2.trans hlt⟩

/-- A weight that is injective on `T` isolates a subset of `T` with at most `Module.finrank F A`
elements: go through `T` by increasing weight and keep the indices whose vector is not in the
span of the vectors kept before. -/
theorem exists_isolates_of_injOn [FiniteDimensional F A] (hinj : Set.InjOn wt T) :
    ∃ S, S.card ≤ Module.finrank F A ∧ Isolates F wt D T S := by
  classical
  suffices h : ∃ S ⊆ T, LinearIndepOn F D (S : Set M) ∧
      ∀ m ∈ T, m ∉ S → D m ∈ Submodule.span F (D '' {m' | m' ∈ S ∧ wt m' < wt m}) by
    obtain ⟨S, hST, hli, hS⟩ := h
    refine ⟨S, ?_, hST, hinj.mono (Finset.coe_subset.2 hST), hS⟩
    simpa using hli.linearIndependent.fintype_card_le_finrank
  induction T using Finset.induction_on_max_value wt with
  | empty => exact ⟨∅, subset_rfl, by simp, by simp⟩
  | insert a T haT hmax ih =>
    rw [Finset.coe_insert] at hinj
    obtain ⟨S, hST, hli, hS⟩ := ih (hinj.mono (Set.subset_insert _ _))
    have haS : a ∉ S := fun h => haT (hST h)
    have hlt : ∀ x ∈ T, wt x < wt a := fun x hx =>
      lt_of_le_of_ne (hmax x hx) fun h =>
        haT (hinj (Set.mem_insert_of_mem _ hx) (Set.mem_insert _ _) h ▸ hx)
    by_cases ha : D a ∈ Submodule.span F (D '' (S : Set M))
    · refine ⟨S, hST.trans (Finset.subset_insert _ _), hli, fun m hm hmS => ?_⟩
      rcases Finset.mem_insert.1 hm with rfl | hm
      · refine Submodule.span_mono (Set.image_mono ?_) ha
        exact fun x hx => ⟨hx, hlt x (hST hx)⟩
      · exact hS m hm hmS
    · refine ⟨insert a S, Finset.insert_subset_insert _ hST, ?_, fun m hm hmS => ?_⟩
      · rw [Finset.coe_insert]
        exact hli.insert ha
      · rw [Finset.mem_insert, not_or] at hmS
        refine Submodule.span_mono (Set.image_mono ?_)
          (hS m ((Finset.mem_insert.1 hm).resolve_left hmS.1) hmS.2)
        exact fun x hx => ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩

/-- Isolation survives a change of weight that preserves the strict order of the weights on `T`
and is injective on `S`. -/
theorem Isolates.mono_weight {wt' : M → ℕ} (h : Isolates F wt D T S)
    (hlt : ∀ m ∈ T, ∀ m' ∈ T, wt m' < wt m → wt' m' < wt' m)
    (hinj : Set.InjOn wt' S) : Isolates F wt' D T S := by
  refine ⟨h.1, hinj, fun m hm hmS => Submodule.span_mono (Set.image_mono ?_) (h.2.2 m hm hmS)⟩
  exact fun m' hm' => ⟨hm'.1, hlt m hm m' (h.1 hm'.1) hm'.2⟩

end Module

section Algebra

variable [Ring A] [Algebra F A] [AddZeroClass M] [DecidableEq M] {wt : M →+ ℕ}
  {D D₁ D₂ : M → A} {T₁ T₂ S₁ S₂ : Finset M}

/-- Isolation for a product. Let `D (m₁ + m₂) = D₁ m₁ * D₂ m₂` for `m₁ ∈ T₁` and `m₂ ∈ T₂`. If
an additive weight isolates `S₁` inside `T₁` for `D₁` and `S₂` inside `T₂` for `D₂`, and is
injective on the pointwise sum `S₁ + S₂`, then it isolates, for `D`, a subset of `S₁ + S₂` with
at most `Module.finrank F A` elements inside `T₁ + T₂`. -/
theorem exists_isolates_add [FiniteDimensional F A]
    (h₁ : Isolates F wt D₁ T₁ S₁) (h₂ : Isolates F wt D₂ T₂ S₂)
    (hD : ∀ m₁ ∈ T₁, ∀ m₂ ∈ T₂, D (m₁ + m₂) = D₁ m₁ * D₂ m₂)
    (hinj : Set.InjOn wt (S₁ + S₂ : Finset M)) :
    ∃ S ⊆ S₁ + S₂, S.card ≤ Module.finrank F A ∧ Isolates F wt D (T₁ + T₂) S := by
  obtain ⟨S, hcard, hSS, -, hS⟩ := exists_isolates_of_injOn (F := F) (D := D) hinj
  have hST : S₁ + S₂ ⊆ T₁ + T₂ := Finset.add_subset_add h₁.1 h₂.1
  refine ⟨S, hSS, hcard, .of_span_lt (hSS.trans hST) (hinj.mono (Finset.coe_subset.2 hSS))
    fun m hm hmS => ?_⟩
  by_cases hmSS : m ∈ S₁ + S₂
  · refine Submodule.span_mono (Set.image_mono ?_) (hS m hmSS hmS)
    exact fun x hx => ⟨hST (hSS hx.1), hx.2⟩
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.1 hm
  rw [hD m₁ hm₁ m₂ hm₂]
  by_cases hm₁S : m₁ ∈ S₁
  · have hm₂S : m₂ ∉ S₂ := fun h => hmSS (Finset.add_mem_add hm₁S h)
    refine Submodule.span_le.2 ?_ (Submodule.apply_mem_span_image_of_mem_span
      (LinearMap.mulLeft F (D₁ m₁)) (h₂.2.2 m₂ hm₂ hm₂S))
    rintro _ ⟨_, ⟨m', ⟨hm', hlt⟩, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨m₁ + m', ⟨Finset.add_mem_add hm₁ (h₂.1 hm'), ?_⟩, ?_⟩
    · simpa using hlt
    · rw [hD m₁ hm₁ m' (h₂.1 hm'), LinearMap.mulLeft_apply]
  · refine Submodule.span_le.2 ?_ (Submodule.apply_mem_span_image_of_mem_span
      (LinearMap.mulRight F (D₂ m₂)) (h₁.2.2 m₁ hm₁ hm₁S))
    rintro _ ⟨_, ⟨m', ⟨hm', hlt⟩, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨m' + m₂, ⟨Finset.add_mem_add (h₁.1 hm') hm₂, ?_⟩, ?_⟩
    · simpa using hlt
    · rw [hD m' (h₁.1 hm') m₂ hm₂, LinearMap.mulRight_apply]

end Algebra

end Cslib
