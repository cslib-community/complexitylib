/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Complexity.Reduction

/-!
# Polynomial-time and logspace one-one reductions

A one-one reduction is a many-one reduction by an injective map. In polynomial time it underlies
p-isomorphism and the Berman–Hartmanis conjecture [Berman and Hartmanis][BermanHartmanis1977]; in
logarithmic space it gives logspace one-one reducibility. Both are instances of
`ManyOneReducibleBy` (`Cslib.Complexity.polyTimeOneOneReducible_iff_manyOneReducibleBy`,
`Cslib.Complexity.logSpaceOneOneReducible_iff_manyOneReducibleBy`), so the generic many-one kernel
applies.

## Main definitions

* `Cslib.Complexity.PolyTimeOneOneReducible`: reduction by an injective polynomial-time map.
* `Cslib.Complexity.LogSpaceOneOneReducible`: reduction by an injective logspace map.

## Main results

* `Cslib.Complexity.polyTimeOneOneReducible_iff_manyOneReducibleBy`,
  `Cslib.Complexity.logSpaceOneOneReducible_iff_manyOneReducibleBy`: bridges to the generic
  many-one kernel.
* `Cslib.Complexity.PolyTimeOneOneReducible.polyTimeReducible`,
  `Cslib.Complexity.LogSpaceOneOneReducible.logSpaceReducible`,
  `Cslib.Complexity.LogSpaceOneOneReducible.polyTimeOneOneReducible`: forgetful implications.
* `Cslib.Complexity.PolyTimeOneOneReducible.refl`,
  `Cslib.Complexity.PolyTimeOneOneReducible.trans`,
  `Cslib.Complexity.LogSpaceOneOneReducible.refl`,
  `Cslib.Complexity.LogSpaceOneOneReducible.trans`: preorders.
* `Cslib.Complexity.PolyTimeOneOneReducible.compl`,
  `Cslib.Complexity.PolyTimeOneOneReducible.mem_P`,
  `Cslib.Complexity.LogSpaceOneOneReducible.compl`,
  `Cslib.Complexity.LogSpaceOneOneReducible.mem_L`,
  `Cslib.Complexity.LogSpaceOneOneReducible.mem_P`.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- `A` reduces to `B` by an injective polynomial-time map `f` with `a ∈ A ↔ f a ∈ B`. -/
def PolyTimeOneOneReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ f : α → β, (ComputableInPolyTime f encA encB ∧ Function.Injective f) ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- One-one reducibility is many-one reducibility by the injective polynomial-time maps. -/
theorem polyTimeOneOneReducible_iff_manyOneReducibleBy :
    PolyTimeOneOneReducible encA encB A B ↔
      ManyOneReducibleBy (fun f => ComputableInPolyTime f encA encB ∧ Function.Injective f) A B :=
  Iff.rfl

/-- A one-one reduction is a many-one reduction. -/
theorem PolyTimeOneOneReducible.polyTimeReducible (h : PolyTimeOneOneReducible encA encB A B) :
    PolyTimeReducible encA encB A B :=
  let ⟨f, ⟨hf, _⟩, hA⟩ := h
  ⟨f, hf, hA⟩

/-- The identity is a one-one reduction. -/
@[refl]
theorem PolyTimeOneOneReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeOneOneReducible encA encA A A :=
  ⟨id, ⟨ComputableInPolyTime.id', Function.injective_id⟩, fun _ => Iff.rfl⟩

/-- One-one reductions compose. -/
@[trans]
theorem PolyTimeOneOneReducible.trans (hAB : PolyTimeOneOneReducible encA encB A B)
    (hBC : PolyTimeOneOneReducible encB encC B C) : PolyTimeOneOneReducible encA encC A C :=
  let ⟨f, ⟨hf, hfi⟩, hA⟩ := hAB
  let ⟨g, ⟨hg, hgi⟩, hB⟩ := hBC
  ⟨g ∘ f, ⟨hg.comp hf, hgi.comp hfi⟩, fun a => (hA a).trans (hB (f a))⟩

/-- A one-one reduction from `A` to `B` is one from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeOneOneReducible.compl (h : PolyTimeOneOneReducible encA encB A B) :
    PolyTimeOneOneReducible encA encB Aᶜ Bᶜ :=
  let ⟨f, hf, hA⟩ := h
  ⟨f, hf, fun a => not_congr (hA a)⟩

/-- `P` is closed under one-one reductions. -/
theorem PolyTimeOneOneReducible.mem_P (h : PolyTimeOneOneReducible encA encB A B)
    (hB : B ∈ P encB) : A ∈ P encA :=
  h.polyTimeReducible.mem_P hB

/-! ### Logspace one-one reductions -/

/-- `A` reduces to `B` by an injective logspace map `f` with `a ∈ A ↔ f a ∈ B`. -/
def LogSpaceOneOneReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ f : α → β, (ComputableInLogSpace f encA encB ∧ Function.Injective f) ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- Logspace one-one reducibility is many-one reducibility by the injective logspace maps. -/
theorem logSpaceOneOneReducible_iff_manyOneReducibleBy :
    LogSpaceOneOneReducible encA encB A B ↔
      ManyOneReducibleBy (fun f => ComputableInLogSpace f encA encB ∧ Function.Injective f) A B :=
  Iff.rfl

/-- A logspace one-one reduction is a logspace many-one reduction. -/
theorem LogSpaceOneOneReducible.logSpaceReducible (h : LogSpaceOneOneReducible encA encB A B) :
    LogSpaceReducible encA encB A B :=
  let ⟨f, ⟨hf, _⟩, hA⟩ := h
  ⟨f, hf, hA⟩

/-- A logspace one-one reduction is a polynomial-time one-one reduction. -/
theorem LogSpaceOneOneReducible.polyTimeOneOneReducible
    (h : LogSpaceOneOneReducible encA encB A B) : PolyTimeOneOneReducible encA encB A B :=
  let ⟨f, ⟨hf, hfi⟩, hA⟩ := h
  ⟨f, ⟨hf.computableInPolyTime, hfi⟩, hA⟩

/-- The identity is a logspace one-one reduction. -/
@[refl]
theorem LogSpaceOneOneReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    LogSpaceOneOneReducible encA encA A A :=
  ⟨id, ⟨ComputableInLogSpace.id, Function.injective_id⟩, fun _ => Iff.rfl⟩

/-- Logspace one-one reductions compose. -/
@[trans]
theorem LogSpaceOneOneReducible.trans (hAB : LogSpaceOneOneReducible encA encB A B)
    (hBC : LogSpaceOneOneReducible encB encC B C) : LogSpaceOneOneReducible encA encC A C :=
  let ⟨f, ⟨hf, hfi⟩, hA⟩ := hAB
  let ⟨g, ⟨hg, hgi⟩, hB⟩ := hBC
  ⟨g ∘ f, ⟨hg.comp hf, hgi.comp hfi⟩, fun a => (hA a).trans (hB (f a))⟩

/-- A logspace one-one reduction from `A` to `B` is one from `Aᶜ` to `Bᶜ`. -/
theorem LogSpaceOneOneReducible.compl (h : LogSpaceOneOneReducible encA encB A B) :
    LogSpaceOneOneReducible encA encB Aᶜ Bᶜ :=
  let ⟨f, hf, hA⟩ := h
  ⟨f, hf, fun a => not_congr (hA a)⟩

/-- `L` is closed under logspace one-one reductions. -/
theorem LogSpaceOneOneReducible.mem_L (h : LogSpaceOneOneReducible encA encB A B)
    (hB : B ∈ L encB) : A ∈ L encA :=
  h.logSpaceReducible.mem_L hB

/-- `P` is closed under logspace one-one reductions. -/
theorem LogSpaceOneOneReducible.mem_P (h : LogSpaceOneOneReducible encA encB A B)
    (hB : B ∈ P encB) : A ∈ P encA :=
  h.polyTimeOneOneReducible.mem_P hB

end Cslib.Complexity
