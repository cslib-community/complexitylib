/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Set.Operations

/-!
# Many-one reductions by admissible maps

`Cslib.Complexity.ManyOneReducibleBy Good A B` asks for a membership-preserving map from `A` to
`B` satisfying an arbitrary predicate `Good`. No machine model, encoding, complexity class, or
closure assumption is built into the definition. The namespace is retained for existing clients.
Polynomial-time, logarithmic-space and computable mapping reductions instantiate this kernel.

Mathlib's `ManyOneReducible` is specialized to computable maps on `Primcodable` types; it does
not replace this map-parametric notion.

## Main definitions

* `Cslib.Complexity.ManyOneReducibleBy`: many-one reducibility by admissible maps.

## Main results

* `Cslib.Complexity.ManyOneReducibleBy.refl`, `Cslib.Complexity.ManyOneReducibleBy.trans`:
  reflexivity and transitivity from identity and composition closure.
* `Cslib.Complexity.ManyOneReducibleBy.mono`: enlarging the admissible maps preserves reductions.
* `Cslib.Complexity.ManyOneReducibleBy.compl`, `Cslib.Complexity.ManyOneReducibleBy.mem_compl`:
  complement reductions and transfer to complement classes.
* `Cslib.Complexity.ManyOneReducibleBy.lift`: transfer along partial decodings.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Definition 2.7.
-/

@[expose] public section

namespace Cslib.Complexity

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w}

/-- `A` many-one reduces to `B` by an admissible map: some `f` satisfying `Good` has
`a ∈ A ↔ f a ∈ B` for every `a`. -/
def ManyOneReducibleBy (Good : (α → β) → Prop) (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, Good f ∧ ∀ a, a ∈ A ↔ f a ∈ B

variable {Good : (α → β) → Prop} {A : Set α} {B : Set β}

namespace ManyOneReducibleBy

/-- Every problem reduces to itself when the identity is admissible. -/
theorem refl {Good : (α → α) → Prop} (hid : Good id) (A : Set α) : ManyOneReducibleBy Good A A :=
  ⟨id, hid, fun _ => Iff.rfl⟩

/-- Reductions compose when composites of admissible maps are admissible. The three classes of
maps may differ, as they do when admissibility depends on encodings. -/
theorem trans {Good₁ : (α → β) → Prop} {Good₂ : (β → γ) → Prop} {Good₃ : (α → γ) → Prop}
    {C : Set γ} (hcomp : ∀ f g, Good₁ f → Good₂ g → Good₃ (g ∘ f))
    (hAB : ManyOneReducibleBy Good₁ A B) (hBC : ManyOneReducibleBy Good₂ B C) :
    ManyOneReducibleBy Good₃ A C :=
  let ⟨f, hf, hfAB⟩ := hAB
  let ⟨g, hg, hgBC⟩ := hBC
  ⟨g ∘ f, hcomp f g hf hg, fun a => (hfAB a).trans (hgBC (f a))⟩

/-- More admissible maps give more reductions. -/
theorem mono {Good' : (α → β) → Prop} (hle : ∀ f, Good f → Good' f)
    (h : ManyOneReducibleBy Good A B) : ManyOneReducibleBy Good' A B :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hle f hf, hAB⟩

/-- A reduction from `A` to `B` is also a reduction from `Aᶜ` to `Bᶜ`. -/
theorem compl (h : ManyOneReducibleBy Good A B) : ManyOneReducibleBy Good Aᶜ Bᶜ :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hf, fun a => not_congr (hAB a)⟩

/-- If reductions preserve membership from `D` to `C`, they also preserve membership in the
complement classes `{B | Bᶜ ∈ D}` and `{A | Aᶜ ∈ C}`. -/
theorem mem_compl {C : Set (Set α)} {D : Set (Set β)}
    (hCD : ∀ {A : Set α} {B : Set β}, ManyOneReducibleBy Good A B → B ∈ D → A ∈ C)
    (h : ManyOneReducibleBy Good A B) (hB : Bᶜ ∈ D) : Aᶜ ∈ C :=
  hCD h.compl hB

/-- **Transfer along partial decodings.** Suppose representations `α'` and `β'` partially decode
to `α` and `β`, and every admissible map `f` is simulated by an admissible map `F` of
representations, in that `F` decodes to `f` on decodable inputs and to nothing elsewhere. Then a
reduction of `A` to `B` gives one of the representations of members of `A` to those of members of
`B`. -/
theorem lift {α' : Type w} {β' : Type x} {Good' : (α' → β') → Prop}
    (dec : α' → Option α) (dec' : β' → Option β)
    (hsim : ∀ f, Good f → ∃ F, Good' F ∧ ∀ y, dec' (F y) = (dec y).map f)
    (h : ManyOneReducibleBy Good A B) :
    ManyOneReducibleBy Good' {y | ∃ a ∈ A, dec y = some a} {z | ∃ b ∈ B, dec' z = some b} := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨F, hF, hFf⟩ := hsim f hf
  refine ⟨F, hF, fun y => ?_⟩
  simp only [Set.mem_ofPred_eq, hFf]
  cases dec y with
  | none => simp
  | some a => simpa using hAB a

end ManyOneReducibleBy

end Cslib.Complexity
