/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Reduction.OneOne
public import Complexity.Computability.Complexity.Reduction.Turing

/-!
# Polynomial-time isomorphism and invertible/length-increasing reductions

In structural complexity, the Berman–Hartmanis conjecture states that all NP-complete sets are
polynomial-time isomorphic (`≅ᵖ`) [Berman and Hartmanis][BermanHartmanis1977].
This module formalizes:

1. **Polynomial-time isomorphism** (`Cslib.Complexity.PolyTimeIsomorphic`): an equivalence
   `e : α ≃ β` where both `e` and `e.symm` are polynomial-time computable, preserving language
   membership (`∀ a, a ∈ A ↔ e a ∈ B`).
2. **Polynomial-time-invertible one-one reductions**
   (`Cslib.Complexity.PolyTimeInvertibleOneOneReducible`): an injective polynomial-time reduction
   `f : α → β` with a polynomial-time left inverse `g : β → α` satisfying `g (f a) = a`.
3. **Length-increasing one-one reductions**
   (`Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible`): an injective polynomial-time
   reduction `f : α → β` strictly increasing input length: `(encA a).length < (encB (f a)).length`.
4. **Length-increasing, invertible one-one reductions**
   (`Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible`, `≤₁,ᵢₗ`):
   an injective polynomial-time reduction that is simultaneously length-increasing and has a
   polynomial-time left inverse [Berman and Hartmanis][BermanHartmanis1977], [Ladner, Lynch and
   Selman][LadnerLynchSelman1975].

## Main definitions

* `Cslib.Complexity.PolyTimeIsomorphic`: polynomial-time isomorphism (`≅ᵖ`).
* `Cslib.Complexity.PolyTimeInvertibleOneOneReducible`: polynomial-time-invertible one-one reduction
  (`≤₁,ᵢ`).
* `Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible`: length-increasing one-one reduction
  (`≤₁,ₗᵢ`).
* `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible`: length-increasing and
  polynomial-time-invertible one-one reduction (`≤₁,ᵢₗ`).

## Main results

* Equivalence relation properties of `≅ᵖ`:
  `Cslib.Complexity.PolyTimeIsomorphic.refl`,
  `Cslib.Complexity.PolyTimeIsomorphic.symm`,
  `Cslib.Complexity.PolyTimeIsomorphic.trans`.
* Preorder properties of `≤₁,ᵢ`, `≤₁,ₗᵢ`, and `≤₁,ᵢₗ`:
  `Cslib.Complexity.PolyTimeInvertibleOneOneReducible.refl`,
  `Cslib.Complexity.PolyTimeInvertibleOneOneReducible.trans`,
  `Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible.trans`,
  `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.trans`.
* Reduction hierarchy inclusions:
  - `≅ᵖ ⇒ ≤₁,ᵢ`:
    `Cslib.Complexity.PolyTimeIsomorphic.polyTimeInvertibleOneOneReducible`.
  - `≅ᵖ ⇒ ≤₁`:
    `Cslib.Complexity.PolyTimeIsomorphic.polyTimeOneOneReducible`.
  - `≤₁,ᵢₗ ⇒ ≤₁,ᵢ`:
    `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.`
    `polyTimeInvertibleOneOneReducible`.
  - `≤₁,ᵢₗ ⇒ ≤₁,ₗᵢ`:
    `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.`
    `polyTimeLengthIncreasingOneOneReducible`.
  - `≤₁,ᵢ ⇒ ≤₁`:
    `Cslib.Complexity.PolyTimeInvertibleOneOneReducible.polyTimeOneOneReducible`.
  - `≤₁,ₗᵢ ⇒ ≤₁`:
    `Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible.polyTimeOneOneReducible`.
  - `≤₁,ᵢ ⇒ ≤ₘ`:
    `Cslib.Complexity.PolyTimeInvertibleOneOneReducible.polyTimeReducible`.
  - `≤₁,ₗᵢ ⇒ ≤ₘ`:
    `Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible.polyTimeReducible`.
  - `≤₁,ᵢₗ ⇒ ≤ₘ`:
    `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeReducible`.
* Complementation:
  `Cslib.Complexity.PolyTimeIsomorphic.compl`,
  `Cslib.Complexity.PolyTimeInvertibleOneOneReducible.compl`,
  `Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible.compl`,
  `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.compl`.
* Complexity class preservation:
  `Cslib.Complexity.PolyTimeIsomorphic.mem_P_iff`,
  `Cslib.Complexity.PolyTimeIsomorphic.mem_NP_iff`,
  `Cslib.Complexity.PolyTimeInvertibleOneOneReducible.mem_P`,
  `Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible.mem_P`,
  `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.mem_P`.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977]
* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-! ### 1. Polynomial-Time Isomorphism (`≅ᵖ`) -/

/-- Two languages `A` and `B` are polynomial-time isomorphic (`A ≅ᵖ B`) if there exists an
equivalence `e : α ≃ β` whose forward map `e` and inverse map `e.symm` are both computable in
polynomial time, preserving membership: `∀ a, a ∈ A ↔ e a ∈ B` [Berman and
Hartmanis][BermanHartmanis1977]. -/
def PolyTimeIsomorphic (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ e : α ≃ β,
    (ComputableInPolyTime e encA encB ∧ ComputableInPolyTime e.symm encB encA) ∧
      ∀ a, a ∈ A ↔ e a ∈ B

/-- The identity equivalence is a polynomial-time isomorphism. -/
@[refl]
theorem PolyTimeIsomorphic.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeIsomorphic encA encA A A :=
  ⟨Equiv.refl α, ⟨ComputableInPolyTime.id', ComputableInPolyTime.id'⟩, fun _ => Iff.rfl⟩

/-- Polynomial-time isomorphism is symmetric. -/
@[symm]
theorem PolyTimeIsomorphic.symm (h : PolyTimeIsomorphic encA encB A B) :
    PolyTimeIsomorphic encB encA B A := by
  obtain ⟨e, ⟨he, hsymm⟩, hAB⟩ := h
  refine ⟨e.symm, ⟨hsymm, ?_⟩, fun b => ?_⟩
  · simpa using he
  · rw [hAB (e.symm b), Equiv.apply_symm_apply]

/-- Polynomial-time isomorphisms compose. -/
@[trans]
theorem PolyTimeIsomorphic.trans (hAB : PolyTimeIsomorphic encA encB A B)
    (hBC : PolyTimeIsomorphic encB encC B C) : PolyTimeIsomorphic encA encC A C := by
  obtain ⟨e₁, ⟨he₁, hsymm₁⟩, h₁⟩ := hAB
  obtain ⟨e₂, ⟨he₂, hsymm₂⟩, h₂⟩ := hBC
  refine ⟨e₁.trans e₂, ⟨he₂.comp he₁, hsymm₁.comp hsymm₂⟩, fun a => ?_⟩
  rw [Equiv.trans_apply, ← h₂ (e₁ a), ← h₁ a]

/-- A polynomial-time isomorphism between `A` and `B` is one between `Aᶜ` and `Bᶜ`. -/
theorem PolyTimeIsomorphic.compl (h : PolyTimeIsomorphic encA encB A B) :
    PolyTimeIsomorphic encA encB Aᶜ Bᶜ := by
  obtain ⟨e, he, hAB⟩ := h
  exact ⟨e, he, fun a => not_congr (hAB a)⟩

/-- A polynomial-time isomorphism is a one-one reduction. -/
theorem PolyTimeIsomorphic.polyTimeOneOneReducible (h : PolyTimeIsomorphic encA encB A B) :
    PolyTimeOneOneReducible encA encB A B := by
  obtain ⟨e, ⟨he, _⟩, hAB⟩ := h
  exact ⟨e, ⟨he, e.injective⟩, hAB⟩

/-- A polynomial-time isomorphism is a many-one reduction. -/
theorem PolyTimeIsomorphic.polyTimeReducible (h : PolyTimeIsomorphic encA encB A B) :
    PolyTimeReducible encA encB A B :=
  h.polyTimeOneOneReducible.polyTimeReducible

/-- A polynomial-time isomorphism is a Turing reduction. -/
theorem PolyTimeIsomorphic.polyTimeTuringReducible (h : PolyTimeIsomorphic encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeReducible.polyTimeTuringReducible

/-- `P` is invariant under polynomial-time isomorphisms. -/
theorem PolyTimeIsomorphic.mem_P_iff (h : PolyTimeIsomorphic encA encB A B) :
    A ∈ P encA ↔ B ∈ P encB :=
  ⟨fun hA => h.symm.polyTimeReducible.mem_P hA, fun hB => h.polyTimeReducible.mem_P hB⟩

/-- `NP` is invariant under polynomial-time isomorphisms. -/
theorem PolyTimeIsomorphic.mem_NP_iff (h : PolyTimeIsomorphic encA encB A B) :
    A ∈ NP encA ↔ B ∈ NP encB :=
  ⟨fun hA => h.symm.polyTimeReducible.mem_NP hA, fun hB => h.polyTimeReducible.mem_NP hB⟩

/-! ### 2. Invertible One-One Reductions (`≤₁,ᵢ`) -/

/-- A polynomial-time one-one reduction `f : α → β` is polynomial-time invertible (`≤₁,ᵢ`) if
there exists a polynomial-time left inverse `g : β → α` with `g (f a) = a` for all `a`
[Berman and Hartmanis][BermanHartmanis1977]. -/
def PolyTimeInvertibleOneOneReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ f : α → β,
    (∃ g : β → α,
      ComputableInPolyTime f encA encB ∧
      ComputableInPolyTime g encB encA ∧
      Function.LeftInverse g f) ∧
    ∀ a, a ∈ A ↔ f a ∈ B

/-- The identity is a polynomial-time-invertible one-one reduction. -/
@[refl]
theorem PolyTimeInvertibleOneOneReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeInvertibleOneOneReducible encA encA A A :=
  ⟨id, ⟨id, ComputableInPolyTime.id', ComputableInPolyTime.id', fun _ => rfl⟩, fun _ => Iff.rfl⟩

/-- Polynomial-time-invertible one-one reductions compose. -/
@[trans]
theorem PolyTimeInvertibleOneOneReducible.trans
    (hAB : PolyTimeInvertibleOneOneReducible encA encB A B)
    (hBC : PolyTimeInvertibleOneOneReducible encB encC B C) :
    PolyTimeInvertibleOneOneReducible encA encC A C := by
  obtain ⟨f₁, ⟨g₁, hf₁, hg₁, hleft₁⟩, h₁⟩ := hAB
  obtain ⟨f₂, ⟨g₂, hf₂, hg₂, hleft₂⟩, h₂⟩ := hBC
  refine ⟨f₂ ∘ f₁, ⟨g₁ ∘ g₂, hf₂.comp hf₁, hg₁.comp hg₂, fun a => ?_⟩, fun a => ?_⟩
  · dsimp
    rw [hleft₂, hleft₁]
  · rw [Function.comp_apply, ← h₂ (f₁ a), ← h₁ a]

/-- An invertible one-one reduction from `A` to `B` is one from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeInvertibleOneOneReducible.compl
    (h : PolyTimeInvertibleOneOneReducible encA encB A B) :
    PolyTimeInvertibleOneOneReducible encA encB Aᶜ Bᶜ := by
  obtain ⟨f, hf, hAB⟩ := h
  exact ⟨f, hf, fun a => not_congr (hAB a)⟩

/-- A polynomial-time isomorphism is an invertible one-one reduction. -/
theorem PolyTimeIsomorphic.polyTimeInvertibleOneOneReducible
    (h : PolyTimeIsomorphic encA encB A B) :
    PolyTimeInvertibleOneOneReducible encA encB A B := by
  obtain ⟨e, ⟨he, hsymm⟩, hAB⟩ := h
  exact ⟨e, ⟨e.symm, he, hsymm, e.symm_apply_apply⟩, hAB⟩

/-- An invertible one-one reduction is an injective one-one reduction. -/
theorem PolyTimeInvertibleOneOneReducible.polyTimeOneOneReducible
    (h : PolyTimeInvertibleOneOneReducible encA encB A B) :
    PolyTimeOneOneReducible encA encB A B := by
  obtain ⟨f, ⟨_, hf, _, hleft⟩, hAB⟩ := h
  exact ⟨f, ⟨hf, hleft.injective⟩, hAB⟩

/-- An invertible one-one reduction is a many-one reduction. -/
theorem PolyTimeInvertibleOneOneReducible.polyTimeReducible
    (h : PolyTimeInvertibleOneOneReducible encA encB A B) :
    PolyTimeReducible encA encB A B :=
  h.polyTimeOneOneReducible.polyTimeReducible

/-- An invertible one-one reduction is a Turing reduction. -/
theorem PolyTimeInvertibleOneOneReducible.polyTimeTuringReducible
    (h : PolyTimeInvertibleOneOneReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeReducible.polyTimeTuringReducible

/-- `P` is closed under invertible one-one reductions. -/
theorem PolyTimeInvertibleOneOneReducible.mem_P
    (h : PolyTimeInvertibleOneOneReducible encA encB A B) (hB : B ∈ P encB) : A ∈ P encA :=
  h.polyTimeReducible.mem_P hB

/-! ### 3. Length-Increasing One-One Reductions (`≤₁,ₗᵢ`) -/

/-- A polynomial-time one-one reduction `f : α → β` is length-increasing (`≤₁,ₗᵢ`) if
`(encA a).length < (encB (f a)).length` for every input `a` [Berman and
Hartmanis][BermanHartmanis1977]. -/
def PolyTimeLengthIncreasingOneOneReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β,
    (ComputableInPolyTime f encA encB ∧
      Function.Injective f ∧
      ∀ a, (encA a).length < (encB (f a)).length) ∧
    ∀ a, a ∈ A ↔ f a ∈ B

/-- Length-increasing one-one reductions compose. -/
@[trans]
theorem PolyTimeLengthIncreasingOneOneReducible.trans
    (hAB : PolyTimeLengthIncreasingOneOneReducible encA encB A B)
    (hBC : PolyTimeLengthIncreasingOneOneReducible encB encC B C) :
    PolyTimeLengthIncreasingOneOneReducible encA encC A C := by
  obtain ⟨f₁, ⟨hf₁, hfi₁, hlen₁⟩, h₁⟩ := hAB
  obtain ⟨f₂, ⟨hf₂, hfi₂, hlen₂⟩, h₂⟩ := hBC
  refine ⟨f₂ ∘ f₁, ⟨hf₂.comp hf₁, hfi₂.comp hfi₁, fun a => ?_⟩, fun a => ?_⟩
  · exact (hlen₁ a).trans (hlen₂ (f₁ a))
  · rw [Function.comp_apply, ← h₂ (f₁ a), ← h₁ a]

/-- A length-increasing one-one reduction from `A` to `B` is one from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeLengthIncreasingOneOneReducible.compl
    (h : PolyTimeLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeLengthIncreasingOneOneReducible encA encB Aᶜ Bᶜ := by
  obtain ⟨f, hf, hAB⟩ := h
  exact ⟨f, hf, fun a => not_congr (hAB a)⟩

/-- A length-increasing one-one reduction is an injective one-one reduction. -/
theorem PolyTimeLengthIncreasingOneOneReducible.polyTimeOneOneReducible
    (h : PolyTimeLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeOneOneReducible encA encB A B := by
  obtain ⟨f, ⟨hf, hfi, _⟩, hAB⟩ := h
  exact ⟨f, ⟨hf, hfi⟩, hAB⟩

/-- A length-increasing one-one reduction is a many-one reduction. -/
theorem PolyTimeLengthIncreasingOneOneReducible.polyTimeReducible
    (h : PolyTimeLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeReducible encA encB A B :=
  h.polyTimeOneOneReducible.polyTimeReducible

/-- A length-increasing one-one reduction is a Turing reduction. -/
theorem PolyTimeLengthIncreasingOneOneReducible.polyTimeTuringReducible
    (h : PolyTimeLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeReducible.polyTimeTuringReducible

/-- `P` is closed under length-increasing one-one reductions. -/
theorem PolyTimeLengthIncreasingOneOneReducible.mem_P
    (h : PolyTimeLengthIncreasingOneOneReducible encA encB A B) (hB : B ∈ P encB) : A ∈ P encA :=
  h.polyTimeReducible.mem_P hB

/-! ### 4. Invertible and Length-Increasing One-One Reductions (`≤₁,ᵢₗ`) -/

/-- A polynomial-time one-one reduction `f : α → β` is length-increasing and polynomial-time
invertible (`≤₁,ᵢₗ`) if it has a polynomial-time left inverse `g : β → α` and strictly increases
length: `(encA a).length < (encB (f a)).length` for all `a` [Berman and
Hartmanis][BermanHartmanis1977]. -/
def PolyTimeInvertibleLengthIncreasingOneOneReducible (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β,
    (∃ g : β → α,
      ComputableInPolyTime f encA encB ∧
      ComputableInPolyTime g encB encA ∧
      Function.LeftInverse g f ∧
      ∀ a, (encA a).length < (encB (f a)).length) ∧
    ∀ a, a ∈ A ↔ f a ∈ B

/-- Length-increasing, invertible one-one reductions compose. -/
@[trans]
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.trans
    (hAB : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B)
    (hBC : PolyTimeInvertibleLengthIncreasingOneOneReducible encB encC B C) :
    PolyTimeInvertibleLengthIncreasingOneOneReducible encA encC A C := by
  obtain ⟨f₁, ⟨g₁, hf₁, hg₁, hleft₁, hlen₁⟩, h₁⟩ := hAB
  obtain ⟨f₂, ⟨g₂, hf₂, hg₂, hleft₂, hlen₂⟩, h₂⟩ := hBC
  refine ⟨f₂ ∘ f₁, ⟨g₁ ∘ g₂, hf₂.comp hf₁, hg₁.comp hg₂, fun a => ?_, fun a => ?_⟩, fun a => ?_⟩
  · dsimp
    rw [hleft₂, hleft₁]
  · exact (hlen₁ a).trans (hlen₂ (f₁ a))
  · rw [Function.comp_apply, ← h₂ (f₁ a), ← h₁ a]

/-- An invertible, length-increasing one-one reduction from `A` to `B` is one from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.compl
    (h : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB Aᶜ Bᶜ := by
  obtain ⟨f, hf, hAB⟩ := h
  exact ⟨f, hf, fun a => not_congr (hAB a)⟩

/-- An invertible, length-increasing one-one reduction is an invertible one-one reduction. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeInvertibleOneOneReducible
    (h : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeInvertibleOneOneReducible encA encB A B := by
  obtain ⟨f, ⟨g, hf, hg, hleft, _⟩, hAB⟩ := h
  exact ⟨f, ⟨g, hf, hg, hleft⟩, hAB⟩

/-- An invertible, length-increasing one-one reduction is a length-increasing one-one reduction. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeLengthIncreasingOneOneReducible
    (h : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeLengthIncreasingOneOneReducible encA encB A B := by
  obtain ⟨f, ⟨_, hf, _, hleft, hlen⟩, hAB⟩ := h
  exact ⟨f, ⟨hf, hleft.injective, hlen⟩, hAB⟩

/-- An invertible, length-increasing one-one reduction is an injective one-one reduction. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeOneOneReducible
    (h : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeOneOneReducible encA encB A B :=
  h.polyTimeInvertibleOneOneReducible.polyTimeOneOneReducible

/-- An invertible, length-increasing one-one reduction is a many-one reduction. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeReducible
    (h : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeReducible encA encB A B :=
  h.polyTimeOneOneReducible.polyTimeReducible

/-- An invertible, length-increasing one-one reduction is a Turing reduction. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeTuringReducible
    (h : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeReducible.polyTimeTuringReducible

/-- `P` is closed under invertible, length-increasing one-one reductions. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.mem_P
    (h : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B)
    (hB : B ∈ P encB) : A ∈ P encA :=
  h.polyTimeReducible.mem_P hB

end Cslib.Complexity
