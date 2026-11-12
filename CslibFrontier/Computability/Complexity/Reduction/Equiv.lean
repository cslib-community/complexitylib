/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.NP.Witness

/-!
# Polynomial-time many-one equivalence

`Cslib.Complexity.PolyTimeEquiv encA encB A B` (`A ≡ₘᵖ B`) says that `A` and `B` reduce to each
other in polynomial time. Unlike `Cslib.Complexity.ReducibleEquiv` in
`CslibFrontier.Computability.Complexity.Reduction.Autoreducibility`, which takes a homogeneous
relation on a single carrier `Set α`, `PolyTimeEquiv` relates problems across distinct instance
types `α` and `β` and encodings `encA` and `encB`.

## Main definitions

* `Cslib.Complexity.PolyTimeEquiv`: mutual polynomial-time many-one reducibility across encoded
  domains.

## Main results

* `Cslib.Complexity.PolyTimeEquiv.refl`, `.symm`, `.trans`, `.compl`: equivalence and complement
  invariance.
* `Cslib.Complexity.PolyTimeEquiv.mem_P_iff`, `.mem_NP_iff`: invariance of `P` and `NP` membership.

## References

* [R. E. Ladner, *On the Structure of Polynomial Time Reducibility*][Ladner1975a]
-/

@[expose] public section

namespace Cslib.Complexity

/-- Two problems are **polynomial-time many-one equivalent** (`A ≡ₘᵖ B`) when each reduces to the
other in polynomial time. -/
def PolyTimeEquiv {α β : Type*} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  PolyTimeReducible encA encB A B ∧ PolyTimeReducible encB encA B A

namespace PolyTimeEquiv

variable {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- Polynomial-time many-one equivalence is reflexive. -/
@[refl]
theorem refl (encA : α ↪ List Bool) (A : Set α) : PolyTimeEquiv encA encA A A :=
  ⟨.refl encA A, .refl encA A⟩

/-- Polynomial-time many-one equivalence is symmetric. -/
@[symm]
theorem symm (h : PolyTimeEquiv encA encB A B) : PolyTimeEquiv encB encA B A :=
  ⟨h.2, h.1⟩

/-- Polynomial-time many-one equivalence is transitive. -/
@[trans]
theorem trans (hAB : PolyTimeEquiv encA encB A B) (hBC : PolyTimeEquiv encB encC B C) :
    PolyTimeEquiv encA encC A C :=
  ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩

/-- Polynomial-time many-one equivalence passes to complements. -/
theorem compl (h : PolyTimeEquiv encA encB A B) : PolyTimeEquiv encA encB Aᶜ Bᶜ :=
  ⟨h.1.compl, h.2.compl⟩

/-- Polynomial-time many-one equivalent problems both lie in `P` or neither does. -/
theorem mem_P_iff {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (h : PolyTimeEquiv encA encB A B) : A ∈ P encA ↔ B ∈ P encB :=
  ⟨fun hA => PolyTimeReducible.mem_P h.2 hA, fun hB => PolyTimeReducible.mem_P h.1 hB⟩

/-- Polynomial-time many-one equivalent problems both lie in `NP` or neither does. -/
theorem mem_NP_iff {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (h : PolyTimeEquiv encA encB A B) : A ∈ NP encA ↔ B ∈ NP encB :=
  ⟨fun hA => PolyTimeReducible.mem_NP h.2 hA, fun hB => PolyTimeReducible.mem_NP h.1 hB⟩

end PolyTimeEquiv

end Cslib.Complexity
