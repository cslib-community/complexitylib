/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Reduction.ManyOne
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable

/-!
# Mapping reductions

`MappingReducible encA encB A B`: a computable function (`Turing.MultiTapeTM.IsComputable`) with
respect to the encodings `encA` and `encB` maps the instances of `A` to instances of `B` and the
other instances to instances outside `B` [Sipser, Definition 5.20][Sipser2013]. Mapping
reducibility is a preorder, and decidability transfers backwards along reductions
(`Turing.MultiTapeTM.IsDecidable.of_mappingReducible`), so undecidability transfers forwards
(`Turing.MultiTapeTM.MappingReducible.not_isDecidable`).

A polynomial-time reduction (`Cslib.Complexity.PolyTimeReducible`) is a mapping reduction, its
function being computable (`Turing.MultiTapeTM.ComputableTidilyInPolyTime.isComputable`).
Mathlib's `ManyOneReducible` is the analogous notion for Mathlib's partial recursive functions on
`Primcodable` types; `Turing.MultiTapeTM.MappingReducible.manyOneReducible` in
`MultiTape.Halting.Partrec` connects the two notions.

## Main definitions

* `Turing.MultiTapeTM.MappingReducible`: mapping reducibility.

## Main results

* `Turing.MultiTapeTM.MappingReducible.refl`, `Turing.MultiTapeTM.MappingReducible.trans`: mapping
  reducibility is a preorder.
* `Turing.MultiTapeTM.MappingReducible.compl`: a reduction is one between the complements.
* `Turing.MultiTapeTM.IsDecidable.of_mappingReducible`,
  `Turing.MultiTapeTM.MappingReducible.not_isDecidable`: transfer of decidability and of
  undecidability.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib.Complexity

variable {α β γ : Type*}

/-- `A` is mapping reducible to `B`: some function `f`, computable with respect to `encA` and
`encB`, satisfies `a ∈ A ↔ f a ∈ B`. This is `ManyOneReducibleBy` for the computable maps
(`mappingReducible_iff_manyOneReducibleBy`). -/
def MappingReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α) (B : Set β) :
    Prop :=
  ∃ f : α → β, IsComputable f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- Mapping reducibility is many-one reducibility by computable maps. -/
theorem mappingReducible_iff_manyOneReducibleBy :
    MappingReducible encA encB A B ↔ ManyOneReducibleBy (IsComputable · encA encB) A B :=
  Iff.rfl

/-- Every set reduces to itself by the identity. -/
@[refl]
theorem MappingReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    MappingReducible encA encA A A :=
  ManyOneReducibleBy.refl (isComputable_id encA) A

/-- **Mapping reductions compose.** -/
@[trans]
theorem MappingReducible.trans (hAB : MappingReducible encA encB A B)
    (hBC : MappingReducible encB encC B C) : MappingReducible encA encC A C :=
  ManyOneReducibleBy.trans (fun _ _ hf hg => hg.comp hf) hAB hBC

/-- A reduction from `A` to `B` is also a reduction from `Aᶜ` to `Bᶜ`. -/
theorem MappingReducible.compl (h : MappingReducible encA encB A B) :
    MappingReducible encA encB Aᶜ Bᶜ :=
  ManyOneReducibleBy.compl h

/-- **Decidability transfers backwards along mapping reductions.** -/
theorem IsDecidable.of_mappingReducible (hB : IsDecidable B encB)
    (h : MappingReducible encA encB A B) : IsDecidable A encA :=
  isDecidable_iff.mpr
    (ManyOneReducibleBy.trans (C := {true}) (fun _ _ hf hg => hg.comp hf) h hB.exists_isComputable)

/-- **Undecidability transfers forwards along mapping reductions.** -/
theorem MappingReducible.not_isDecidable (h : MappingReducible encA encB A B)
    (hA : ¬IsDecidable A encA) : ¬IsDecidable B encB :=
  fun hB => hA (hB.of_mappingReducible h)

end Turing.MultiTapeTM
