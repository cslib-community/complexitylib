/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Mathlib.Data.FinEnum
public import Mathlib.Data.FinEnum.Option
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Encodings of fixed finite types

A finite type is encoded by unary ranks in one fixed enumeration. The enumeration and its size
are independent of the runtime input; this does not give a uniform algorithm for growing types.
Concrete finite types with a `FinEnum` instance use `Turing.MultiTapeTM.encFinEnum`, which is
computable; generic `[Finite α]` parameters use `Turing.MultiTapeTM.encFinite`.

## Main definitions

* `Turing.MultiTapeTM.encFinEnum`: computable unary ranks for a constructively enumerated finite
  type.
* `Turing.MultiTapeTM.encFinite`: unary ranks for a fixed finite type.

## Main results

* `Turing.MultiTapeTM.length_encFinEnum_lt`: the cardinality bounds every constructively encoded
  rank.
* `Turing.MultiTapeTM.length_encFinite_lt`: the cardinality bounds every encoded rank.

## References

Adapts Computability/Probabilistic/Finite.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing unary encoding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Concrete bit enumeration. -/
instance instFinEnumBool : FinEnum Bool :=
  FinEnum.ofList [false, true] (by decide)

/-- Encode a constructively enumerated finite type by unary ranks. -/
def encFinEnum (α : Type) [FinEnum α] : α ↪ List Bool :=
  ⟨fun a => encUnary (FinEnum.equiv a).val, fun _ _ h =>
    FinEnum.equiv.injective (Fin.ext (encUnary.injective h))⟩

/-- Every constructively encoded finite tag has length less than the fixed domain's cardinality. -/
theorem length_encFinEnum_lt {α : Type} [FinEnum α] (a : α) :
    (encFinEnum α a).length < Nat.card α := by
  let _ : Fintype α := inferInstance
  simp [encFinEnum, Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard]

/-- Encode a fixed finite type by unary ranks in an enumeration chosen once. -/
noncomputable def encFinite (α : Type) [Finite α] : α ↪ List Bool :=
  let _ := Fintype.ofFinite α
  ⟨fun a => encUnary (Fintype.equivFin α a).val, fun _ _ h =>
    (Fintype.equivFin α).injective (Fin.ext (encUnary.injective h))⟩

/-- Every encoded finite tag has length less than the fixed domain's cardinality. -/
theorem length_encFinite_lt {α : Type} [Finite α] (a : α) :
    (encFinite α a).length < Nat.card α := by
  let _ := Fintype.ofFinite α
  simp [encFinite, Nat.card_eq_fintype_card]

end Turing.MultiTapeTM
