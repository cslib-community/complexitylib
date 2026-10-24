/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation

/-!
# One-dimensional interpretations

An interpretation of dimension `Unit` defines its relations on single elements. Its relation
formulas define new relations on the universe of the structure itself
(`Interpretation.unitStructure`), and when its domain formula holds of every element, the
interpreted structure is isomorphic to this structure (`Interpretation.unitModelEquiv`). Many
first-order reductions, such as complementing a relation, are of this kind; through this
isomorphism their correctness is a statement about the input universe, without the tuples and
subtypes of `Interpretation.Model`.

## Main definitions

* `Cslib.Logic.FO.Interpretation.unitStructure`: the relations defined by a one-dimensional
  interpretation, on the universe of the structure itself.
* `Cslib.Logic.FO.Interpretation.unitModelEquiv`: the interpreted structure is isomorphic to it
  when the domain formula always holds.

## Main results

* `Cslib.Logic.FO.Interpretation.relMap_unitStructure`: the defined relations.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v' w

namespace Cslib.Logic.FO.Interpretation

open FirstOrder Language Structure

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L'.IsRelational]
  (I : Interpretation L L' Unit) (M : Type w) [L.Structure M]

/-- The relations defined by a one-dimensional interpretation on the universe of `M` itself: a
relation symbol holds of some elements when its defining formula holds of them. -/
@[instance_reducible]
def unitStructure : L'.Structure M where
  RelMap R x := (I.rel R).Realize fun p => x p.1

variable {M} in
/-- On single elements, a target relation holds exactly when its defining formula does. -/
@[fo_realize]
theorem relMap_unitStructure {n : ℕ} (R : L'.Relations n) (x : Fin n → M) :
    (I.unitStructure M).RelMap R x ↔ (I.rel R).Realize fun p => x p.1 :=
  Iff.rfl

/-- When the domain formula of a one-dimensional interpretation holds of every element, the
interpreted structure is isomorphic to `M` with the relations defined by the interpretation. -/
def unitModelEquiv (hdom : ∀ x : M, I.domain.Realize fun _ => x) :
    @Language.Equiv L' (I.Model M) M _ (I.unitStructure M) :=
  letI := I.unitStructure M
  { toFun x := x.1 ()
    invFun x := ⟨fun _ => x, hdom x⟩
    left_inv _ := Model.ext rfl
    right_inv _ := rfl
    map_fun' f := isEmptyElim f
    map_rel' _ _ := Iff.rfl }

/-- `I.unitModelEquiv M hdom` maps a 1-dimensional interpreted element `x` to `x.1 ()`. -/
@[simp]
theorem unitModelEquiv_apply (hdom : ∀ x : M, I.domain.Realize fun _ => x) (x : I.Model M) :
    I.unitModelEquiv M hdom x = x.1 () :=
  rfl

end Cslib.Logic.FO.Interpretation
