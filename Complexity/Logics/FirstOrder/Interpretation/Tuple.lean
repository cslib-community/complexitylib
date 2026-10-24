/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation

/-!
# Interpretations on all tuples

The relation formulas of an interpretation `I` of dimension `ι` define relations on all tuples
`ι → M` of an `L`-structure `M` (`Interpretation.tupleStructure`). When the domain formula holds of
every tuple, the interpreted structure is isomorphic to this structure
(`Interpretation.tupleModelEquiv`), so that statements about the interpreted structure become
statements about tuples of elements of `M`, without the subtypes of `Interpretation.Model`. This
generalizes `Interpretation.unitStructure` from dimension one, where the tuples are identified
with the elements themselves, to every dimension.

Through this isomorphism the pullback of a formula along such an interpretation is realized as the
formula itself in the structure on tuples (`Interpretation.realize_onFormula_tupleStructure`). In
particular, the domain and relation formulas of a composite `J.comp I` whose first
interpretation `I` has such a domain are realized as those of `J` in the structure defined by `I`
on tuples (`Interpretation.realize_comp_domain_tupleStructure`,
`Interpretation.realize_comp_rel_tupleStructure`), at arbitrary valuations.

## Main definitions

* `Cslib.Logic.FO.Interpretation.tupleStructure`: the relations defined by an interpretation on
  all tuples.
* `Cslib.Logic.FO.Interpretation.tupleModelEquiv`: the interpreted structure is isomorphic to it
  when the domain formula always holds.

## Main results

* `Cslib.Logic.FO.Interpretation.relMap_tupleStructure`: the defined relations.
* `Cslib.Logic.FO.Interpretation.realize_onFormula_tupleStructure`: the pullback of a formula
  along an interpretation whose domain formula always holds.
* `Cslib.Logic.FO.Interpretation.realize_comp_domain_tupleStructure`,
  `Cslib.Logic.FO.Interpretation.realize_comp_rel_tupleStructure`: the domain and relation
  formulas of a composite.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v' u'' v'' w

namespace Cslib.Logic.FO.Interpretation

open FirstOrder Language Structure

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L'.IsRelational] {ι : Type*}
  (I : Interpretation L L' ι) (M : Type w) [L.Structure M]

/-- The relations defined by an interpretation on all tuples `ι → M`: a relation symbol holds of
some tuples when its defining formula holds of their coordinates. -/
@[instance_reducible]
def tupleStructure : L'.Structure (ι → M) where
  RelMap R x := (I.rel R).Realize fun p => x p.1 p.2

variable {M} in
/-- On all tuples, a target relation holds exactly when its defining formula does. -/
@[fo_realize]
theorem relMap_tupleStructure {n : ℕ} (R : L'.Relations n) (x : Fin n → ι → M) :
    (I.tupleStructure M).RelMap R x ↔ (I.rel R).Realize fun p => x p.1 p.2 :=
  Iff.rfl

/-- When the domain formula of an interpretation holds of every tuple, the interpreted structure
is isomorphic to the tuples with the relations defined by the interpretation. -/
def tupleModelEquiv (hdom : ∀ x : ι → M, I.domain.Realize x) :
    @Language.Equiv L' (I.Model M) (ι → M) _ (I.tupleStructure M) :=
  letI := I.tupleStructure M
  { toFun x := x.1
    invFun x := ⟨x, hdom x⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_fun' f := isEmptyElim f
    map_rel' _ _ := Iff.rfl }

/-- `I.tupleModelEquiv M hdom` maps an interpreted element `x` to its underlying tuple `x.1`. -/
@[simp]
theorem tupleModelEquiv_apply (hdom : ∀ x : ι → M, I.domain.Realize x) (x : I.Model M) :
    I.tupleModelEquiv M hdom x = x.1 :=
  rfl

/-- Equality of functions on `Unit` is equality at `()`. -/
@[fo_realize]
theorem fun_unit_eq_iff {α : Type*} {f g : Unit → α} : f = g ↔ f () = g () :=
  ⟨fun h => congrFun h (), fun h => funext fun () => h⟩

variable {M} [Finite ι]

/-- The pullback of a formula along an interpretation whose domain formula holds of every tuple is
realized as the formula in the structure defined on tuples. -/
theorem realize_onFormula_tupleStructure (hdom : ∀ x : ι → M, I.domain.Realize x) {α : Type*}
    (φ : L'.Formula α) (v : α → ι → M) :
    (I.onFormula φ).Realize (fun p => v p.1 p.2) ↔
      @Formula.Realize L' (ι → M) (I.tupleStructure M) α φ v := by
  let := I.tupleStructure M
  let w : α → I.Model M := fun a => ⟨v a, hdom (v a)⟩
  exact (realize_onFormula φ w).trans
    (StrongHomClass.realize_formula (I.tupleModelEquiv M hdom) φ (v := w)).symm

variable {L'' : Language.{u'', v''}} {κ : Type*} [Finite κ]

/-- The domain formula of a composite `J.comp I`, when the domain formula of `I` holds of every
tuple, is realized as the domain formula of `J` in the structure defined by `I` on tuples. -/
@[fo_realize high]
theorem realize_comp_domain_tupleStructure (J : Interpretation L' L'' κ)
    (hdom : ∀ x : ι → M, I.domain.Realize x) (v : κ × ι → M) :
    (J.comp I).domain.Realize v ↔
      @Formula.Realize L' (ι → M) (I.tupleStructure M) κ J.domain fun j i => v (j, i) := by
  rw [realize_comp_domain]
  exact ⟨fun ⟨_, h⟩ => (realize_onFormula_tupleStructure I hdom J.domain _).1
      ((realize_onFormula J.domain _).2 h),
    fun h => ⟨fun j => hdom _, (realize_onFormula J.domain _).1
      ((realize_onFormula_tupleStructure I hdom J.domain _).2 h)⟩⟩

/-- A relation formula of a composite `J.comp I`, when the domain formula of `I` holds of every
tuple, is realized as the relation formula of `J` in the structure defined by `I` on tuples. -/
@[fo_realize high]
theorem realize_comp_rel_tupleStructure (J : Interpretation L' L'' κ)
    (hdom : ∀ x : ι → M, I.domain.Realize x) {n : ℕ} (R : L''.Relations n)
    (v : Fin n × (κ × ι) → M) :
    ((J.comp I).rel R).Realize v ↔
      @Formula.Realize L' (ι → M) (I.tupleStructure M) _ (J.rel R) fun p i => v (p.1, p.2, i) :=
  Formula.realize_relabel.trans
    (realize_onFormula_tupleStructure I hdom (J.rel R) fun p i => v (p.1, p.2, i))

end Cslib.Logic.FO.Interpretation
