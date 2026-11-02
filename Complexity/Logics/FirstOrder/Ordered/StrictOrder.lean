/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Query
public import Complexity.Logics.SecondOrder.Projection

/-!
# Strict-order interpretations of canonical ordered structures

The one-dimensional interpretation retains every input relation and reads strict order from
canonical non-strict order. It allows order-based relational formulas to be reused with the
canonical ordered vocabulary, including in the full-tuple power interpretation.

## Main definitions

* `Cslib.Logic.FO.Ordered.strictOrderInterpretation`: the relational strict-order interpretation.
* `Cslib.Logic.FO.Ordered.strictOrderEquiv`: the isomorphism with the canonical input universe.

## Main results

* `Cslib.Logic.FO.Ordered.realize_strictOrder_onFormula`: arbitrary formula truth is preserved.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 1.26 and Proposition 3.5.
-/

@[expose] public section

universe u v

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- The one-dimensional interpretation retaining the input relations and reading strict order
from canonical non-strict order. -/
def strictOrderInterpretation (L : Language.{u, v}) :
    FO.Interpretation (language L) (L.sum ESO.orderLanguage) Unit where
  domain := ⊤
  rel := fun {n} r => match r with
    | .inl R => Relations.formula (L := language L) (Sum.inl R) fun i => .var (i, ())
    | .inr r => by
      rcases r with ⟨⟨⟩, h⟩
      subst n
      exact ∼(Relations.formula (L := language L) (Sum.inr NumericRelation.le)
        fun i => .var (if i = 0 then 1 else 0, ()))

/-- The canonical strict-order structure interpreted above is the original ordered universe. -/
def strictOrderEquiv {L : Language.{u, v}} [L.IsRelational] (M : Ordered.Structure L) :
    letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
      (ESO.orderRelOfEquiv (Equiv.refl M));
    (strictOrderInterpretation L).Model M ≃[L.sum ESO.orderLanguage] M := by
  letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
    (ESO.orderRelOfEquiv (Equiv.refl M))
  refine
    { toFun := fun x => x.1 ()
      invFun := fun x => ⟨fun _ => x, Formula.realize_top.2 trivial⟩
      left_inv := fun _ => FO.Interpretation.Model.ext rfl
      right_inv := fun _ => rfl
      map_fun' := fun f => isEmptyElim f
      map_rel' := ?_ }
  intro n r x
  cases r with
  | inl R => exact Iff.rfl
  | inr r =>
    rcases r with ⟨⟨⟩, h⟩
    subst n
    change (x 0).1 () < (x 1).1 () ↔ ¬ (x 1).1 () ≤ (x 0).1 ()
    exact not_le.symm

/-- Pulling a relational strict-order formula back to the canonical ordered vocabulary preserves
its truth for every free-variable assignment. -/
@[fo_realize]
theorem realize_strictOrder_onFormula {L : Language.{u, v}} [L.IsRelational]
    (M : Ordered.Structure L) {α : Type*} (φ : (L.sum ESO.orderLanguage).Formula α)
    (x : α → M) :
    ((strictOrderInterpretation L).onFormula φ).Realize (fun p => x p.1) ↔
      letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
        (ESO.orderRelOfEquiv (Equiv.refl M))
      φ.Realize x := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
    (ESO.orderRelOfEquiv (Equiv.refl M))
  let y : α → (strictOrderInterpretation L).Model M :=
    fun a => ⟨fun _ => x a, Formula.realize_top.mpr trivial⟩
  rw [(strictOrderInterpretation L).realize_onFormula φ y]
  exact (StrongHomClass.realize_formula (strictOrderEquiv M) φ).symm

end Cslib.Logic.FO.Ordered
