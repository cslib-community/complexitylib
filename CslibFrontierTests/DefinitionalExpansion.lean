/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.DefinitionalExpansion
public import CslibFrontier.Logics.FirstOrder.Ordered.Basic

/-! # Unfolding defined symbols into the ordered vocabulary

A vocabulary `D` with a constant `top`, a binary relation `below` and a unary relation `notTop`
is unfolded into the ordered vocabulary, which has the constants `0`, `1` and `max`: `top`
becomes `max`, `below x y` becomes `¬ y ≤ x`, and `notTop x` becomes `∃ y, ¬ y ≤ x`, which is
not quantifier-free. -/

@[expose] public section

namespace Cslib.Tests.DefinitionalExpansion

open FirstOrder Language Structure Cslib.Logic.FO Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 3) := ⟨by decide⟩

/-- A constant symbol. -/
inductive DFunc : ℕ → Type
  | top : DFunc 0

/-- A binary and a unary relation symbol. -/
inductive DRel : ℕ → Type
  | below : DRel 2
  | notTop : DRel 1

abbrev D : Language := ⟨DFunc, DRel⟩

instance : D.Structure (Fin 3) where
  funMap | .top, _ => 2
  RelMap
    | .below, x => x 0 < x 1
    | .notTop, x => x 0 ≠ 2

/-- `top` is the greatest element. -/
def topDef : ∀ {n : ℕ}, D.Functions n → (language L).Term (Fin n)
  | _, .top => max L

/-- `below x y` is `¬ y ≤ x`; `notTop x` is `∃ y, ¬ y ≤ x`, with a quantifier. -/
noncomputable def relDef : ∀ {n : ℕ}, D.Relations n → (language L).Formula (Fin n)
  | _, .below => (le L (.var 1) (.var 0)).not
  | _, .notTop => Formula.iExs Unit (le L (.var (.inr ())) (.var (.inl 0))).not

theorem realize_topDef {n : ℕ} (f : D.Functions n) (x : Fin n → Fin 3) :
    (topDef f).realize x = funMap f x := by
  cases f
  rfl

theorem realize_relDef {n : ℕ} (R : D.Relations n) (x : Fin n → Fin 3) :
    (relDef R).Realize x ↔ RelMap R x := by
  cases R
  · rw [relDef, Formula.realize_not, Ordered.realize_le, not_le]
    rfl
  · rw [relDef, Formula.realize_iExs]
    simp only [Formula.realize_not, Ordered.realize_le, not_le]
    change (∃ i : Unit → Fin 3, x 0 < i ()) ↔ x 0 ≠ 2
    constructor
    · rintro ⟨i, hi⟩ h
      rw [h] at hi
      exact absurd hi (not_lt.mpr (Fin.le_last (i ())))
    · intro h
      exact ⟨fun _ => 2, lt_of_le_of_ne (Fin.le_last (x 0)) h⟩

/-- Every element other than `top` is below `top`: a sentence with a constant and a bound
variable. -/
noncomputable def belowTop : D.Formula Empty :=
  Formula.iAlls Unit ((Relations.formula₁ (DRel.notTop : D.Relations 1) (.var (.inr ()))).iff
    (Relations.formula₂ (DRel.below : D.Relations 2) (.var (.inr ()))
      (Constants.term (DFunc.top : D.Constants))))

/-- The unfolded sentence holds in the ordered structure `Fin 3`, by transfer from `D`. -/
example : Formula.Realize (unfoldSymbols topDef relDef belowTop) (default : Empty → Fin 3) := by
  rw [realize_unfoldSymbols_formula realize_topDef realize_relDef, belowTop,
    Formula.realize_iAlls]
  intro i
  simp only [Formula.realize_iff, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr]
  change i () ≠ 2 ↔ i () < 2
  generalize i () = a
  revert a
  decide

/-- `top` is not `notTop`: unfolding the constant inside the quantified definition. -/
example : ¬Formula.Realize (unfoldSymbols topDef relDef
    (Relations.formula₁ (DRel.notTop : D.Relations 1)
      (Constants.term (DFunc.top : D.Constants)) : D.Formula Empty))
    (default : Empty → Fin 3) := by
  rw [realize_unfoldSymbols_formula realize_topDef realize_relDef, Formula.realize_rel₁]
  change ¬((2 : Fin 3) ≠ 2)
  decide

end Cslib.Tests.DefinitionalExpansion
