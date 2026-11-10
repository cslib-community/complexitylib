/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Successor
public import CslibFrontier.Logics.FirstOrder.Ordered.BitArithmetic
import CslibFrontier.Tactic.FirstOrder

/-! # The successor vocabulary and successor elimination

The ordered vocabularies here have the constants `0`, `1` and `max`. Both successor definitions
used for elimination, `successor L` (one universal quantifier) and `addSucc` (through `addEq`,
whose definition quantifies over carries), are not quantifier-free. -/

@[expose] public section

namespace Cslib.Tests.OrderedSuccessorLanguage

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨le_rfl⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩

/-! ### The canonical structure composes through Mathlib's sum structure -/

example : (language (succLanguage L)).Structure (Fin 3) := inferInstance

example : (inferInstance : (language (succLanguage L)).Structure (Fin 3)) =
    @Language.sumStructure _ _ _
      (@Language.sumStructure _ _ _ Language.emptyStructure succStructure)
      (numericStructure (by decide)) := rfl

/-- Successor, order and the constants hold together in one structure. -/
example : Formula.Realize
    (succ L (zero _) (one _) ⊓ le _ (zero _) (max _) : (language (succLanguage L)).Formula Empty)
    (default : Empty → Fin 3) := by
  simp only [Formula.realize_inf, realize_succ, realize_le]
  decide

/-- The inclusion of the ordered vocabulary keeps the meaning of `≤` and the constants. -/
example : ¬Formula.Realize ((succInclusion L).onFormula (le L (max L) (zero L)))
    (default : Empty → Fin 3) := by
  rw [realize_succInclusion, realize_le]
  decide

example (x y : (language (succLanguage L)).Term (Fin 2)) :
    (succ L x y ⊓ (Term.equal x y).not).IsQF := by
  fo_qf

/-! ### Elimination with constants and bound variables -/

/-- `0 + 1 = 1` survives elimination of a successor atom between constants. -/
example : Formula.Realize (elimSucc (succ L (zero _) (one _)) : (language L).Formula Empty)
    (default : Empty → Fin 2) := by
  rw [realize_elimSucc_formula, realize_succ]
  decide

/-- `max` is not the successor of `0` on `Fin 3`. -/
example : ¬Formula.Realize (elimSucc (succ L (zero _) (max _)) : (language L).Formula Empty)
    (default : Empty → Fin 3) := by
  rw [realize_elimSucc_formula, realize_succ]
  decide

/-- The greatest element has no successor: a sentence with a constant and a bound variable. -/
noncomputable def maxNoSucc : (language (succLanguage L)).Formula Empty :=
  Formula.iAlls Unit (succ L (max _) (.var (.inr ()))).not

theorem realize_elimSucc_maxNoSucc {n : ℕ} [Fact (2 ≤ n)] (v : Empty → Fin n) :
    Formula.Realize (elimSucc maxNoSucc) v := by
  rw [realize_elimSucc_formula, maxNoSucc, Formula.realize_iAlls]
  intro i
  simp only [Formula.realize_not, realize_succ, realize_max_val, Term.realize_var, Sum.elim_inr]
  have := (i ()).isLt
  omega

/-! ### Elimination through `addEq` agrees with elimination through `successor L` -/

/-- Successor through addition: `x + 1 = y`. -/
noncomputable def addSucc : (language L).Formula (Fin 2) :=
  addEq L (.var 0) (one L) (.var 1)

theorem realize_addSucc {n : ℕ} [Fact (2 ≤ n)] (v : Fin 2 → Fin n) :
    addSucc.Realize v ↔ (v 1).val = (v 0).val + 1 := by
  simp only [addSucc, realize_addEq, realize_one_val, Term.realize_var]
  exact eq_comm

/-- The two eliminations agree on every formula over every `Fin n` with `2 ≤ n`. -/
theorem realize_elimSuccWith_addSucc {α : Type*} {n : ℕ} [Fact (2 ≤ n)]
    (φ : (language (succLanguage L)).Formula α) (v : α → Fin n) :
    Formula.Realize (elimSuccWith addSucc φ) v ↔ Formula.Realize (elimSucc φ) v := by
  rw [realize_elimSuccWith_formula realize_addSucc, realize_elimSucc_formula]

/-- The successor atom on two free variables. -/
def succAtom : (language (succLanguage L)).Formula (Fin 2) :=
  succ L (.var 0) (.var 1)

theorem realize_elimSucc_succAtom {n : ℕ} [Fact (2 ≤ n)] (v : Fin 2 → Fin n) :
    Formula.Realize (elimSucc succAtom) v ↔ (v 0).val + 1 = (v 1).val := by
  simp only [realize_elimSucc_formula, succAtom, realize_succ, Term.realize_var]

theorem realize_elimSuccWith_addSucc_succAtom {n : ℕ} [Fact (2 ≤ n)] (v : Fin 2 → Fin n) :
    Formula.Realize (elimSuccWith addSucc succAtom) v ↔ (v 0).val + 1 = (v 1).val := by
  simp only [realize_elimSuccWith_formula realize_addSucc, succAtom, realize_succ,
    Term.realize_var]

/-- On `Fin 2`, both eliminations accept `0 ↦ 1` and reject the wrap `1 ↦ 0`. -/
example : Formula.Realize (elimSucc succAtom) (![0, 1] : Fin 2 → Fin 2) ∧
    Formula.Realize (elimSuccWith addSucc succAtom) (![0, 1] : Fin 2 → Fin 2) ∧
    ¬Formula.Realize (elimSucc succAtom) (![1, 0] : Fin 2 → Fin 2) ∧
    ¬Formula.Realize (elimSuccWith addSucc succAtom) (![1, 0] : Fin 2 → Fin 2) := by
  simp only [realize_elimSucc_succAtom, realize_elimSuccWith_addSucc_succAtom]
  decide

/-- On `Fin 3`, both eliminations accept `1 ↦ 2`, reject the wrap `2 ↦ 0` from the last element
and reject the jump `0 ↦ 2`. -/
example : Formula.Realize (elimSucc succAtom) (![1, 2] : Fin 2 → Fin 3) ∧
    Formula.Realize (elimSuccWith addSucc succAtom) (![1, 2] : Fin 2 → Fin 3) ∧
    ¬Formula.Realize (elimSucc succAtom) (![2, 0] : Fin 2 → Fin 3) ∧
    ¬Formula.Realize (elimSuccWith addSucc succAtom) (![2, 0] : Fin 2 → Fin 3) ∧
    ¬Formula.Realize (elimSucc succAtom) (![0, 2] : Fin 2 → Fin 3) ∧
    ¬Formula.Realize (elimSuccWith addSucc succAtom) (![0, 2] : Fin 2 → Fin 3) := by
  simp only [realize_elimSucc_succAtom, realize_elimSuccWith_addSucc_succAtom]
  decide

/-- The last element has no successor on `Fin 2` and on `Fin 3`, under either elimination. -/
example : Formula.Realize (elimSucc maxNoSucc) (default : Empty → Fin 2) ∧
    Formula.Realize (elimSuccWith addSucc maxNoSucc) (default : Empty → Fin 3) :=
  ⟨realize_elimSucc_maxNoSucc _,
    (realize_elimSuccWith_addSucc _ _).2 (realize_elimSucc_maxNoSucc _)⟩

end Cslib.Tests.OrderedSuccessorLanguage
