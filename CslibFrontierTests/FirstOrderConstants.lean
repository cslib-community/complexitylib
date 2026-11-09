/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Constants

/-! # Nonvacuous clients of formula-defined target constants -/

@[expose] public section

namespace Cslib.Tests.FirstOrderConstants

open FirstOrder Language Structure
open Cslib.Logic.FO

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩

example : (Ordered.constants L).Valid (Fin 2) := Ordered.constants_valid
example : (Ordered.constants L).Valid (Fin 3) := Ordered.constants_valid

example : (((Ordered.constants L).value (Ordered.constants_valid (n := 3)) .max).val ()).val = 2 :=
  Ordered.constants_value_val .max

example : (((Ordered.constants L).value (Ordered.constants_valid (n := 2)) .one).val ()).val = 1 :=
  Ordered.constants_value_val .one

/-- A target formula mixing a free variable with a newly interpreted target constant. -/
def atMax : L[[Ordered.NumericFunction 0]].Formula Unit :=
  Term.equal (.var ()) (L.con .max).term

example (v : Unit → (Ordered.forget L).Model (Fin 3)) :
    ((Ordered.constants L).onFormula atMax).Realize (fun p => (v p.1).val p.2) ↔
      (v ()).val () = ((Ordered.constants L).value Ordered.constants_valid .max).val () := by
  rw [(Ordered.constants L).realize_onFormula Ordered.constants_valid]
  simp only [atMax, Formula.realize_equal, Term.realize_var, Term.realize_constants]
  exact ⟨fun h => congrArg (fun x => x.val ()) h,
    fun h => Interpretation.Model.ext (funext fun i => by cases i; exact h)⟩

/-- Quantification with a target constant remains a native first-order sentence. -/
noncomputable def hasMax : L[[Ordered.NumericFunction 0]].Sentence :=
  closeEx Unit atMax

example : Fin 3 ⊨ (Ordered.constants L).onSentence hasMax := by
  rw [(Ordered.constants L).realize_onSentence Ordered.constants_valid]
  simp only [hasMax, closeEx, Sentence.Realize, Formula.realize_iExs,
    Formula.realize_relabel, atMax, Formula.realize_equal, Term.realize_var,
    Term.realize_constants]
  exact ⟨fun _ => (Ordered.constants L).value Ordered.constants_valid .max, rfl⟩

/-- A formula with two distinct target constants, including under negation. -/
def separated : L[[Ordered.NumericFunction 0]].Sentence :=
  ((L.con .zero).term.equal (L.con .one).term).not

example : Fin 2 ⊨ (Ordered.constants L).onSentence separated := by
  rw [(Ordered.constants L).realize_onSentence Ordered.constants_valid]
  simp only [separated, Sentence.Realize, Formula.realize_not, Formula.realize_equal,
    Term.realize_constants]
  intro h
  have hv := congrArg (fun x : (Ordered.forget L).Model (Fin 2) => (x.val ()).val) h
  change (((Ordered.constants L).value Ordered.constants_valid .zero).val ()).val =
    (((Ordered.constants L).value Ordered.constants_valid .one).val ()).val at hv
  simp only [Ordered.constants_value_val] at hv
  contradiction

/-- Definitions selecting no tuple are not silently assigned arbitrary values. -/
def absent : (Ordered.forget L).WithConstants Unit where
  constant _ := ⊥

example : ¬ absent.Valid (Fin 2) := by
  intro h
  obtain ⟨x, hx, _⟩ := h ()
  exact Formula.realize_bot.mp hx

/-- Definitions selecting multiple tuples fail the uniqueness requirement. -/
def ambiguous : (Ordered.forget L).WithConstants Unit where
  constant _ := ⊤

example : ¬ ambiguous.Valid (Fin 2) := by
  intro h
  have heq := (h ()).unique (y₁ := Ordered.forgetEquiv.symm (0 : Fin 2))
    (y₂ := Ordered.forgetEquiv.symm (1 : Fin 2))
    (Formula.realize_top.mpr trivial) (Formula.realize_top.mpr trivial)
  have hv := congrArg (fun x : (Ordered.forget L).Model (Fin 2) => (x.val ()).val) heq
  change 0 = 1 at hv
  contradiction

/-- No target constants impose no nonemptiness requirement on an interpreted domain. -/
def noConstants : (Interpretation.empty L L).WithConstants Empty where
  constant c := c.elim

example : noConstants.Valid (Fin 0) := fun c => c.elim

/-- An input relation selects an element without any source constant symbols. -/
inductive Mark : ℕ → Type
  | mark : Mark 1

abbrev markedLanguage : Language := ⟨fun _ => Empty, Mark⟩

instance : markedLanguage.IsRelational := fun _ => inferInstance

instance : markedLanguage.Structure (Fin 3) where
  RelMap r xs := match r with | .mark => xs 0 = 2

/-- The target constant is defined solely by the input unary relation. -/
def marked : (Interpretation.id markedLanguage).WithConstants Unit where
  constant _ := Relations.formula₁ (L := markedLanguage) .mark (.var ())

theorem marked_valid : marked.Valid (Fin 3) := by
  intro c
  refine ⟨Interpretation.idEquiv.symm (2 : Fin 3), ?_, ?_⟩
  · simp only [marked, Formula.realize_rel₁]
    rfl
  · intro x hx
    simp only [marked, Formula.realize_rel₁] at hx
    apply Interpretation.Model.ext
    funext i
    cases i
    exact hx

/-- The free variable survives quantification of another variable and of the selected constant. -/
noncomputable def quantifiedFree : markedLanguage[[Unit]].Formula Unit :=
  Formula.iAlls Unit
    (((Term.var (Sum.inr ())).equal (markedLanguage.con ()).term).imp
      ((Term.var (Sum.inr ())).equal (.var (Sum.inl ()))))

example (v : Unit → (Interpretation.id markedLanguage).Model (Fin 3)) :
    (marked.onFormula quantifiedFree).Realize (fun p => (v p.1).val p.2) ↔
      v () = marked.value marked_valid () := by
  rw [marked.realize_onFormula marked_valid]
  simp only [quantifiedFree, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_equal, Term.realize_var, Term.realize_constants]
  constructor
  · intro h
    exact (h (fun _ => marked.value marked_valid ()) rfl).symm
  · intro h x hx
    exact hx.trans h.symm

end Cslib.Tests.FirstOrderConstants
