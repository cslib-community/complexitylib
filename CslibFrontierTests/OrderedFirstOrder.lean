/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.Ordered.Interpretation

/-!
# Canonical ordered first-order clients

These use the minimal universe of size two, the non-power-of-two universe of size three,
least-significant-bit indexing, input constants, a quantified mixed input/numeric formula,
and a numeric query through the existing relational interpretation API.
-/

namespace CslibFrontierTests.OrderedFirstOrder

open FirstOrder Language Structure Cslib.Logic FO

private inductive Relation : ℕ → Type
  | mark : Relation 1

private abbrev inputLanguage : Language where
  Functions _ := Empty
  Relations := Relation

private instance : inputLanguage.IsRelational := fun _ => inferInstance

private instance {n : ℕ} : inputLanguage.Structure (Fin n) where
  RelMap r x := match r with | .mark => (x 0).val = 2

private instance : Fact (2 ≤ 2) := ⟨by decide⟩
private instance : Fact (2 ≤ 3) := ⟨by decide⟩

example : (Ordered.zero inputLanguage).realize (fun _ : Unit => (0 : Fin 2)) ≠
    (Ordered.one inputLanguage).realize (fun _ : Unit => (0 : Fin 2)) :=
  Ordered.realize_zero_ne_one _

example : ((Ordered.max inputLanguage).realize (fun _ : Unit => (0 : Fin 2))).val = 1 := rfl

example : ((Ordered.max inputLanguage).realize (fun _ : Unit => (0 : Fin 3))).val = 2 := rfl

-- 2 is binary10: bit0 is false and bit1 is true, even though the base has size3.
example : ¬ (Ordered.bit inputLanguage (.var ()) (Ordered.zero inputLanguage)).Realize
    (fun _ : Unit => (2 : Fin 3)) := by
  rw [Ordered.realize_bit]
  decide

example : (Ordered.bit inputLanguage (.var ()) (Ordered.one inputLanguage)).Realize
    (fun _ : Unit => (2 : Fin 3)) := by
  rw [Ordered.realize_bit]
  decide

private def mixedBody : (Ordered.language inputLanguage).Formula (Fin 1) :=
  (LHom.sumInl : inputLanguage →ᴸ Ordered.language inputLanguage).onFormula
    (Relations.formula₁ (L := inputLanguage) Relation.mark (.var 0)) ⊓
  Ordered.bit inputLanguage (.var 0) (Ordered.one inputLanguage)

-- An input relation and numeric constant occur together under an existential quantifier.
example : Fin 3 ⊨ closeEx (Fin 1) mixedBody := by
  apply (realize_closeEx _ _).mpr
  refine ⟨fun _ => 2, ?_⟩
  change ((LHom.sumInl : inputLanguage →ᴸ Ordered.language inputLanguage).onFormula
    (Relations.formula₁ (L := inputLanguage) Relation.mark (.var 0)) ⊓
    Ordered.bit inputLanguage (.var 0) (Ordered.one inputLanguage)).Realize (fun _ => (2 : Fin 3))
  rw [Formula.realize_inf, Ordered.realize_inputFormula, Formula.realize_rel₁,
    Ordered.realize_bit]
  exact ⟨rfl, by decide⟩

private def oddQuery : Interpretation (Ordered.language inputLanguage) inputLanguage Unit where
  domain := ⊤
  rel r := match r with
    | .mark => Ordered.bit inputLanguage (.var (0, ())) (Ordered.zero inputLanguage)

example (x : oddQuery.Model (Fin 3)) :
    RelMap (L := inputLanguage) Relation.mark ![x] ↔ (x.val ()).val.testBit 0 = true := by
  change (Ordered.bit inputLanguage (.var (0, ())) (Ordered.zero inputLanguage)).Realize
    (fun p => (![x] p.1).val p.2) ↔ _
  rw [Ordered.realize_bit]
  rfl

example (φ : inputLanguage.Sentence) :
    Fin 3 ⊨ oddQuery.onSentence φ ↔ oddQuery.Model (Fin 3) ⊨ φ :=
  Interpretation.realize_onSentence _ _

example (φ : inputLanguage.Sentence) :
    Fin 3 ⊨ (Ordered.forget inputLanguage).onSentence φ ↔ Fin 3 ⊨ φ :=
  Ordered.realize_forget_onSentence φ

-- Input constants remain genuine function symbols alongside the added numeric constants.
private abbrev constantLanguage := Language.constantsOn Unit

private instance : constantLanguage.Structure (Fin 3) :=
  Language.constantsOn.structure (fun _ => 2)

private noncomputable def constantSentence : constantLanguage.Sentence :=
  closeEx (Fin 1) ((Constants.term ()).equal (.var 0))

example : Fin 3 ⊨ constantSentence := by
  apply (realize_closeEx _ _).mpr
  refine ⟨fun _ => 2, ?_⟩
  rw [Formula.realize_equal]
  rfl

example : Fin 3 ⊨
    (LHom.sumInl : constantLanguage →ᴸ Ordered.language constantLanguage).onSentence
      constantSentence := by
  exact (LHom.realize_onSentence _ _ _).mpr (by
    apply (realize_closeEx _ _).mpr
    exact ⟨fun _ => 2, Formula.realize_equal.mpr rfl⟩)

end CslibFrontierTests.OrderedFirstOrder
