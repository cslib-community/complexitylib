/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Monadic

/-! # The monadic small model property: checked instances

A monadic language with one nullary and two unary symbols, interpreted on `ℕ`: small models of
sentences true in `ℕ`, a sentence attaining the bound `max q 1 * 2 ^ k`, and the role of the
factor `max q 1` for sentences of quantifier rank `0`. Over the empty language, `Fin 3` and
`Fin 5` agree on sentences of quantifier rank at most `3`. -/

@[expose] public section

namespace Cslib.Tests.MonadicSmallModel

open FirstOrder Language Structure
open Cslib.Logic.FO Cslib.Logic.FO.Monadic

/-- Relation symbols: one nullary symbol, and two unary symbols indexed by `Bool`. -/
def Rel : ℕ → Type
  | 0 => Unit
  | 1 => Bool
  | _ + 2 => Empty

/-- A monadic language with one nullary and two unary relation symbols. -/
def lang : Language := ⟨fun _ => Empty, Rel⟩

instance : lang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Finite (lang.Relations 1) := inferInstanceAs (Finite Bool)

theorem lang_monadic : ∀ l, 2 ≤ l → IsEmpty (lang.Relations l)
  | _ + 2, _ => inferInstanceAs (IsEmpty Empty)

theorem card_relations_one : Nat.card (lang.Relations 1) = 2 :=
  (Nat.card_eq_fintype_card (α := Bool)).trans Fintype.card_bool

/-- The nullary symbol. -/
def flag : lang.Relations 0 := ()

/-- The unary symbol interpreted as evenness on `ℕ`. -/
def even : lang.Relations 1 := true

/-- The unary symbol interpreted as `· < 3` on `ℕ`. -/
def small : lang.Relations 1 := false

/-- The interpretation of the unary symbols on `ℕ`. -/
def unaryRel : Bool → ℕ → Prop
  | true, m => m % 2 = 0
  | false, m => m < 3

/-- The interpretation of the relation symbols on `ℕ`. -/
def natRel : ∀ {l : ℕ}, lang.Relations l → (Fin l → ℕ) → Prop
  | 0, _, _ => True
  | 1, b, x => unaryRel b (x 0)
  | _ + 2, R, _ => (R : Empty).elim

instance : lang.Structure ℕ where
  funMap f := (f : Empty).elim
  RelMap := natRel

theorem relMap_even (m : ℕ) : RelMap even ![m] ↔ m % 2 = 0 := Iff.rfl

theorem relMap_small (m : ℕ) : RelMap small ![m] ↔ m < 3 := Iff.rfl

/-- "Some element is even and small, and some element is neither", of quantifier rank `1`. -/
def evenSmallAndNeither : lang.Sentence :=
  (∃' (even.boundedFormula₁ (&0) ⊓ small.boundedFormula₁ (&0))) ⊓
    ∃' ((even.boundedFormula₁ (&0)).not ⊓ (small.boundedFormula₁ (&0)).not)

theorem quantifierRank_evenSmallAndNeither : quantifierRank evenSmallAndNeither = 1 := by
  simp [evenSmallAndNeither]

theorem nat_realize_evenSmallAndNeither : ℕ ⊨ evenSmallAndNeither := by
  simp only [evenSmallAndNeither, Sentence.Realize, Formula.Realize, BoundedFormula.realize_inf,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.snoc_zero, relMap_even, relMap_small]
  exact ⟨⟨0, by decide, by decide⟩, 5, by decide, by decide⟩

/-- `evenSmallAndNeither` holds in `ℕ`, so it has a model with at most `1 * 2 ^ 2 = 4`
elements. -/
example : ∃ n, n + 1 ≤ 4 ∧
    ∃ _ : lang.Structure (Fin (n + 1)), Fin (n + 1) ⊨ evenSmallAndNeither := by
  have h := exists_fin_realize lang_monadic nat_realize_evenSmallAndNeither
  rwa [quantifierRank_evenSmallAndNeither, card_relations_one] at h

/-- "Every color occurs", of quantifier rank `1`. -/
def allColors : lang.Sentence :=
  (∃' (even.boundedFormula₁ (&0) ⊓ small.boundedFormula₁ (&0))) ⊓
    (∃' (even.boundedFormula₁ (&0) ⊓ (small.boundedFormula₁ (&0)).not)) ⊓
    (∃' ((even.boundedFormula₁ (&0)).not ⊓ small.boundedFormula₁ (&0))) ⊓
    ∃' ((even.boundedFormula₁ (&0)).not ⊓ (small.boundedFormula₁ (&0)).not)

theorem quantifierRank_allColors : quantifierRank allColors = 1 := by
  simp [allColors]

theorem nat_realize_allColors : ℕ ⊨ allColors := by
  simp only [allColors, Sentence.Realize, Formula.Realize, BoundedFormula.realize_inf,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.snoc_zero, relMap_even, relMap_small]
  exact ⟨⟨⟨⟨0, by decide, by decide⟩, 4, by decide, by decide⟩, 1, by decide, by decide⟩,
    5, by decide, by decide⟩

/-- The bound is attained: every model of `allColors` has at least `4 = max 1 1 * 2 ^ 2`
elements, since the color map onto `Bool × Bool` is surjective. -/
theorem four_le_card_of_realize_allColors {M : Type} [Finite M] [lang.Structure M]
    (h : M ⊨ allColors) : 4 ≤ Nat.card M := by
  simp only [allColors, Sentence.Realize, Formula.Realize, BoundedFormula.realize_inf,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.snoc_zero] at h
  obtain ⟨⟨⟨⟨a, ha⟩, b, hb⟩, c, hc⟩, d, hd⟩ := h
  classical
  let f : M → Bool × Bool := fun m =>
    (decide (RelMap even ![m]), decide (RelMap small ![m]))
  have hf : Function.Surjective f := by
    rintro ⟨_ | _, _ | _⟩
    · exact ⟨d, by simp [f, hd.1, hd.2]⟩
    · exact ⟨c, by simp [f, hc.1, hc.2]⟩
    · exact ⟨b, by simp [f, hb.1, hb.2]⟩
    · exact ⟨a, by simp [f, ha.1, ha.2]⟩
  simpa using Nat.card_le_card_of_surjective f hf

/-- The factor `max q 1` matters: `⊤` has quantifier rank `0` and holds in `ℕ`, so it has a model
on some `Fin (n + 1)` within the bound `max 0 1 * 2 ^ k`, but no `Fin (n + 1)` is within
`0 * 2 ^ k = 0`. -/
example :
    (∃ n, n + 1 ≤ max (quantifierRank (⊤ : lang.Sentence)) 1 * 2 ^ Nat.card (lang.Relations 1) ∧
      ∃ _ : lang.Structure (Fin (n + 1)), Fin (n + 1) ⊨ (⊤ : lang.Sentence)) ∧
    ¬ ∃ n, n + 1 ≤ quantifierRank (⊤ : lang.Sentence) * 2 ^ Nat.card (lang.Relations 1) := by
  refine ⟨exists_fin_realize (M := ℕ) lang_monadic (by simp), ?_⟩
  rintro ⟨n, hn⟩
  rw [quantifierRank_top, zero_mul] at hn
  exact Nat.not_succ_le_zero n hn

/-- The nullary symbol holds in `ℕ`, so a small model of it exists, of size at most
`max 0 1 * 2 ^ 2 = 4`; in particular it is nonempty. -/
example : ∃ n, n + 1 ≤ 4 ∧ ∃ _ : lang.Structure (Fin (n + 1)),
    Fin (n + 1) ⊨ (flag.formula default : lang.Sentence) := by
  have h := exists_fin_realize (M := ℕ) lang_monadic (φ := flag.formula default) trivial
  rwa [show quantifierRank (flag.formula default : lang.Sentence) = 0 by simp [Relations.formula],
    card_relations_one] at h

/-! ### The empty language -/

instance (m : ℕ) : Language.empty.Structure (Fin m) := emptyStructure

/-- Over the empty language every element has every color. -/
theorem encard_color_empty {M : Type} [Language.empty.Structure M]
    (C : Set (Language.empty.Relations 1)) :
    {m : M | color Language.empty m = C}.encard = ENat.card M := by
  rw [← Set.encard_univ]
  congr 1
  exact Set.eq_univ_of_forall fun m =>
    (Set.ext fun R => isEmptyElim R : color Language.empty m = C)

theorem encard_color_empty_fin (m : ℕ) (C : Set (Language.empty.Relations 1)) :
    {x : Fin m | color Language.empty x = C}.encard = m := by
  rw [encard_color_empty, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- "There are at least three elements", of quantifier rank `3`. -/
def atLeastThree : Language.empty.Sentence :=
  ∃' ∃' ∃' (((&0).bdEqual (&1)).not ⊓ ((&0).bdEqual (&2)).not ⊓ ((&1).bdEqual (&2)).not)

/-- Over the empty language every element has the same color, so `Fin 3` and `Fin 5` agree on
sentences of quantifier rank at most `3`. -/
theorem fin3_realize_iff_fin5 {φ : Language.empty.Sentence} (hφ : quantifierRank φ ≤ 3) :
    Fin 3 ⊨ φ ↔ Fin 5 ⊨ φ :=
  realize_iff_of_encard (fun _ _ => inferInstance) (fun R => isEmptyElim R)
    (fun C => .inr ⟨(encard_color_empty_fin 3 C).ge, by
      rw [encard_color_empty_fin]
      exact Nat.cast_le.2 (by decide)⟩) hφ

example : Fin 5 ⊨ atLeastThree :=
  (fin3_realize_iff_fin5 (by simp [atLeastThree])).1 (by
    simp only [atLeastThree, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
      BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual]
    exact ⟨0, 1, 2, by decide⟩)

end Cslib.Tests.MonadicSmallModel
