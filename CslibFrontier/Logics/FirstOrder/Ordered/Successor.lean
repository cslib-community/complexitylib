/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Basic
public import CslibFrontier.Logics.FirstOrder.DefinitionalExpansion
public import Mathlib.ModelTheory.Complexity
import CslibFrontier.Tactic.FirstOrder

/-!
# A canonical successor relation for ordered vocabularies

`succLanguage L` adds one binary symbol to an input vocabulary `L`. On `Fin n` it means
`y = x + 1`, so the greatest element has no successor. Its ordered expansion
`language (succLanguage L)` has the input symbols, successor and the canonical numeric symbols
`≤`, `BIT`, `0`, `1` and `max`, so the ordered API (`le`, `bit`, `zero`, `one`, `max`, `addEq`, …)
applies to it unchanged.

Successor is first-order definable from `≤`: `successor L` says that `y` is above `x` and that
every element above `x` is at least `y`. This formula has a universal quantifier. Fragments that
restrict quantification therefore take successor as a primitive symbol; Immerman and Landau list
it among the logical relations, alongside `≤` and `BIT`, for use in quantifier-free
interpretations. `elimSucc` removes the symbol again. It replaces each `succ` atom by an
instance of `successor L`, keeps every other symbol, and preserves truth on every canonical
structure `Fin n` with `2 ≤ n`.

## Main definitions

* `Cslib.Logic.FO.Ordered.SuccRelation`, `Cslib.Logic.FO.Ordered.succSymbols`: the successor
  symbol and its one-symbol relational vocabulary, interpreted on every `Fin n`.
* `Cslib.Logic.FO.Ordered.succLanguage`: an input vocabulary extended by successor.
* `Cslib.Logic.FO.Ordered.succ`: the successor atom on arbitrary terms.
* `Cslib.Logic.FO.Ordered.succInclusion`: the inclusion of the ordered vocabulary.
* `Cslib.Logic.FO.Ordered.successor`: successor defined from `≤` with one universal quantifier.
* `Cslib.Logic.FO.Ordered.elimSuccWith`, `Cslib.Logic.FO.Ordered.elimSucc`: translation back into
  the ordered vocabulary, through any formula defining successor, or through `successor L`.

## Main results

* `Cslib.Logic.FO.Ordered.realize_succ`, `Cslib.Logic.FO.Ordered.isAtomic_succ`,
  `Cslib.Logic.FO.Ordered.isQF_succ`: the atom means `s + 1 = t` and is atomic.
* `Cslib.Logic.FO.Ordered.realize_successor`: the `≤` formula defines non-wrapping successor.
* `Cslib.Logic.FO.Ordered.realize_succInclusion`: the inclusion preserves truth.
* `Cslib.Logic.FO.Ordered.realize_elimSuccWith`, `Cslib.Logic.FO.Ordered.realize_elimSucc`:
  elimination preserves truth.

## References

* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  footnote 1 (the logical relations `=`, `≤`, successor, `BIT` and the constants `0`, `max`, for
  `n > 1`) and Definition 3.3 (quantifier-free interpretations exclude `BIT`).
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32 and Exercise 1.33(2).
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- The successor relation symbol. -/
inductive SuccRelation : ℕ → Type
  /-- `succ x y` means `y = x + 1`. -/
  | succ : SuccRelation 2
  deriving DecidableEq

/-- The relational vocabulary with only the successor symbol. -/
abbrev succSymbols : Language where
  Functions _ := Empty
  Relations := SuccRelation

/-- Canonical non-wrapping successor on `Fin n`: `succ x y` holds when `y = x + 1`. -/
instance succStructure {n : ℕ} : succSymbols.Structure (Fin n) where
  RelMap r x := match r with
    | .succ => (x 0).val + 1 = (x 1).val

/-- An input vocabulary extended by the successor symbol. Its ordered expansion
`language (succLanguage L)` has the input symbols, successor and the canonical numeric symbols. -/
abbrev succLanguage (L : Language) : Language := L.sum succSymbols

variable (L : Language) {α : Type*}

/-- The successor atom on arbitrary terms: `succ L s t` means `s + 1 = t`. -/
def succ (s t : (language (succLanguage L)).Term α) :
    (language (succLanguage L)).Formula α :=
  Relations.formula₂ ((LHom.sumInl : succLanguage L →ᴸ language (succLanguage L)).onRelation
    ((LHom.sumInr : succSymbols →ᴸ succLanguage L).onRelation .succ)) s t

/-- The successor atom is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_succ (s t : (language (succLanguage L)).Term α) : (succ L s t).IsAtomic :=
  BoundedFormula.IsAtomic.rel _ _

/-- The successor atom is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_succ (s t : (language (succLanguage L)).Term α) : (succ L s t).IsQF :=
  (isAtomic_succ L s t).isQF

/-- The ordered vocabulary is a sublanguage of the ordered vocabulary with successor. -/
abbrev succInclusion : language L →ᴸ language (succLanguage L) :=
  LHom.sumMap LHom.sumInl (LHom.id _)

/-- Successor in the canonical `≤` vocabulary: strict order with no intermediate point.
The formula universally quantifies one element; it is not quantifier-free. -/
noncomputable def successor : (language L).Formula (Fin 2) :=
  (le L (.var 1) (.var 0)).not ⊓ Formula.iAlls Unit
    ((le L (.var (.inr ())) (.var (.inl 0))).not.imp
      (le L (.var (.inl 1)) (.var (.inr ()))))

variable {L}

/-- Function symbols of the ordered vocabulary with successor, as terms of the ordered
vocabulary; successor adds no function symbols. -/
private def elimSuccFunctions :
    ∀ {n : ℕ}, (language (succLanguage L)).Functions n → (language L).Term (Fin n)
  | _, .inl (.inl f) => Functions.term (Sum.inl f : (language L).Functions _)
  | _, .inl (.inr f) => Empty.elim f
  | _, .inr f => Functions.term (Sum.inr f : (language L).Functions _)

/-- Relation symbols of the ordered vocabulary with successor, as formulas of the ordered
vocabulary: successor becomes `σ`, every other symbol itself. -/
private def elimSuccRelations (σ : (language L).Formula (Fin 2)) :
    ∀ {n : ℕ}, (language (succLanguage L)).Relations n → (language L).Formula (Fin n)
  | _, .inl (.inl R) => Relations.formula (Sum.inl R : (language L).Relations _) fun i => .var i
  | _, .inl (.inr .succ) => σ
  | _, .inr R => Relations.formula (Sum.inr R : (language L).Relations _) fun i => .var i

/-- Replace every successor atom `succ s t` by the formula `σ` applied to `s` and `t`, keeping
all other symbols. -/
noncomputable def elimSuccWith (σ : (language L).Formula (Fin 2)) {k : ℕ} :
    (language (succLanguage L)).BoundedFormula α k → (language L).BoundedFormula α k :=
  unfoldSymbols elimSuccFunctions (elimSuccRelations σ)

/-- Replace every successor atom `succ s t` by `successor L` applied to `s` and `t`. -/
noncomputable def elimSucc {k : ℕ} :
    (language (succLanguage L)).BoundedFormula α k → (language L).BoundedFormula α k :=
  elimSuccWith (successor L)

variable {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- On `Fin n` with `2 ≤ n`, the `≤` formula defines ordinary, non-wrapping successor. -/
@[simp, fo_realize]
theorem realize_successor (v : Fin 2 → Fin n) :
    (successor L).Realize v ↔ (v 1).val = (v 0).val + 1 := by
  fo_simp [successor, not_le]
  constructor
  · rintro ⟨h, hi⟩
    have h' : (v 0).val < (v 1).val := h
    let c : Fin n := ⟨(v 0).val + 1, by have := (v 1).isLt; lia⟩
    have hc := hi (fun _ => c) (by change (v 0).val < (v 0).val + 1; lia)
    change (v 1).val ≤ (v 0).val + 1 at hc
    lia
  · intro h
    refine ⟨by change (v 0).val < (v 1).val; lia, fun z hz => ?_⟩
    change (v 0).val < (z ()).val at hz
    change (v 1).val ≤ (z ()).val
    lia

/-- On `Fin n` with `2 ≤ n`, `succ L s t` holds exactly when `s + 1 = t`. -/
@[simp, fo_realize]
theorem realize_succ (s t : (language (succLanguage L)).Term α) (v : α → Fin n) :
    (succ L s t).Realize v ↔ (s.realize v).val + 1 = (t.realize v).val := by
  rw [succ, Formula.realize_rel₂]
  rfl

/-- On `Fin n` with `2 ≤ n`, the inclusion of the ordered vocabulary preserves truth. -/
@[simp]
theorem realize_succInclusion (φ : (language L).Formula α) (v : α → Fin n) :
    ((succInclusion L).onFormula φ).Realize v ↔ φ.Realize v :=
  LHom.realize_onFormula _ _

/-- **Successor elimination preserves truth** on `Fin n` with `2 ≤ n`, for every formula `σ`
that defines non-wrapping successor there. -/
theorem realize_elimSuccWith {σ : (language L).Formula (Fin 2)}
    (hσ : ∀ v : Fin 2 → Fin n, σ.Realize v ↔ (v 1).val = (v 0).val + 1) {k : ℕ}
    (φ : (language (succLanguage L)).BoundedFormula α k) (v : α → Fin n) (xs : Fin k → Fin n) :
    (elimSuccWith σ φ).Realize v xs ↔ φ.Realize v xs := by
  refine realize_unfoldSymbols (fun f x => ?_) (fun R x => ?_) φ v xs
  · rcases f with (f | f) | f
    · rfl
    · exact Empty.elim f
    · rfl
  · rcases R with (R | R) | R
    · exact Formula.realize_rel
    · cases R
      exact (hσ x).trans eq_comm
    · exact Formula.realize_rel

/-- Successor elimination through `σ` preserves the truth of formulas, under the hypotheses of
`Cslib.Logic.FO.Ordered.realize_elimSuccWith`. -/
theorem realize_elimSuccWith_formula {σ : (language L).Formula (Fin 2)}
    (hσ : ∀ v : Fin 2 → Fin n, σ.Realize v ↔ (v 1).val = (v 0).val + 1)
    (φ : (language (succLanguage L)).Formula α) (v : α → Fin n) :
    Formula.Realize (elimSuccWith σ φ) v ↔ φ.Realize v :=
  realize_elimSuccWith hσ φ v default

/-- **Successor elimination through `successor L` preserves truth** on `Fin n` with
`2 ≤ n`. -/
theorem realize_elimSucc {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula α k)
    (v : α → Fin n) (xs : Fin k → Fin n) : (elimSucc φ).Realize v xs ↔ φ.Realize v xs :=
  realize_elimSuccWith realize_successor φ v xs

/-- Successor elimination through `successor L` preserves the truth of formulas on `Fin n` with
`2 ≤ n`. -/
@[simp, fo_realize]
theorem realize_elimSucc_formula (φ : (language (succLanguage L)).Formula α) (v : α → Fin n) :
    Formula.Realize (elimSucc φ) v ↔ φ.Realize v :=
  realize_elimSucc φ v default

end Cslib.Logic.FO.Ordered
