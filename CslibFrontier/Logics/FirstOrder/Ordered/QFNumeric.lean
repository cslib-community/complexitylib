/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Successor
import CslibFrontier.Tactic.FirstOrder

/-!
# The numeric vocabulary of quantifier-free projections

Immerman and Landau's quantifier-free interpretations and projections may test the logical
relations `=`, `≤` and successor and the constants `0` and `max`, but not `BIT`: `BIT` on
`k`-tuples cannot easily be replaced by a quantifier-free formula, while successor, order and
the constants can. `qfNumericLanguage` is this vocabulary: `endpointOrderLanguage` (the constants
`0` and `max` and the relation `≤`) together with the successor symbol of
`Cslib.Logic.FO.Ordered.succSymbols`. It has no `BIT` and no constant `1`; `x = 1` is the atom
`succ 0 x`.

On `Fin n` with `2 ≤ n`, each symbol has its canonical meaning, with non-wrapping successor.
`toNumeric` translates formulas into the canonical numeric vocabulary `numericLanguage`,
preserving truth. It replaces each successor atom by `Ordered.successor`, which has a universal
quantifier, so the image of a quantifier-free formula need not be quantifier-free.

## Main definitions

* `Cslib.Logic.FO.Ordered.endpointOrderLanguage`, `Cslib.Logic.FO.Ordered.endpointOrderHom`: the
  constants `0`, `max` and the relation `≤`, and their inclusion into `numericLanguage`.
* `Cslib.Logic.FO.Ordered.qfNumericLanguage`: Immerman and Landau's numeric vocabulary without
  `BIT`.
* `Cslib.Logic.FO.Ordered.QFNumeric.zero`, `Cslib.Logic.FO.Ordered.QFNumeric.max`,
  `Cslib.Logic.FO.Ordered.QFNumeric.le`, `Cslib.Logic.FO.Ordered.QFNumeric.succ`: its terms and
  atoms.
* `Cslib.Logic.FO.Ordered.toNumeric`: translation into `numericLanguage`.

## Main results

* `Cslib.Logic.FO.Ordered.QFNumeric.realize_le`, `Cslib.Logic.FO.Ordered.QFNumeric.realize_succ`:
  the canonical meaning of the atoms.
* `Cslib.Logic.FO.Ordered.realize_toNumeric`: translation preserves truth on `Fin n`, `2 ≤ n`.

## References

* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  footnote 1 (the logical relations and constants), Definition 3.3 and the remark after it
  (quantifier-free interpretations omit `BIT`), and Definition 3.6.
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- The endpoint constants of the quantifier-free numeric vocabulary. -/
inductive EndpointFunction : ℕ → Type
  /-- The least element. -/
  | zero : EndpointFunction 0
  /-- The greatest element. -/
  | max : EndpointFunction 0
  deriving DecidableEq

/-- The order relation of the quantifier-free numeric vocabulary. -/
inductive EndpointRelation : ℕ → Type
  /-- The weak order. -/
  | le : EndpointRelation 2
  deriving DecidableEq

/-- The constants `0` and `max` and the relation `≤`. -/
abbrev endpointOrderLanguage : Language where
  Functions := EndpointFunction
  Relations := EndpointRelation

/-- Immerman and Landau's numeric vocabulary for quantifier-free interpretations and projections:
`≤`, successor, `0` and `max`, without `BIT`. -/
abbrev qfNumericLanguage : Language := endpointOrderLanguage.sum succSymbols

/-- Each endpoint symbol is the numeric symbol of the same name. -/
def endpointOrderHom : endpointOrderLanguage →ᴸ numericLanguage where
  onFunction {_} f := match f with
    | .zero => .zero
    | .max => .max
  onRelation {_} R := match R with
    | .le => .le

/-- The canonical endpoint structure on `Fin n`: the reduct of the canonical numeric structure. -/
instance endpointOrderStructure {n : ℕ} [Fact (2 ≤ n)] :
    endpointOrderLanguage.Structure (Fin n) :=
  endpointOrderHom.reduct (Fin n)

namespace QFNumeric

variable {α : Type*}

/-- The least element, as a term. -/
def zero : qfNumericLanguage.Term α :=
  .func ((LHom.sumInl : endpointOrderLanguage →ᴸ qfNumericLanguage).onFunction .zero) Fin.elim0

/-- The greatest element, as a term. -/
def max : qfNumericLanguage.Term α :=
  .func ((LHom.sumInl : endpointOrderLanguage →ᴸ qfNumericLanguage).onFunction .max) Fin.elim0

/-- The weak order on terms. -/
def le (s t : qfNumericLanguage.Term α) : qfNumericLanguage.Formula α :=
  Relations.formula₂ ((LHom.sumInl : endpointOrderLanguage →ᴸ qfNumericLanguage).onRelation .le)
    s t

/-- Non-wrapping successor on terms: `succ s t` means `s + 1 = t`. -/
def succ (s t : qfNumericLanguage.Term α) : qfNumericLanguage.Formula α :=
  Relations.formula₂ ((LHom.sumInr : succSymbols →ᴸ qfNumericLanguage).onRelation .succ) s t

/-- The order atom is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_le (s t : qfNumericLanguage.Term α) : (le s t).IsAtomic :=
  BoundedFormula.IsAtomic.rel _ _

/-- The successor atom is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_succ (s t : qfNumericLanguage.Term α) : (succ s t).IsAtomic :=
  BoundedFormula.IsAtomic.rel _ _

variable {n : ℕ} [Fact (2 ≤ n)]

/-- `zero` evaluates to `0 : Fin n`. -/
@[simp] theorem realize_zero_val (v : α → Fin n) :
    ((zero : qfNumericLanguage.Term α).realize v).val = 0 := by
  rw [zero]
  rfl

/-- `max` evaluates to `n - 1 : Fin n`. -/
@[simp] theorem realize_max_val (v : α → Fin n) :
    ((max : qfNumericLanguage.Term α).realize v).val = n - 1 := by
  rw [max]
  rfl

/-- `le s t` holds when `s ≤ t`. -/
@[simp, fo_realize]
theorem realize_le (s t : qfNumericLanguage.Term α) (v : α → Fin n) :
    (le s t).Realize v ↔ s.realize v ≤ t.realize v := by
  rw [le, Formula.realize_rel₂]
  rfl

/-- `succ s t` holds when `s + 1 = t`; the greatest element has no successor. -/
@[simp, fo_realize]
theorem realize_succ (s t : qfNumericLanguage.Term α) (v : α → Fin n) :
    (succ s t).Realize v ↔ (s.realize v).val + 1 = (t.realize v).val := by
  rw [succ, Formula.realize_rel₂]
  rfl

end QFNumeric

/-- `Ordered.successor` over the canonical numeric vocabulary. -/
noncomputable def numericSuccessor : numericLanguage.Formula (Fin 2) :=
  (LHom.sumElim (LHom.ofIsEmpty Language.empty numericLanguage) (LHom.id _)).onFormula
    (successor Language.empty)

/-- On `Fin n` with `2 ≤ n`, `numericSuccessor` defines non-wrapping successor. -/
theorem realize_numericSuccessor {n : ℕ} [Fact (2 ≤ n)] (v : Fin 2 → Fin n) :
    numericSuccessor.Realize v ↔ (v 1).val = (v 0).val + 1 := by
  let : Language.empty.Structure (Fin n) := Language.emptyStructure
  rw [numericSuccessor, LHom.realize_onFormula, realize_successor]

/-- The function symbols of `qfNumericLanguage`, as numeric terms. -/
private def toNumericFunctions :
    ∀ {m : ℕ}, qfNumericLanguage.Functions m → numericLanguage.Term (Fin m)
  | _, .inl f => Functions.term (endpointOrderHom.onFunction f)
  | _, .inr f => Empty.elim f

/-- The relation symbols of `qfNumericLanguage`, as numeric formulas. -/
private noncomputable def toNumericRelations :
    ∀ {m : ℕ}, qfNumericLanguage.Relations m → numericLanguage.Formula (Fin m)
  | _, .inl R => Relations.formula (endpointOrderHom.onRelation R) fun i => .var i
  | _, .inr .succ => numericSuccessor

/-- Translate into the canonical numeric vocabulary, replacing each successor atom by
`numericSuccessor`. -/
noncomputable def toNumeric {α : Type*} {k : ℕ} :
    qfNumericLanguage.BoundedFormula α k → numericLanguage.BoundedFormula α k :=
  unfoldSymbols toNumericFunctions toNumericRelations

variable {α : Type*} {n : ℕ} [Fact (2 ≤ n)]

/-- **Translation into the canonical numeric vocabulary preserves truth** on `Fin n` with
`2 ≤ n`. -/
theorem realize_toNumeric {k : ℕ} (φ : qfNumericLanguage.BoundedFormula α k) (v : α → Fin n)
    (xs : Fin k → Fin n) : (toNumeric φ).Realize v xs ↔ φ.Realize v xs := by
  refine realize_unfoldSymbols (fun f x => ?_) (fun R x => ?_) φ v xs
  · rcases f with f | f
    · rfl
    · exact Empty.elim f
  · rcases R with R | R
    · exact Formula.realize_rel
    · cases R
      exact (realize_numericSuccessor x).trans eq_comm

/-- Translation into the canonical numeric vocabulary preserves the truth of formulas. -/
@[simp, fo_realize]
theorem realize_toNumeric_formula (φ : qfNumericLanguage.Formula α) (v : α → Fin n) :
    Formula.Realize (toNumeric φ) v ↔ φ.Realize v :=
  realize_toNumeric φ v default

end Cslib.Logic.FO.Ordered
