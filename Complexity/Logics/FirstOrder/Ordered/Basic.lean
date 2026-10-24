/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Basic
public import Mathlib.Data.Nat.Bits

/-!
# Canonical ordered first-order structures

The numeric vocabulary contains `≤`, `BIT`, and the constants `0`, `1`, and `max`. On `Fin n`,
with `2 ≤ n`, these have their canonical meanings computed from the natural indices. In
`BIT(x, i)`, bit zero is the least significant bit. The numeric tables are not additional input.
An input language is expanded by Mathlib's `Language.sum`; its existing functions, constants and
relations retain their interpretations. Formulas and terms are Mathlib's existing syntax, so
numeric constants can occur directly in relation arguments, equalities and quantified formulas.

This is the canonical-structure prerequisite for ordered descriptive complexity. Native full-tuple
BIT and canonical full-tuple interpretations are supplied in `Ordered.TupleBit` and
`Ordered.FullTuple`; their composition is in `Ordered.FullTuple.Composition`.
Machine and circuit capture theorems require separate developments.

## Main definitions

* `Cslib.Logic.FO.Ordered.NumericFunction`, `Cslib.Logic.FO.Ordered.NumericFunction.index`,
  `Cslib.Logic.FO.Ordered.NumericRelation`, `Cslib.Logic.FO.Ordered.numericLanguage`: the numeric
  function and relation symbols and their language.
* `Cslib.Logic.FO.Ordered.language`: expansion of an input language by the numeric vocabulary.
* `Cslib.Logic.FO.Ordered.numericStructure`: canonical numeric semantics on `Fin n`, for `n ≥ 2`.
* `Cslib.Logic.FO.Ordered.zero`, `Cslib.Logic.FO.Ordered.one`, `Cslib.Logic.FO.Ordered.max`:
  numeric constant terms in the expanded language.
* `Cslib.Logic.FO.Ordered.le`, `Cslib.Logic.FO.Ordered.bit`: numeric atoms on arbitrary terms.

## Main results

* `Cslib.Logic.FO.Ordered.realize_bit`: exact zero-indexed BIT semantics.
* `Cslib.Logic.FO.Ordered.realize_zero_ne_one`: the numeric constants are distinct.
* `Cslib.Logic.FO.Ordered.realize_inputFormula`: expansion preserves all input formulas.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 1.2 and Provisos 1.14–1.15.
  This minimal vocabulary includes order and BIT; no equivalence with addition/multiplication
  is asserted.
* Earlier canonical-expansion interfaces in [S. Schlesinger, *Canonical numerical predicates
  in Complexitylib*][Schlesinger2026Numerical] informed this native Mathlib formulation.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- The numeric function symbols are constants only. -/
inductive NumericFunction : ℕ → Type
  /-- The least element. -/
  | zero : NumericFunction 0
  /-- The element with natural index one. -/
  | one : NumericFunction 0
  /-- The greatest element. -/
  | max : NumericFunction 0
  deriving DecidableEq

/-- Finite enumeration of the nullary numeric function symbols `zero`, `one`, and `max`. -/
instance : Fintype (NumericFunction 0) :=
  ⟨{.zero, .one, .max}, by intro c; cases c <;> simp⟩

/-- The natural index of a canonical numeric constant in a universe of size `m`. -/
abbrev NumericFunction.index {k : ℕ} (c : NumericFunction k) (m : ℕ) : ℕ :=
  match c with
  | .zero => 0
  | .one => 1
  | .max => m - 1

/-- When `2 ≤ m`, the natural index `c.index m` of any numeric constant is strictly less than
`m`. -/
theorem NumericFunction.index_lt {k m : ℕ} (hm : 2 ≤ m) (c : NumericFunction k) :
    c.index m < m := by
  cases c <;> simp only [NumericFunction.index] <;> lia

/-- Canonical order and zero-indexed binary digits. -/
inductive NumericRelation : ℕ → Type
  /-- Weak natural order. -/
  | le : NumericRelation 2
  /-- `bit x i` tests the bit of weight `2^i` in `x`. -/
  | bit : NumericRelation 2
  deriving DecidableEq

/-- The canonical numeric vocabulary, including genuine nullary function symbols. -/
abbrev numericLanguage : Language where
  Functions := NumericFunction
  Relations := NumericRelation

/-- Preserve input symbols and adjoin the canonical numeric vocabulary. -/
abbrev language (L : Language) : Language := L.sum numericLanguage

/-- Canonical numeric semantics; the lower bound makes zero and one distinct elements. -/
@[instance_reducible]
def numericStructure {n : ℕ} (hn : 2 ≤ n) : numericLanguage.Structure (Fin n) where
  funMap f _ := ⟨f.index n, f.index_lt hn⟩
  RelMap r x := match r with
    | .le => x 0 ≤ x 1
    | .bit => (x 0).val.testBit (x 1).val = true

/-- Canonical `numericLanguage.Structure (Fin n)` instance when `Fact (2 ≤ n)` holds. -/
instance {n : ℕ} [Fact (2 ≤ n)] : numericLanguage.Structure (Fin n) :=
  numericStructure Fact.out

variable (L : Language) {α : Type*}

/-- The numeric zero, as an ordinary Mathlib constant term. -/
def zero : (language L).Term α :=
  .func ((LHom.sumInr : numericLanguage →ᴸ language L).onFunction .zero) Fin.elim0

/-- The numeric one, as an ordinary Mathlib constant term. -/
def one : (language L).Term α :=
  .func ((LHom.sumInr : numericLanguage →ᴸ language L).onFunction .one) Fin.elim0

/-- The greatest element, as an ordinary Mathlib constant term. -/
def max : (language L).Term α :=
  .func ((LHom.sumInr : numericLanguage →ᴸ language L).onFunction .max) Fin.elim0

/-- Canonical weak order applied to arbitrary terms, including constants. -/
def le (s t : (language L).Term α) : (language L).Formula α :=
  Relations.formula₂ ((LHom.sumInr : numericLanguage →ᴸ language L).onRelation .le) s t

/-- Canonical BIT applied to arbitrary terms; the second argument is the zero-based bit index. -/
def bit (s i : (language L).Term α) : (language L).Formula α :=
  Relations.formula₂ ((LHom.sumInr : numericLanguage →ᴸ language L).onRelation .bit) s i

variable {L} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The numeric constant `zero L` evaluates to `0 : Fin n`. -/
@[simp] theorem realize_zero_val (v : α → Fin n) :
    ((zero L).realize v).val = 0 := rfl

/-- The numeric constant `one L` evaluates to `1 : Fin n`. -/
@[simp] theorem realize_one_val (v : α → Fin n) :
    ((one L).realize v).val = 1 := rfl

/-- The numeric constant `max L` evaluates to `n - 1 : Fin n`. -/
@[simp] theorem realize_max_val (v : α → Fin n) :
    ((max L).realize v).val = n - 1 := rfl

/-- The numeric constants are distinct in every canonical expanded structure. -/
theorem realize_zero_ne_one (v : α → Fin n) : (zero L).realize v ≠ (one L).realize v := by
  intro h
  have := congrArg Fin.val h
  simp only [realize_zero_val, realize_one_val] at this
  contradiction

/-- `le L s t` holds under `v` if and only if `s.realize v ≤ t.realize v`. -/
@[simp, fo_realize] theorem realize_le (s t : (language L).Term α) (v : α → Fin n) :
    (le L s t).Realize v ↔ s.realize v ≤ t.realize v := by
  rw [le, Formula.realize_rel₂]
  rfl

/-- `bit L s i` holds exactly when bit `i` of `s` is set, counting from the least significant
bit. -/
@[simp, fo_realize] theorem realize_bit (s i : (language L).Term α) (v : α → Fin n) :
    (bit L s i).Realize v ↔ (s.realize v).val.testBit (i.realize v).val = true := by
  rw [bit, Formula.realize_rel₂]
  rfl

/-- The language inclusion preserves the truth of every input formula, including constants
and quantifiers already present in the input language. -/
theorem realize_inputFormula (φ : L.Formula α) (v : α → Fin n) :
    ((LHom.sumInl : L →ᴸ language L).onFormula φ).Realize v ↔ φ.Realize v :=
  LHom.realize_onFormula _ _

end Cslib.Logic.FO.Ordered
