/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.ModelTheory.Semantics

/-!
# Unfolding defined symbols

A language `L` is often extended by symbols that are definable in `L`. For example, successor can
be added to an ordered vocabulary as a primitive relation. `Cslib.Logic.FO.unfoldSymbols`
translates formulas of the extended language back into `L`. Each function symbol is replaced by
a term of `L` and each relation symbol by a formula of `L`; variables, connectives and
quantifiers are unchanged. A symbol that `L` already has is replaced by itself, applied to its
argument variables. If every replacement defines its symbol in a structure `M`, the translation
preserves truth in `M` (`Cslib.Logic.FO.realize_unfoldSymbols`).

The definitions may use quantifiers, so the translation of a quantifier-free formula need not
be quantifier-free. Function symbols are replaced with Mathlib's `Term.substFunc`.

`Cslib.Logic.FO.Interpretation.onFormula` also replaces each relation symbol by a formula. It
interprets a relational language on tuples cut out by a domain formula, so it changes the
universe and handles no function symbols. Here the universe stays the same and the language may
keep its constants and functions.

## Main definitions

* `Cslib.Logic.FO.unfoldSymbols`: replace each symbol by its definition.

## Main results

* `Cslib.Logic.FO.realize_unfoldSymbols`, `Cslib.Logic.FO.realize_unfoldSymbols_formula`: the
  translation preserves truth in every structure where the definitions hold.
-/

public section

universe u v u' v'

namespace Cslib.Logic.FO

open FirstOrder Language Structure

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {α : Type*}

/-- Replace each function symbol of `L` by a term of `L'` and each relation symbol of `L` by a
formula of `L'` in the argument variables. Variables, connectives and quantifiers are kept. -/
noncomputable def unfoldSymbols (tf : ∀ {n : ℕ}, L.Functions n → L'.Term (Fin n))
    (rf : ∀ {n : ℕ}, L.Relations n → L'.Formula (Fin n)) :
    ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | _, .falsum => .falsum
  | _, .equal s t => .equal (s.substFunc tf) (t.substFunc tf)
  | _, .rel R ts => ((rf R).subst fun i => (ts i).substFunc tf).relabel id
  | _, .imp φ ψ => .imp (unfoldSymbols tf rf φ) (unfoldSymbols tf rf ψ)
  | _, .all φ => .all (unfoldSymbols tf rf φ)

variable {M : Type*} [L.Structure M] [L'.Structure M]
  {tf : ∀ {n : ℕ}, L.Functions n → L'.Term (Fin n)}
  {rf : ∀ {n : ℕ}, L.Relations n → L'.Formula (Fin n)}

/-- **Unfolding preserves truth.** If each function symbol of `L` agrees in `M` with its
replacement term and each relation symbol with its replacement formula, then a bounded formula
and its translation hold under the same assignments. -/
theorem realize_unfoldSymbols
    (htf : ∀ {n : ℕ} (f : L.Functions n) (x : Fin n → M), (tf f).realize x = funMap f x)
    (hrf : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → M), (rf R).Realize x ↔ RelMap R x)
    {k : ℕ} (φ : L.BoundedFormula α k) (v : α → M) (xs : Fin k → M) :
    (unfoldSymbols tf rf φ).Realize v xs ↔ φ.Realize v xs := by
  have hc : ∀ {n : ℕ} (g : L.Functions n) (y : Fin n → M), g.term.realize y = (tf g).realize y :=
    fun g y => (htf g y).symm
  induction φ with
  | falsum => rfl
  | equal s t =>
    simp only [unfoldSymbols, BoundedFormula.Realize, Term.realize_substFunc hc]
  | @rel k l R ts =>
    have h0 : xs ∘ (Fin.natAdd k : Fin 0 → Fin (k + 0)) = default := Subsingleton.elim _ _
    have h1 : Sum.elim v (xs ∘ Fin.castAdd 0) ∘ id = Sum.elim v xs := rfl
    rw [unfoldSymbols, BoundedFormula.realize_relabel, h0, h1, BoundedFormula.realize_subst]
    refine (hrf R _).trans ?_
    simp only [Term.realize_substFunc hc]
    rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ xs) (ihψ xs)
  | all φ ih => exact forall_congr' fun x => ih (Fin.snoc xs x)

/-- **Unfolding preserves the truth of formulas**, under the hypotheses of
`Cslib.Logic.FO.realize_unfoldSymbols`. -/
theorem realize_unfoldSymbols_formula
    (htf : ∀ {n : ℕ} (f : L.Functions n) (x : Fin n → M), (tf f).realize x = funMap f x)
    (hrf : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → M), (rf R).Realize x ↔ RelMap R x)
    (φ : L.Formula α) (v : α → M) :
    Formula.Realize (unfoldSymbols tf rf φ) v ↔ φ.Realize v :=
  realize_unfoldSymbols htf hrf φ v default

end Cslib.Logic.FO
