/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.QuantifierRank
public import Mathlib.Data.Fintype.Basic
public import Mathlib.ModelTheory.Semantics
import CslibFrontier.Foundations.Data.List.FoldrForall

/-!
# Finite-variable first-order logic

The `k`-variable fragment `FO^k` of first-order logic consists of the formulas that use at most `k`
distinct variable names, each of which may be quantified again inside its own scope. Reusing names
gives these formulas more power than their number of variables suggests: on linear orders, a
formula with two variables can say that there are at least `n` elements, for every `n`
([Libkin2004], formula (11.4)).

Mathlib's `FirstOrder.Language.BoundedFormula` gives every quantifier a fresh de Bruijn index, so
it cannot say that two quantifiers bind the same variable. This file therefore introduces a small
dedicated syntax `Cslib.Logic.FO.FiniteVariable.Formula L k` whose variables are `Fin k`; the
quantifier `all i φ` rebinds the variable `i`. Its semantics updates the assignment
`a : Fin k → M` at `i`. The translation `Formula.toFormula` into Mathlib's `L.Formula (Fin k)`
preserves truth (`Formula.realize_toFormula`) and quantifier rank
(`Formula.quantifierRank_toFormula`), so `FO^k` is a fragment of ordinary first-order logic.

As in [Libkin2004] and [Immerman1999], the vocabulary is relational: atomic formulas are equations
between variables and relation symbols applied to variables. Function and constant symbols of `L`
are simply not used, so the language need not be relational.

## Main definitions

* `Cslib.Logic.FO.FiniteVariable.Formula`: formulas of `FO^k` over the relation symbols of `L`.
* `Cslib.Logic.FO.FiniteVariable.Formula.Realize`: truth under an assignment `Fin k → M`.
* `Cslib.Logic.FO.FiniteVariable.Formula.quantifierRank`,
  `Cslib.Logic.FO.FiniteVariable.Formula.freeVars`: quantifier rank and free variables.
* `Cslib.Logic.FO.FiniteVariable.Formula.not`, `Cslib.Logic.FO.FiniteVariable.Formula.ex`,
  `Cslib.Logic.FO.FiniteVariable.Formula.iInf`, `Cslib.Logic.FO.FiniteVariable.Formula.iSup`:
  derived connectives, including finite conjunctions and disjunctions.
* `Cslib.Logic.FO.FiniteVariable.Formula.toFormula`: the translation to Mathlib's formulas.

## Main results

* `Cslib.Logic.FO.FiniteVariable.Formula.realize_congr`: truth depends only on the values of the
  free variables.
* `Cslib.Logic.FO.FiniteVariable.Formula.realize_toFormula`,
  `Cslib.Logic.FO.FiniteVariable.Formula.quantifierRank_toFormula`: the translation preserves truth
  and quantifier rank.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 11.1, Definition 11.1.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 6.9.
-/

public section

universe u v w

open FirstOrder Language Structure

namespace Cslib.Logic.FO.FiniteVariable

variable (L : Language.{u, v}) (k : ℕ)

/-- Formulas of the `k`-variable fragment `FO^k` over the relation symbols of `L`. The variables
are `Fin k`, and `all i φ` quantifies the variable `i`, which may already be bound or free in an
enclosing formula. -/
inductive Formula : Type v
  /-- Falsity. -/
  | falsum : Formula
  /-- The equation `xᵢ = xⱼ`. -/
  | equal (i j : Fin k) : Formula
  /-- The relation `R` applied to the variables `x_{f 0}, …, x_{f (l - 1)}`. -/
  | rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) : Formula
  /-- Implication. -/
  | imp (φ ψ : Formula) : Formula
  /-- Universal quantification of the variable `xᵢ`. -/
  | all (i : Fin k) (φ : Formula) : Formula

variable {L k}

namespace Formula

/-- Negation. -/
def not (φ : Formula L k) : Formula L k :=
  imp φ falsum

/-- Existential quantification of the variable `xᵢ`. -/
def ex (i : Fin k) (φ : Formula L k) : Formula L k :=
  (all i φ.not).not

instance : Bot (Formula L k) :=
  ⟨falsum⟩

instance : Top (Formula L k) :=
  ⟨falsum.not⟩

instance : Min (Formula L k) :=
  ⟨fun φ ψ => (φ.imp ψ.not).not⟩

instance : Max (Formula L k) :=
  ⟨fun φ ψ => φ.not.imp ψ⟩

/-- The conjunction of a finite family of formulas. Like Mathlib's
`FirstOrder.Language.BoundedFormula.iInf`, it is defined through an arbitrary enumeration of the
index type, so only its truth, rank and free variables are determined. -/
noncomputable def iInf {β : Type*} [Finite β] (f : β → Formula L k) : Formula L k :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

/-- The disjunction of a finite family of formulas, as the negation of the conjunction of the
negations. -/
noncomputable def iSup {β : Type*} [Finite β] (f : β → Formula L k) : Formula L k :=
  (iInf fun b => (f b).not).not

/-! ### Semantics -/

/-- Truth of a formula in `M` under the assignment `a` of elements to the `k` variables. -/
def Realize {M : Type w} [L.Structure M] : Formula L k → (Fin k → M) → Prop
  | falsum, _ => False
  | equal i j, a => a i = a j
  | rel R f, a => RelMap R (a ∘ f)
  | imp φ ψ, a => φ.Realize a → ψ.Realize a
  | all i φ, a => ∀ c : M, φ.Realize (Function.update a i c)

variable {M : Type w} [L.Structure M]

@[simp] theorem realize_falsum (a : Fin k → M) : (falsum : Formula L k).Realize a ↔ False := by
  rw [Realize]

@[simp] theorem realize_equal (i j : Fin k) (a : Fin k → M) :
    (equal i j : Formula L k).Realize a ↔ a i = a j := by
  rw [Realize]

@[simp] theorem realize_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) (a : Fin k → M) :
    (rel R f).Realize a ↔ RelMap R (a ∘ f) := by
  rw [Realize]

@[simp] theorem realize_imp (φ ψ : Formula L k) (a : Fin k → M) :
    (imp φ ψ).Realize a ↔ (φ.Realize a → ψ.Realize a) := by
  rw [Realize]

@[simp] theorem realize_all (i : Fin k) (φ : Formula L k) (a : Fin k → M) :
    (all i φ).Realize a ↔ ∀ c : M, φ.Realize (Function.update a i c) := by
  rw [Realize]

@[simp] theorem realize_not (φ : Formula L k) (a : Fin k → M) :
    φ.not.Realize a ↔ ¬φ.Realize a := by
  rw [not, realize_imp, realize_falsum]

@[simp] theorem realize_ex (i : Fin k) (φ : Formula L k) (a : Fin k → M) :
    (ex i φ).Realize a ↔ ∃ c : M, φ.Realize (Function.update a i c) := by
  simp only [ex, realize_not, realize_all, not_forall, not_not]

@[simp] theorem realize_bot (a : Fin k → M) : (⊥ : Formula L k).Realize a ↔ False :=
  realize_falsum a

@[simp] theorem realize_top (a : Fin k → M) : (⊤ : Formula L k).Realize a ↔ True :=
  (realize_not _ a).trans (by simp only [realize_falsum, not_false_eq_true])

@[simp] theorem realize_inf (φ ψ : Formula L k) (a : Fin k → M) :
    (φ ⊓ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a := by
  change (φ.imp ψ.not).not.Realize a ↔ _
  simp only [realize_not, realize_imp, not_imp, not_not]

@[simp] theorem realize_sup (φ ψ : Formula L k) (a : Fin k → M) :
    (φ ⊔ ψ).Realize a ↔ φ.Realize a ∨ ψ.Realize a := by
  change (φ.not.imp ψ).Realize a ↔ _
  simp only [realize_imp, realize_not, or_iff_not_imp_left]

/-- A property of formulas that holds of `⊤` and distributes over `⊓` holds of a finite
conjunction exactly when it holds of every conjunct. -/
private theorem apply_iInf_iff {β : Type*} [Finite β] {p : Formula L k → Prop}
    (hinf : ∀ φ ψ, p (φ ⊓ ψ) ↔ p φ ∧ p ψ) (htop : p ⊤) (f : β → Formula L k) :
    p (iInf f) ↔ ∀ b, p (f b) := by
  let := Fintype.ofFinite β
  exact List.apply_foldr_map_univ_toList_iff hinf htop f

@[simp] theorem realize_iInf {β : Type*} [Finite β] (f : β → Formula L k) (a : Fin k → M) :
    (iInf f).Realize a ↔ ∀ b, (f b).Realize a :=
  apply_iInf_iff (p := fun φ => φ.Realize a) (fun φ ψ => realize_inf φ ψ a)
    ((realize_top a).2 trivial) f

@[simp] theorem realize_iSup {β : Type*} [Finite β] (f : β → Formula L k) (a : Fin k → M) :
    (iSup f).Realize a ↔ ∃ b, (f b).Realize a := by
  simp only [iSup, realize_not, realize_iInf, not_forall, not_not]

/-! ### Quantifier rank -/

/-- The quantifier rank of a formula: the maximal nesting depth of its quantifiers. -/
def quantifierRank : Formula L k → ℕ
  | falsum => 0
  | equal _ _ => 0
  | rel _ _ => 0
  | imp φ ψ => max φ.quantifierRank ψ.quantifierRank
  | all _ φ => φ.quantifierRank + 1

@[simp] theorem quantifierRank_falsum : (falsum : Formula L k).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_equal (i j : Fin k) :
    (equal i j : Formula L k).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_imp (φ ψ : Formula L k) :
    (imp φ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_all (i : Fin k) (φ : Formula L k) :
    (all i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_not (φ : Formula L k) :
    φ.not.quantifierRank = φ.quantifierRank := by
  rw [not, quantifierRank_imp, quantifierRank_falsum, Nat.max_zero]

@[simp] theorem quantifierRank_ex (i : Fin k) (φ : Formula L k) :
    (ex i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [ex, quantifierRank_not, quantifierRank_all, quantifierRank_not]

@[simp] theorem quantifierRank_bot : (⊥ : Formula L k).quantifierRank = 0 :=
  quantifierRank_falsum

@[simp] theorem quantifierRank_top : (⊤ : Formula L k).quantifierRank = 0 :=
  (quantifierRank_not _).trans quantifierRank_falsum

@[simp] theorem quantifierRank_inf (φ ψ : Formula L k) :
    (φ ⊓ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  change (φ.imp ψ.not).not.quantifierRank = _
  rw [quantifierRank_not, quantifierRank_imp, quantifierRank_not]

@[simp] theorem quantifierRank_sup (φ ψ : Formula L k) :
    (φ ⊔ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  change (φ.not.imp ψ).quantifierRank = _
  rw [quantifierRank_imp, quantifierRank_not]

/-- A finite conjunction has quantifier rank at most `m` when each conjunct does. -/
theorem quantifierRank_iInf_le {β : Type*} [Finite β] {f : β → Formula L k} {m : ℕ}
    (h : ∀ b, (f b).quantifierRank ≤ m) : (iInf f).quantifierRank ≤ m :=
  (apply_iInf_iff (p := fun φ => φ.quantifierRank ≤ m)
    (fun φ ψ => by rw [quantifierRank_inf, max_le_iff])
    (quantifierRank_top.trans_le (Nat.zero_le m)) f).2 h

/-- A finite disjunction has quantifier rank at most `m` when each disjunct does. -/
theorem quantifierRank_iSup_le {β : Type*} [Finite β] {f : β → Formula L k} {m : ℕ}
    (h : ∀ b, (f b).quantifierRank ≤ m) : (iSup f).quantifierRank ≤ m := by
  rw [iSup, quantifierRank_not]
  exact quantifierRank_iInf_le fun b => (quantifierRank_not _).trans_le (h b)

/-! ### Free variables -/

/-- The free variables of a formula. -/
def freeVars : Formula L k → Finset (Fin k)
  | falsum => ∅
  | equal i j => {i, j}
  | rel _ f => Finset.univ.image f
  | imp φ ψ => φ.freeVars ∪ ψ.freeVars
  | all i φ => φ.freeVars.erase i

@[simp] theorem freeVars_falsum : (falsum : Formula L k).freeVars = ∅ := by
  rw [freeVars]

@[simp] theorem freeVars_equal (i j : Fin k) : (equal i j : Formula L k).freeVars = {i, j} := by
  rw [freeVars]

@[simp] theorem freeVars_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f).freeVars = Finset.univ.image f := by
  rw [freeVars]

@[simp] theorem freeVars_imp (φ ψ : Formula L k) :
    (imp φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  rw [freeVars]

@[simp] theorem freeVars_all (i : Fin k) (φ : Formula L k) :
    (all i φ).freeVars = φ.freeVars.erase i := by
  rw [freeVars]

@[simp] theorem freeVars_not (φ : Formula L k) : φ.not.freeVars = φ.freeVars := by
  rw [not, freeVars_imp, freeVars_falsum, Finset.union_empty]

@[simp] theorem freeVars_ex (i : Fin k) (φ : Formula L k) :
    (ex i φ).freeVars = φ.freeVars.erase i := by
  rw [ex, freeVars_not, freeVars_all, freeVars_not]

@[simp] theorem freeVars_bot : (⊥ : Formula L k).freeVars = ∅ :=
  freeVars_falsum

@[simp] theorem freeVars_top : (⊤ : Formula L k).freeVars = ∅ :=
  (freeVars_not _).trans freeVars_falsum

@[simp] theorem freeVars_inf (φ ψ : Formula L k) :
    (φ ⊓ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  change (φ.imp ψ.not).not.freeVars = _
  rw [freeVars_not, freeVars_imp, freeVars_not]

@[simp] theorem freeVars_sup (φ ψ : Formula L k) :
    (φ ⊔ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  change (φ.not.imp ψ).freeVars = _
  rw [freeVars_imp, freeVars_not]

/-- The free variables of a finite conjunction lie in `S` when those of each conjunct do. -/
theorem freeVars_iInf_subset {β : Type*} [Finite β] {f : β → Formula L k} {S : Set (Fin k)}
    (h : ∀ b, ↑(f b).freeVars ⊆ S) : ↑(iInf f).freeVars ⊆ S :=
  (apply_iInf_iff (p := fun φ => ↑φ.freeVars ⊆ S)
    (fun φ ψ => by rw [freeVars_inf, Finset.coe_union, Set.union_subset_iff])
    (by rw [freeVars_top, Finset.coe_empty]; exact Set.empty_subset S) f).2 h

/-- The free variables of a finite disjunction lie in `S` when those of each disjunct do. -/
theorem freeVars_iSup_subset {β : Type*} [Finite β] {f : β → Formula L k} {S : Set (Fin k)}
    (h : ∀ b, ↑(f b).freeVars ⊆ S) : ↑(iSup f).freeVars ⊆ S := by
  rw [iSup, freeVars_not]
  exact freeVars_iInf_subset fun b => (freeVars_not (f b)).symm ▸ h b

/-- The truth of a formula depends only on the values of its free variables. -/
theorem realize_congr {φ : Formula L k} {a a' : Fin k → M} (h : ∀ i ∈ φ.freeVars, a i = a' i) :
    φ.Realize a ↔ φ.Realize a' := by
  induction φ generalizing a a' with
  | falsum => exact Iff.rfl
  | equal i j =>
    simp only [freeVars_equal, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq] at h
    rw [realize_equal, realize_equal, h.1, h.2]
  | rel R f =>
    rw [realize_rel, realize_rel]
    have : a ∘ f = a' ∘ f := funext fun t => h _ (by simp)
    rw [this]
  | imp φ ψ ihφ ihψ =>
    simp only [freeVars_imp, Finset.mem_union] at h
    rw [realize_imp, realize_imp, ihφ fun i hi => h i (Or.inl hi),
      ihψ fun i hi => h i (Or.inr hi)]
  | all i φ ih =>
    simp only [freeVars_all, Finset.mem_erase] at h
    rw [realize_all, realize_all]
    refine forall_congr' fun c => ih fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji, h j ⟨hji, hj⟩]

/-! ### Translation to Mathlib's first-order formulas -/

/-- The translation of a formula of `FO^k` into Mathlib's `L.Formula (Fin k)`: the variable `i`
becomes the free variable `i`, and `all i φ` quantifies over a fresh bound variable which replaces
`i` in the translation of `φ`. -/
def toFormula : Formula L k → L.Formula (Fin k)
  | falsum => ⊥
  | equal i j => Term.equal (.var i) (.var j)
  | rel R f => R.formula fun t => .var (f t)
  | imp φ ψ => φ.toFormula.imp ψ.toFormula
  | all i φ =>
    (BoundedFormula.relabel (fun j : Fin k => if j = i then (Sum.inr 0 : Fin k ⊕ Fin 1) else
      Sum.inl j) φ.toFormula : L.BoundedFormula (Fin k) 1).all

private theorem toFormula_all_assignment (i : Fin k) (a : Fin k → M) (c : M) :
    Sum.elim a (((Fin.snoc (default : Fin 0 → M) c : Fin 1 → M)) ∘ Fin.castAdd 0) ∘
        (fun j : Fin k => if j = i then (Sum.inr 0 : Fin k ⊕ Fin 1) else Sum.inl j) =
      Function.update a i c := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.comp_apply, ite_eq_left, Sum.elim_inr, Function.update_self]
    rfl
  · simp only [Function.comp_apply, ite_eq_right hj, Sum.elim_inl, Function.update_of_ne hj]

/-- The translation of a formula holds of an assignment exactly when the formula does. -/
@[simp] theorem realize_toFormula (φ : Formula L k) (a : Fin k → M) :
    φ.toFormula.Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum => simp only [toFormula, Language.Formula.realize_bot, realize_falsum]
  | equal i j =>
    simp only [toFormula, Language.Formula.realize_equal, Term.realize_var, realize_equal]
  | rel R f =>
    simp only [toFormula, Language.Formula.realize_rel, Term.realize_var, realize_rel]
    rfl
  | imp φ ψ ihφ ihψ =>
    simp only [toFormula, Language.Formula.realize_imp, ihφ, ihψ, realize_imp]
  | all i φ ih =>
    rw [realize_all, toFormula, Language.Formula.Realize, BoundedFormula.realize_all]
    refine forall_congr' fun c => ?_
    rw [BoundedFormula.realize_relabel, toFormula_all_assignment, ← ih]
    exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- The translation preserves quantifier rank. -/
@[simp] theorem quantifierRank_toFormula (φ : Formula L k) :
    FO.quantifierRank φ.toFormula = φ.quantifierRank := by
  induction φ with
  | falsum => rw [toFormula, FO.quantifierRank_bot, quantifierRank_falsum]
  | equal i j => rw [toFormula, Term.equal, FO.quantifierRank_bdEqual, quantifierRank_equal]
  | rel R f =>
    rw [toFormula, Relations.formula, FO.quantifierRank_relations_boundedFormula,
      quantifierRank_rel]
  | imp φ ψ ihφ ihψ => rw [toFormula, FO.quantifierRank_imp, ihφ, ihψ, quantifierRank_imp]
  | all i φ ih =>
    rw [toFormula, FO.quantifierRank_all, FO.quantifierRank_relabel, ih, quantifierRank_all]

end Formula

end Cslib.Logic.FO.FiniteVariable
