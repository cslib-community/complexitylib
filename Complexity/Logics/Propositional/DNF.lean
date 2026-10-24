/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF

/-!
# Disjunctive normal form

Formulas in disjunctive normal form over a type of variables `V`, dual to the conjunctive normal
form of `Cslib.Logic.PL.CNF`. A term is a list of literals read conjunctively, and a formula is a
list of terms read disjunctively. Negating every literal turns a term into a clause and a formula
in disjunctive normal form into the negation of a formula in conjunctive normal form
(`DNF.eval_negate`).

## Main definitions

* `Cslib.Logic.PL.Term`, `Cslib.Logic.PL.DNF`, `Cslib.Logic.PL.Term.eval`,
  `Cslib.Logic.PL.DNF.eval`.
* `Cslib.Logic.PL.Term.negate`, `Cslib.Logic.PL.Clause.negate`, `Cslib.Logic.PL.DNF.negate`,
  `Cslib.Logic.PL.CNF.negate`: the negation, in the dual normal form.

## Main results

* `Cslib.Logic.PL.DNF.eval_eq_true_iff`, `Cslib.Logic.PL.Term.eval_eq_true_iff`: the semantics as
  quantifiers over terms and literals.
* `Cslib.Logic.PL.DNF.eval_negate`: de Morgan duality.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- A term is a conjunction of literals. -/
abbrev Term (V : Type*) : Type _ := List (Literal V)

/-- A formula in disjunctive normal form is a disjunction of terms. -/
abbrev DNF (V : Type*) : Type _ := List (Term V)

/-- A term holds when all of its literals do. -/
def Term.eval (σ : V → Bool) (t : Term V) : Bool := t.all (Literal.eval σ)

/-- A formula holds when one of its terms does. -/
def DNF.eval (σ : V → Bool) (φ : DNF V) : Bool := φ.any (Term.eval σ)

/-- A term holds when every literal does. -/
theorem Term.eval_eq_true_iff (σ : V → Bool) (t : Term V) :
    t.eval σ = true ↔ ∀ l ∈ t, σ l.1 = l.2 := by
  simp [Term.eval, Literal.eval]

/-- Flipping a variable that a term does not mention does not change its value. -/
theorem Term.eval_update_of_forall_ne [DecidableEq V] {t : Term V} {i : V}
    (hi : ∀ l ∈ t, l.1 ≠ i) (x : V → Bool) (b : Bool) :
    t.eval (Function.update x i b) = t.eval x := by
  rw [Bool.eq_iff_iff, Term.eval_eq_true_iff, Term.eval_eq_true_iff]
  exact forall₂_congr fun l hl => by rw [Function.update_of_ne (hi l hl)]

/-- Evaluating the empty term yields `true`. -/
@[simp] theorem Term.eval_nil (σ : V → Bool) : Term.eval σ [] = true := rfl

/-- Evaluating a `cons` term conjoins the head literal with the tail term. -/
@[simp] theorem Term.eval_cons (σ : V → Bool) (l : Literal V) (t : Term V) :
    Term.eval σ (l :: t) = (Literal.eval σ l && Term.eval σ t) := rfl

/-- A formula holds when some term does. -/
theorem DNF.eval_eq_true_iff (σ : V → Bool) (φ : DNF V) :
    φ.eval σ = true ↔ ∃ t ∈ φ, t.eval σ = true := by
  simp [DNF.eval]

/-- Evaluating the empty DNF formula yields `false`. -/
@[simp] theorem DNF.eval_nil (σ : V → Bool) : DNF.eval σ [] = false := rfl

/-- Evaluating the concatenation of two DNF formulas disjoins their values. -/
@[simp] theorem DNF.eval_append (σ : V → Bool) (φ ψ : DNF V) :
    DNF.eval σ (φ ++ ψ) = (DNF.eval σ φ || DNF.eval σ ψ) := by
  simp [DNF.eval, List.any_append]

/-- Evaluating a `cons` DNF formula disjoins the head term with the tail formula. -/
@[simp] theorem DNF.eval_cons (σ : V → Bool) (t : Term V) (φ : DNF V) :
    DNF.eval σ (t :: φ) = (Term.eval σ t || DNF.eval σ φ) := rfl

/-- The clause of the negated literals of a term. -/
def Term.negate (t : Term V) : Clause V :=
  t.map fun l => (l.1, !l.2)

/-- Evaluating the negated clause of a term `t` negates `t.eval σ`. -/
@[simp] theorem Term.eval_negate (σ : V → Bool) (t : Term V) :
    Clause.eval σ t.negate = !t.eval σ := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    simp only [Term.negate, List.map_cons, Clause.eval_cons, Term.eval_cons] at ih ⊢
    rw [ih, Bool.not_and]
    congr 1
    simp only [Literal.eval]
    cases σ l.1 <;> cases l.2 <;> rfl

/-- The formula in conjunctive normal form of the negation of a formula in disjunctive normal
form. -/
def DNF.negate (φ : DNF V) : CNF V :=
  φ.map Term.negate

/-- **De Morgan duality.** -/
@[simp] theorem DNF.eval_negate (σ : V → Bool) (φ : DNF V) :
    CNF.eval σ φ.negate = !φ.eval σ := by
  induction φ with
  | nil => rfl
  | cons t φ ih =>
    simp only [DNF.negate, List.map_cons, CNF.eval_cons, DNF.eval_cons] at ih ⊢
    rw [ih, Term.eval_negate, Bool.not_or]

/-- The term of the negated literals of a clause. -/
def Clause.negate (c : Clause V) : Term V :=
  c.map fun l => (l.1, !l.2)

/-- Evaluating the negated term of a clause `c` negates `c.eval σ`. -/
@[simp] theorem Clause.eval_negate (σ : V → Bool) (c : Clause V) :
    Term.eval σ c.negate = !c.eval σ := by
  have h := Term.eval_negate σ (Clause.negate c)
  have hc : (Clause.negate c).negate = c := by
    simp only [Clause.negate, Term.negate, List.map_map]
    conv_rhs => rw [← List.map_id c]
    congr 1
    funext l
    simp
  rw [hc] at h
  rw [h, Bool.not_not]

/-- Negating a clause preserves its length. -/
@[simp] theorem Clause.length_negate (c : Clause V) : c.negate.length = c.length :=
  List.length_map _

/-- Negating a clause preserves its list of underlying variables. -/
theorem Clause.map_fst_negate (c : Clause V) : c.negate.map Prod.fst = c.map Prod.fst := by
  simp [Clause.negate]

/-- The formula in disjunctive normal form of the negation of a formula in conjunctive normal
form. -/
def CNF.negate (φ : CNF V) : DNF V :=
  φ.map Clause.negate

/-- **De Morgan duality**, from conjunctive to disjunctive normal form. -/
@[simp] theorem CNF.eval_negate (σ : V → Bool) (φ : CNF V) :
    DNF.eval σ φ.negate = !φ.eval σ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [CNF.negate, List.map_cons, DNF.eval_cons, CNF.eval_cons] at ih ⊢
    rw [ih, Clause.eval_negate, Bool.not_and]

end Cslib.Logic.PL
