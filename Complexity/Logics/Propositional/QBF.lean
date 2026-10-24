/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Logic.Operators
public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Quantified Boolean formulas

Quantified Boolean formulas over an arbitrary type `V` of variables: variables, the two constants,
negation, conjunction, disjunction, and quantifiers `∃ v` and `∀ v` over the truth value of a
variable [Stockmeyer and Meyer][StockmeyerMeyer1973]. `QBF.eval σ φ` is the truth value of `φ`
under the assignment `σ`; a quantifier over `v` evaluates its body with `v` set to each of the two
truth values (`Function.update`).

The value of a formula depends only on its free variables (`QBF.eval_congr`), so a closed formula,
one without free variables, has the same value under every assignment (`QBF.eval_eq_of_closed`).
The true closed formulas form the problem `TQBF` (`Cslib.Complexity.TQBF`), which is proved
`PSPACE`-complete in `Complexity.Computability.Complexity.Classes.Space.TQBF`
(`Cslib.Complexity.TQBF_pspaceComplete`) [Arora and Barak, Section 4.2][AroraBarak09].

cslib's `Cslib.Logic.PL.Proposition` has no quantifiers and is a syntax for proof systems rather
than an evaluated one, so it is not reused. `QBF V` instantiates cslib's logical operator
typeclasses (`Top`, `Bot`, `Cslib.Logic.HasNot`, `Cslib.Logic.HasAnd`, `Cslib.Logic.HasOr`,
`Cslib.Logic.HasImp`, `Cslib.Logic.HasIff`), so that `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, `↔`, and `⋀`
are available on `QBF V` when `Cslib.Logic` is open.

## Main definitions

* `Cslib.Logic.PL.QBF`: the formulas, with `Top`, `Bot`, `HasNot`, `HasAnd`, `HasOr`, `HasImp`, and
  `HasIff` instances.
* `Cslib.Logic.PL.QBF.eval`: the value of a formula under an assignment.
* `Cslib.Logic.PL.QBF.freeVars`, `Cslib.Logic.PL.QBF.Closed`.
* `Cslib.Logic.PL.QBF.vars`, `Cslib.Logic.PL.QBF.size`: the variables, free or bound, and the number
  of nodes.
* `Cslib.Logic.PL.QBF.exs`, `Cslib.Logic.PL.QBF.alls`, `Cslib.Logic.PL.QBF.conj`,
  `Cslib.Logic.PL.QBF.imp`, `Cslib.Logic.PL.QBF.iff`, `Cslib.Logic.PL.QBF.lit`: derived
  connectives, blocks of quantifiers and conjunctions of lists (`QBF.conj_eq_finiteAnd`).
* `Cslib.Logic.PL.QBF.ofClause`, `Cslib.Logic.PL.QBF.ofCNF`: clauses and formulas in conjunctive
  normal form as quantified Boolean formulas.

## Main results

* `Cslib.Logic.PL.QBF.eval_ex_eq_true_iff`, `Cslib.Logic.PL.QBF.eval_all_eq_true_iff`: the
  quantifiers as `∃` and `∀` over a truth value.
* `Cslib.Logic.PL.QBF.eval_congr`: the value depends only on the free variables.
* `Cslib.Logic.PL.QBF.eval_eq_of_closed`: a closed formula has the same value under every
  assignment.
* `Cslib.Logic.PL.QBF.eval_not_ex`, `Cslib.Logic.PL.QBF.eval_not_all`: De Morgan's laws for the
  quantifiers.
* `Cslib.Logic.PL.QBF.eval_exs_eq_true_iff`, `Cslib.Logic.PL.QBF.eval_alls_eq_true_iff`: blocks
  of quantifiers range over the assignments that agree outside the block.
* `Cslib.Logic.PL.QBF.eval_ofCNF`, `Cslib.Logic.PL.QBF.mem_freeVars_ofCNF`: formulas in
  conjunctive normal form keep their value and their variables.

## References

* [L. Stockmeyer, A. Meyer, *Word problems requiring exponential time*][StockmeyerMeyer1973]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- Quantified Boolean formulas over variables of type `V`. -/
inductive QBF (V : Type*) where
  /-- The variable `v`. -/
  | var (v : V)
  /-- The constant true. -/
  | top
  /-- The constant false. -/
  | bot
  /-- Negation. -/
  | not (φ : QBF V)
  /-- Conjunction. -/
  | and (φ ψ : QBF V)
  /-- Disjunction. -/
  | or (φ ψ : QBF V)
  /-- Existential quantification `∃ v, φ` over the truth value of `v`. -/
  | ex (v : V) (φ : QBF V)
  /-- Universal quantification `∀ v, φ` over the truth value of `v`. -/
  | all (v : V) (φ : QBF V)
  deriving DecidableEq

namespace QBF

variable {V : Type*} [DecidableEq V]

/-! ### Evaluation -/

/-- The value of a formula under the assignment `σ`. A quantifier over `v` evaluates its body
with `v` set to `false` and to `true`, and takes the disjunction (`ex`) or the conjunction (`all`)
of the two values. -/
def eval (σ : V → Bool) : QBF V → Bool
  | .var v => σ v
  | .top => true
  | .bot => false
  | .not φ => !eval σ φ
  | .and φ ψ => eval σ φ && eval σ ψ
  | .or φ ψ => eval σ φ || eval σ ψ
  | .ex v φ => eval (Function.update σ v false) φ || eval (Function.update σ v true) φ
  | .all v φ => eval (Function.update σ v false) φ && eval (Function.update σ v true) φ

variable (σ : V → Bool) (v : V) (φ ψ : QBF V)

/-- Evaluating a variable `var v` under `σ` yields `σ v`. -/
@[simp] theorem eval_var : (var v).eval σ = σ v := rfl

/-- The constant `top` evaluates to `true`. -/
@[simp] theorem eval_top : (top : QBF V).eval σ = true := rfl

/-- The constant `bot` evaluates to `false`. -/
@[simp] theorem eval_bot : (bot : QBF V).eval σ = false := rfl

/-- Evaluating `φ.not` negates the truth value of `φ`. -/
@[simp] theorem eval_not : φ.not.eval σ = !φ.eval σ := rfl

/-- Evaluating `φ.and ψ` takes the Boolean conjunction of `φ.eval σ` and `ψ.eval σ`. -/
@[simp] theorem eval_and : (φ.and ψ).eval σ = (φ.eval σ && ψ.eval σ) := rfl

/-- Evaluating `φ.or ψ` takes the Boolean disjunction of `φ.eval σ` and `ψ.eval σ`. -/
@[simp] theorem eval_or : (φ.or ψ).eval σ = (φ.eval σ || ψ.eval σ) := rfl

/-- Evaluating `ex v φ` takes the disjunction of `φ` with `v` set to `false` and to `true`. -/
@[simp] theorem eval_ex :
    (ex v φ).eval σ = (φ.eval (Function.update σ v false) || φ.eval (Function.update σ v true)) :=
  rfl

/-- Evaluating `all v φ` takes the conjunction of `φ` with `v` set to `false` and to `true`. -/
@[simp] theorem eval_all :
    (all v φ).eval σ = (φ.eval (Function.update σ v false) && φ.eval (Function.update σ v true)) :=
  rfl

/-- `∃ v, φ` is true when `φ` is true for some value of `v`. -/
theorem eval_ex_eq_true_iff :
    (ex v φ).eval σ = true ↔ ∃ b, φ.eval (Function.update σ v b) = true := by
  rw [Bool.exists_bool, eval_ex, Bool.or_eq_true]

/-- `∀ v, φ` is true when `φ` is true for every value of `v`. -/
theorem eval_all_eq_true_iff :
    (all v φ).eval σ = true ↔ ∀ b, φ.eval (Function.update σ v b) = true := by
  rw [Bool.forall_bool, eval_all, Bool.and_eq_true]

/-- De Morgan's law for `∃`: `¬∃ v, φ` and `∀ v, ¬φ` have the same value. -/
theorem eval_not_ex : (ex v φ).not.eval σ = (all v φ.not).eval σ := by
  simp only [eval_not, eval_ex, eval_all, Bool.not_or]

/-- De Morgan's law for `∀`: `¬∀ v, φ` and `∃ v, ¬φ` have the same value. -/
theorem eval_not_all : (all v φ).not.eval σ = (ex v φ.not).eval σ := by
  simp only [eval_not, eval_ex, eval_all, Bool.not_and]

/-! ### Free variables -/

/-- The free variables of a formula: the variables with an occurrence outside the scope of every
quantifier over them. -/
def freeVars : QBF V → Finset V
  | .var v => {v}
  | .top => ∅
  | .bot => ∅
  | .not φ => freeVars φ
  | .and φ ψ => freeVars φ ∪ freeVars ψ
  | .or φ ψ => freeVars φ ∪ freeVars ψ
  | .ex v φ => (freeVars φ).erase v
  | .all v φ => (freeVars φ).erase v

/-- The free variables of `var v` are `{v}`. -/
@[simp] theorem freeVars_var : (var v).freeVars = {v} := rfl

/-- The constant `top` has no free variables. -/
@[simp] theorem freeVars_top : (top : QBF V).freeVars = ∅ := rfl

/-- The constant `bot` has no free variables. -/
@[simp] theorem freeVars_bot : (bot : QBF V).freeVars = ∅ := rfl

/-- Negation preserves the set of free variables. -/
@[simp] theorem freeVars_not : φ.not.freeVars = φ.freeVars := rfl

/-- The free variables of `φ.and ψ` are the union of those of `φ` and `ψ`. -/
@[simp] theorem freeVars_and : (φ.and ψ).freeVars = φ.freeVars ∪ ψ.freeVars := rfl

/-- The free variables of `φ.or ψ` are the union of those of `φ` and `ψ`. -/
@[simp] theorem freeVars_or : (φ.or ψ).freeVars = φ.freeVars ∪ ψ.freeVars := rfl

/-- Existential quantification over `v` removes `v` from the free variables of `φ`. -/
@[simp] theorem freeVars_ex : (ex v φ).freeVars = φ.freeVars.erase v := rfl

/-- Universal quantification over `v` removes `v` from the free variables of `φ`. -/
@[simp] theorem freeVars_all : (all v φ).freeVars = φ.freeVars.erase v := rfl

variable {σ v φ}

/-- Two assignments that agree on the free variables of `φ`, updated at the same variable, agree
on the free variables of the body of a quantifier over that variable. -/
private theorem update_eq_update {τ : V → Bool} (h : ∀ w ∈ (ex v φ).freeVars, σ w = τ w) (b : Bool)
    (w : V) (hw : w ∈ φ.freeVars) : Function.update σ v b w = Function.update τ v b w := by
  by_cases hwv : w = v
  · subst hwv
    simp only [Function.update_self]
  · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]
    exact h w (Finset.mem_erase.2 ⟨hwv, hw⟩)

/-- **Agreement on free variables.** The value of a formula depends only on the values of its free
variables. -/
theorem eval_congr {τ : V → Bool} (h : ∀ w ∈ φ.freeVars, σ w = τ w) : φ.eval σ = φ.eval τ := by
  induction φ generalizing σ τ with
  | var v => exact h v (Finset.mem_singleton_self v)
  | top => rfl
  | bot => rfl
  | not φ ih => rw [eval_not, eval_not, ih h]
  | and φ ψ ihφ ihψ =>
    rw [eval_and, eval_and, ihφ fun w hw => h w (Finset.mem_union_left _ hw),
      ihψ fun w hw => h w (Finset.mem_union_right _ hw)]
  | or φ ψ ihφ ihψ =>
    rw [eval_or, eval_or, ihφ fun w hw => h w (Finset.mem_union_left _ hw),
      ihψ fun w hw => h w (Finset.mem_union_right _ hw)]
  | ex v φ ih =>
    rw [eval_ex, eval_ex, ih (update_eq_update h false), ih (update_eq_update h true)]
  | all v φ ih =>
    rw [eval_all, eval_all, ih (update_eq_update h false), ih (update_eq_update h true)]

/-- Updating a variable that is not free does not change the value of a formula. -/
theorem eval_update_of_notMem_freeVars (hv : v ∉ φ.freeVars) (σ : V → Bool) (b : Bool) :
    φ.eval (Function.update σ v b) = φ.eval σ :=
  eval_congr fun _ hw => Function.update_of_ne (ne_of_mem_of_not_mem hw hv) _ _

/-- A quantifier `∃ v` over a variable that is not free in its body can be dropped. -/
theorem eval_ex_of_notMem_freeVars (hv : v ∉ φ.freeVars) (σ : V → Bool) :
    (ex v φ).eval σ = φ.eval σ := by
  rw [eval_ex, eval_update_of_notMem_freeVars hv, eval_update_of_notMem_freeVars hv, Bool.or_self]

/-- A quantifier `∀ v` over a variable that is not free in its body can be dropped. -/
theorem eval_all_of_notMem_freeVars (hv : v ∉ φ.freeVars) (σ : V → Bool) :
    (all v φ).eval σ = φ.eval σ := by
  rw [eval_all, eval_update_of_notMem_freeVars hv, eval_update_of_notMem_freeVars hv,
    Bool.and_self]

/-! ### Variables and size -/

/-- The variables of a formula, free or bound, with multiplicity, in prefix order. -/
def vars : QBF V → List V
  | .var v => [v]
  | .top => []
  | .bot => []
  | .not φ => vars φ
  | .and φ ψ => vars φ ++ vars ψ
  | .or φ ψ => vars φ ++ vars ψ
  | .ex v φ => v :: vars φ
  | .all v φ => v :: vars φ

/-- The number of nodes of a formula. -/
def size : QBF V → ℕ
  | .var _ => 1
  | .top => 1
  | .bot => 1
  | .not φ => size φ + 1
  | .and φ ψ => size φ + size ψ + 1
  | .or φ ψ => size φ + size ψ + 1
  | .ex _ φ => size φ + 1
  | .all _ φ => size φ + 1

omit [DecidableEq V] in
/-- Every formula has size at least `1`. -/
theorem one_le_size (φ : QBF V) : 1 ≤ φ.size := by
  cases φ <;> simp only [size] <;> omega

omit [DecidableEq V] in
/-- The number of variable occurrences in `φ` is at most `φ.size`. -/
theorem length_vars_le_size (φ : QBF V) : φ.vars.length ≤ φ.size := by
  induction φ <;>
    simp only [vars, size, List.length_nil, List.length_append, List.length_cons] <;>
    omega

/-! ### Closed formulas -/

/-- A formula is closed when it has no free variables. -/
def Closed (φ : QBF V) : Prop := φ.freeVars = ∅

/-- Being closed is decidable when variable equality is decidable. -/
instance : DecidablePred (Closed (V := V)) := fun φ => inferInstanceAs (Decidable (φ.freeVars = ∅))

/-- A closed formula has the same value under every assignment. -/
theorem eval_eq_of_closed (hφ : φ.Closed) (σ τ : V → Bool) : φ.eval σ = φ.eval τ :=
  eval_congr fun w hw => absurd (hφ ▸ hw) (Finset.notMem_empty w)

/-- A negated formula `φ.not` is closed if and only if `φ` is closed. -/
theorem closed_not : φ.not.Closed ↔ φ.Closed := Iff.rfl

/-- A conjunction `φ.and ψ` is closed if and only if both `φ` and `ψ` are closed. -/
theorem closed_and : (φ.and ψ).Closed ↔ φ.Closed ∧ ψ.Closed := Finset.union_eq_empty

/-- A disjunction `φ.or ψ` is closed if and only if both `φ` and `ψ` are closed. -/
theorem closed_or : (φ.or ψ).Closed ↔ φ.Closed ∧ ψ.Closed := Finset.union_eq_empty

end QBF

namespace QBF

/-! ### Derived connectives -/

variable {V : Type*}

/-- Existential quantification over each variable of a list, the first one outermost. -/
def exs (vs : List V) (φ : QBF V) : QBF V := vs.foldr ex φ

/-- Universal quantification over each variable of a list, the first one outermost. -/
def alls (vs : List V) (φ : QBF V) : QBF V := vs.foldr all φ

/-- The conjunction of a list of formulas, `top` for the empty list. -/
def conj (l : List (QBF V)) : QBF V := l.foldr and top

/-- Implication. -/
def imp (φ ψ : QBF V) : QBF V := or (not φ) ψ

/-- Equivalence. -/
def iff (φ ψ : QBF V) : QBF V := or (and φ ψ) (and (not φ) (not ψ))

/-- `⊤` on `QBF V` is `QBF.top`. -/
instance : Top (QBF V) := ⟨.top⟩
/-- `⊥` on `QBF V` is `QBF.bot`. -/
instance : Bot (QBF V) := ⟨.bot⟩
/-- `¬` on `QBF V` is `QBF.not`. -/
instance : HasNot (QBF V) := ⟨.not⟩
/-- `∧` on `QBF V` is `QBF.and`. -/
instance : HasAnd (QBF V) := ⟨.and⟩
/-- `∨` on `QBF V` is `QBF.or`. -/
instance : HasOr (QBF V) := ⟨.or⟩
/-- `→` on `QBF V` is `QBF.imp`. -/
instance : HasImp (QBF V) := ⟨.imp⟩
/-- `↔` on `QBF V` is `QBF.iff`. -/
instance : HasIff (QBF V) := ⟨.iff⟩

/-- `QBF.conj` agrees with `Cslib.Logic.finiteAnd` (`⋀`). -/
theorem conj_eq_finiteAnd (φs : List (QBF V)) : conj φs = ⋀φs := rfl

/-- The literal of `v` with sign `b`: `v` itself for `true`, its negation for `false`. -/
def lit (v : V) (b : Bool) : QBF V := if b then var v else not (var v)

/-- A clause as the disjunction of its literals, `bot` for the empty clause. -/
def ofClause (c : Clause V) : QBF V := c.foldr (fun l φ => or (lit l.1 l.2) φ) bot

/-- A formula in conjunctive normal form as the conjunction of its clauses, `top` for the empty
formula. -/
def ofCNF (φ : CNF V) : QBF V := φ.foldr (fun c ψ => and (ofClause c) ψ) top

/-- Existential quantification over `vs ++ ws` is existential quantification over `vs` followed by
`ws`. -/
theorem exs_append (vs ws : List V) (φ : QBF V) : exs (vs ++ ws) φ = exs vs (exs ws φ) :=
  List.foldr_append

/-- Universal quantification over `vs ++ ws` is universal quantification over `vs` followed by
`ws`. -/
theorem alls_append (vs ws : List V) (φ : QBF V) : alls (vs ++ ws) φ = alls vs (alls ws φ) :=
  List.foldr_append

variable [DecidableEq V] (σ : V → Bool)

/-- **A block of existential quantifiers** ranges over the assignments that agree with the given
one outside the block. -/
theorem eval_exs_eq_true_iff (vs : List V) (φ : QBF V) :
    (exs vs φ).eval σ = true ↔ ∃ τ, (∀ x ∉ vs, τ x = σ x) ∧ φ.eval τ = true := by
  induction vs generalizing σ with
  | nil => exact ⟨fun h => ⟨σ, fun _ _ => rfl, h⟩, fun ⟨τ, hτ, h⟩ =>
      (funext fun x => hτ x (List.not_mem_nil)) ▸ h⟩
  | cons v vs ih =>
    simp only [exs, List.foldr_cons] at ih ⊢
    rw [eval_ex_eq_true_iff]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨τ, hτ, h⟩ := (ih _).mp hb
      refine ⟨τ, fun x hx => ?_, h⟩
      rw [hτ x fun h => hx (List.mem_cons_of_mem _ h),
        Function.update_of_ne fun h => hx (by simp [h])]
    · rintro ⟨τ, hτ, h⟩
      refine ⟨τ v, (ih _).mpr ⟨τ, fun x hx => ?_, h⟩⟩
      by_cases hxv : x = v
      · subst hxv
        simp
      · rw [Function.update_of_ne hxv]
        exact hτ x (by simp [hxv, hx])

/-- **A block of universal quantifiers** ranges over the assignments that agree with the given one
outside the block. -/
theorem eval_alls_eq_true_iff (vs : List V) (φ : QBF V) :
    (alls vs φ).eval σ = true ↔ ∀ τ, (∀ x ∉ vs, τ x = σ x) → φ.eval τ = true := by
  induction vs generalizing σ with
  | nil => exact ⟨fun h τ hτ => (funext fun x => hτ x (List.not_mem_nil)) ▸ h,
      fun h => h σ fun _ _ => rfl⟩
  | cons v vs ih =>
    simp only [alls, List.foldr_cons] at ih ⊢
    rw [eval_all_eq_true_iff]
    constructor
    · intro h τ hτ
      refine (ih _).mp (h (τ v)) τ fun x hx => ?_
      by_cases hxv : x = v
      · subst hxv
        simp
      · rw [Function.update_of_ne hxv]
        exact hτ x (by simp [hxv, hx])
    · intro h b
      refine (ih _).mpr fun τ hτ => h τ fun x hx => ?_
      rw [hτ x fun h => hx (List.mem_cons_of_mem _ h),
        Function.update_of_ne fun h => hx (by simp [h])]

/-- The conjunction of a list `l` evaluates to `true` iff every formula in `l` evaluates to
`true`. -/
@[simp] theorem eval_conj (l : List (QBF V)) : (conj l).eval σ = l.all (·.eval σ) := by
  induction l with
  | nil => rfl
  | cons φ l ih =>
    change (φ.and (conj l)).eval σ = _
    simp [ih]

/-- Evaluating `imp φ ψ` computes Boolean implication `!φ.eval σ || ψ.eval σ`. -/
@[simp] theorem eval_imp (φ ψ : QBF V) : (imp φ ψ).eval σ = (!φ.eval σ || ψ.eval σ) := rfl

/-- Evaluating `iff φ ψ` computes Boolean equivalence `φ.eval σ == ψ.eval σ`. -/
@[simp] theorem eval_iff (φ ψ : QBF V) : (iff φ ψ).eval σ = (φ.eval σ == ψ.eval σ) := by
  simp only [iff, eval_or, eval_and, eval_not]
  cases φ.eval σ <;> cases ψ.eval σ <;> rfl

/-- A literal `lit v b` evaluates to `true` iff `σ v` equals `b`. -/
@[simp] theorem eval_lit (v : V) (b : Bool) : (lit v b).eval σ = (σ v == b) := by
  cases b <;> simp only [lit, eval_var, eval_not, Bool.false_eq_true, ite_false, ite_true] <;>
    cases σ v <;> rfl

/-- Embedding a clause via `ofClause` preserves its truth value under `σ`. -/
@[simp] theorem eval_ofClause (c : Clause V) : (ofClause c).eval σ = Clause.eval σ c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    change ((lit l.1 l.2).or (ofClause c)).eval σ = _
    simp [ih, Literal.eval]

/-- **A formula in conjunctive normal form keeps its value.** -/
@[simp] theorem eval_ofCNF (φ : CNF V) : (ofCNF φ).eval σ = CNF.eval σ φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change ((ofClause c).and (ofCNF φ)).eval σ = _
    simp [ih]

/-! ### Free variables of the derived connectives -/

/-- Quantifying existentially over `vs` removes `vs.toFinset` from the free variables of `φ`. -/
theorem freeVars_exs (vs : List V) (φ : QBF V) :
    (exs vs φ).freeVars = φ.freeVars \ vs.toFinset := by
  induction vs with
  | nil => simp [exs]
  | cons v vs ih =>
    simp only [exs, List.foldr_cons] at ih ⊢
    rw [freeVars_ex, ih, List.toFinset_cons]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto

/-- Quantifying universally over `vs` removes `vs.toFinset` from the free variables of `φ`. -/
theorem freeVars_alls (vs : List V) (φ : QBF V) :
    (alls vs φ).freeVars = φ.freeVars \ vs.toFinset := by
  induction vs with
  | nil => simp [alls]
  | cons v vs ih =>
    simp only [alls, List.foldr_cons] at ih ⊢
    rw [freeVars_all, ih, List.toFinset_cons]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto

/-- A variable is free in `conj l` if and only if it is free in some formula of `l`. -/
theorem mem_freeVars_conj {l : List (QBF V)} {x : V} :
    x ∈ (conj l).freeVars ↔ ∃ φ ∈ l, x ∈ φ.freeVars := by
  induction l with
  | nil => simp [conj]
  | cons φ l ih =>
    change x ∈ (φ.and (conj l)).freeVars ↔ _
    simp [ih]

/-- The free variables of `imp φ ψ` are the union of those of `φ` and `ψ`. -/
@[simp] theorem freeVars_imp (φ ψ : QBF V) : (imp φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := rfl

/-- The free variables of `iff φ ψ` are the union of those of `φ` and `ψ`. -/
@[simp] theorem freeVars_iff (φ ψ : QBF V) : (iff φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  ext x
  simp only [iff, freeVars_or, freeVars_and, freeVars_not, Finset.mem_union]
  tauto

/-- The only free variable of `lit v b` is `v`. -/
@[simp] theorem freeVars_lit (v : V) (b : Bool) : (lit v b).freeVars = {v} := by
  cases b <;> rfl

/-- The free variables of `ofCNF φ` are the variables occurring in `φ`. -/
theorem mem_freeVars_ofCNF {x : V} {φ : CNF V} : x ∈ (ofCNF φ).freeVars ↔ x ∈ φ.vars := by
  have hc (c : Clause V) : x ∈ (ofClause c).freeVars ↔ ∃ l ∈ c, l.1 = x := by
    induction c with
    | nil => simp [ofClause]
    | cons l c ih =>
      change x ∈ ((lit l.1 l.2).or (ofClause c)).freeVars ↔ _
      rw [freeVars_or, Finset.mem_union, ih, freeVars_lit, Finset.mem_singleton]
      simp [eq_comm]
  induction φ with
  | nil => simp [ofCNF, CNF.vars]
  | cons c φ ih =>
    change x ∈ ((ofClause c).and (ofCNF φ)).freeVars ↔ _
    simp only [freeVars_and, Finset.mem_union, ih, hc]
    simp [CNF.vars]

end QBF

end Cslib.Logic.PL
