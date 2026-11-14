/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.SQL.Row
public import CslibFrontier.Languages.SQL.Scalar

/-!
# Resolved SQL expressions

`Expr n` is a scalar SQL expression over a row of `n` columns: literals, typed `NULL`, column
references by position (`Expr.col i` with `i : Fin n`, so a reference to a missing column cannot be
written), the operators of `Cslib.SQL.Scalar`, `e IN (v₁, …, vₖ)` over a literal list, and
`CASE WHEN c THEN a ELSE b END`.

`Expr.eval r e` evaluates `e` on the row `r`. It is strict and goes from left to right: every
operand is evaluated, and the first error is the result. The one exception is `CASE`, which
evaluates only the branch it takes, so an error in the other branch is not raised. A `WHERE` or
`ON` predicate is read through `Expr.evalTruth`, which also rejects a non-boolean result.

Moving an expression across a scope boundary is explicit. `Expr.rename ρ` reindexes the columns,
and `Expr.subst σ` replaces column `i` by an expression `σ i`: evaluating a substituted expression
is evaluating the original on the row of results of `σ`, provided every `σ i` succeeds
(`Expr.eval_subst`). For joins, whose rows are `Fin.append`, `Expr.eval_rename_castAdd` and
`Expr.eval_rename_natAdd` evaluate an expression moved to the left or right side.

It adapts and redesigns the expressions of `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell.
There, column references were names looked up in rows at evaluation time, `NULL` literals carried
optional types, and the expression type held aggregates, subqueries and windows evaluated by
partial functions. Here references are resolved positions, the fragment is scalar, and evaluation
is structural and total.

## Main definitions

* `Cslib.SQL.Expr`: resolved scalar expressions over `n` columns.
* `Cslib.SQL.Expr.eval`: strict evaluation on a row; `Cslib.SQL.Expr.evalTruth` for predicates.
* `Cslib.SQL.Expr.rename`, `Cslib.SQL.Expr.subst`: renaming and substitution of columns.

## Main results

* `Cslib.SQL.Expr.eval_rename`: renaming is evaluation on the reindexed row.
* `Cslib.SQL.Expr.eval_subst`: substitution is evaluation on the row of substituted results.
* `Cslib.SQL.Expr.eval_rename_castAdd`, `Cslib.SQL.Expr.eval_rename_natAdd`: an expression moved
  into a join reads its own side of the joined row.
* `Cslib.SQL.Expr.toOption_eval_subst_congr`: substitutions with the same observations give
  expressions with the same observations.
-/

@[expose] public section

namespace Cslib.SQL

/-- A resolved scalar SQL expression over rows of `n` columns. -/
inductive Expr (n : ℕ) : Type where
  /-- A non-null literal. -/
  | lit (v : Value)
  /-- A `NULL` literal of type `τ`; the type matters only for typing. -/
  | null (τ : SqlType)
  /-- The `i`-th column of the row. -/
  | col (i : Fin n)
  /-- A unary operator. -/
  | unary (op : UnOp) (e : Expr n)
  /-- A binary operator. -/
  | binary (op : BinOp) (e₁ e₂ : Expr n)
  /-- `e IN (v₁, …, vₖ)` over a list of literals; `NULL` may occur in the list. -/
  | inList (e : Expr n) (vs : List Datum)
  /-- `CASE WHEN c THEN a ELSE b END`. -/
  | caseWhen (c a b : Expr n)
  deriving DecidableEq, Repr

namespace Expr

variable {n m k : ℕ}

/-- Evaluate an expression on a row: strict and left to right, except that `CASE` evaluates only
the branch it takes. -/
def eval (r : Row n) : Expr n → Except EvalError Datum
  | lit v => .ok (some v)
  | null _ => .ok none
  | col i => .ok (r i)
  | unary op e => do evalUnOp op (← e.eval r)
  | binary op e₁ e₂ => do evalBinOp op (← e₁.eval r) (← e₂.eval r)
  | inList e vs => do return Truth.toDatum (← (← e.eval r).inList vs)
  | caseWhen c a b => do
    if (← (← c.eval r).toTruth).isTrue then a.eval r else b.eval r

/-- Evaluate a predicate on a row, as `WHERE` and `ON` do: a non-boolean result is a type error,
and the row is kept exactly when the result is `Truth.true`. -/
def evalTruth (r : Row n) (e : Expr n) : Except EvalError Truth := do (← e.eval r).toTruth

section Eval

variable (r : Row n)

@[simp] theorem eval_lit (v : Value) : (lit v : Expr n).eval r = .ok (some v) := rfl

@[simp] theorem eval_null (τ : SqlType) : (null τ : Expr n).eval r = .ok none := rfl

@[simp] theorem eval_col (i : Fin n) : (col i).eval r = .ok (r i) := rfl

theorem eval_unary (op : UnOp) (e : Expr n) :
    (unary op e).eval r = (do evalUnOp op (← e.eval r)) := rfl

theorem eval_binary (op : BinOp) (e₁ e₂ : Expr n) :
    (binary op e₁ e₂).eval r = (do evalBinOp op (← e₁.eval r) (← e₂.eval r)) := rfl

theorem eval_inList (e : Expr n) (vs : List Datum) :
    (inList e vs).eval r = (do return Truth.toDatum (← (← e.eval r).inList vs)) := rfl

theorem eval_caseWhen (c a b : Expr n) :
    (caseWhen c a b).eval r =
      (do if (← (← c.eval r).toTruth).isTrue then a.eval r else b.eval r) := rfl

/-- `CASE` takes the `THEN` branch when the condition is `TRUE`, without evaluating `ELSE`. -/
theorem eval_caseWhen_of_true {c : Expr n} (hc : c.evalTruth r = .ok .true) (a b : Expr n) :
    (caseWhen c a b).eval r = a.eval r := by
  obtain ⟨d, hd, ht⟩ := Except.bind_eq_ok.mp hc
  simp only [eval_caseWhen, hd, ht, Except.ok_bind]
  rfl

/-- `CASE` takes the `ELSE` branch when the condition is `FALSE` or `unknown`, without evaluating
`THEN`. -/
theorem eval_caseWhen_of_ne_true {c : Expr n} {t : Truth} (hc : c.evalTruth r = .ok t)
    (ht : t ≠ .true) (a b : Expr n) : (caseWhen c a b).eval r = b.eval r := by
  obtain ⟨d, hd, hdt⟩ := Except.bind_eq_ok.mp hc
  simp only [eval_caseWhen, hd, hdt, Except.ok_bind]
  cases t <;> first | rfl | exact absurd rfl ht

end Eval

/-! ### Renaming and substitution -/

/-- Reindex the columns of an expression along `ρ`. -/
def rename (ρ : Fin n → Fin m) : Expr n → Expr m
  | lit v => lit v
  | null τ => null τ
  | col i => col (ρ i)
  | unary op e => unary op (e.rename ρ)
  | binary op e₁ e₂ => binary op (e₁.rename ρ) (e₂.rename ρ)
  | inList e vs => inList (e.rename ρ) vs
  | caseWhen c a b => caseWhen (c.rename ρ) (a.rename ρ) (b.rename ρ)

/-- Replace every column `i` of an expression by the expression `σ i`. -/
def subst (σ : Fin n → Expr m) : Expr n → Expr m
  | lit v => lit v
  | null τ => null τ
  | col i => σ i
  | unary op e => unary op (e.subst σ)
  | binary op e₁ e₂ => binary op (e₁.subst σ) (e₂.subst σ)
  | inList e vs => inList (e.subst σ) vs
  | caseWhen c a b => caseWhen (c.subst σ) (a.subst σ) (b.subst σ)

/-- Renaming is substitution by column references. -/
theorem rename_eq_subst (ρ : Fin n → Fin m) (e : Expr n) : e.rename ρ = e.subst (col ∘ ρ) := by
  induction e <;> simp_all [rename, subst]

@[simp] theorem rename_id (e : Expr n) : e.rename id = e := by
  induction e <;> simp_all [rename]

theorem rename_rename (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (e : Expr n) :
    (e.rename ρ).rename ρ' = e.rename (ρ' ∘ ρ) := by
  induction e <;> simp_all [rename]

@[simp] theorem subst_col (e : Expr n) : e.subst col = e := by
  induction e <;> simp_all [subst]

theorem subst_subst (σ : Fin n → Expr m) (σ' : Fin m → Expr k) (e : Expr n) :
    (e.subst σ).subst σ' = e.subst fun i => (σ i).subst σ' := by
  induction e <;> simp_all [subst]

/-- Evaluating a renamed expression is evaluating the original on the reindexed row. -/
theorem eval_rename (ρ : Fin n → Fin m) (r : Row m) (e : Expr n) :
    (e.rename ρ).eval r = e.eval (r ∘ ρ) := by
  induction e <;> simp_all [rename, eval]

/-- Evaluating a substituted expression is evaluating the original on the row `d` of the
substituted results, when every `σ i` succeeds with `d i`. -/
theorem eval_subst {σ : Fin n → Expr m} {r : Row m} {d : Row n}
    (h : ∀ i, (σ i).eval r = .ok (d i)) (e : Expr n) : (e.subst σ).eval r = e.eval d := by
  induction e <;> simp_all [subst, eval]

/-- An expression over the left input of a join reads the left part of the joined row. -/
theorem eval_rename_castAdd (e : Expr n) (r : Row n) (s : Row m) :
    (e.rename (Fin.castAdd m)).eval (Fin.append r s) = e.eval r := by
  rw [eval_rename]
  congr 1
  funext i
  exact Fin.append_left r s i

/-- An expression over the right input of a join reads the right part of the joined row. -/
theorem eval_rename_natAdd (e : Expr m) (r : Row n) (s : Row m) :
    (e.rename (Fin.natAdd n)).eval (Fin.append r s) = e.eval s := by
  rw [eval_rename]
  congr 1
  funext i
  exact Fin.append_right r s i

/-- Evaluation depends on the substituted expressions only through their observations: if `σ i`
and `σ' i` succeed together with the same result, so do `e.subst σ` and `e.subst σ'`. -/
theorem toOption_eval_subst_congr {σ σ' : Fin n → Expr m} {r : Row m}
    (h : ∀ i, ((σ i).eval r).toOption = ((σ' i).eval r).toOption) (e : Expr n) :
    ((e.subst σ).eval r).toOption = ((e.subst σ').eval r).toOption := by
  induction e <;> simp_all [subst, eval, Except.toOption_bind, apply_ite Except.toOption]

end Expr

end Cslib.SQL
