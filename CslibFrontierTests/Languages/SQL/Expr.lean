/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.SQL.Column
public import CslibFrontier.Languages.SQL.Equiv

/-! Checked examples of resolved SQL expressions, typing, safety, equivalence and name resolution,
through ordinary imports. Evaluations are computed by `rfl`; typing, safety and conformance are
decided by `decide`. -/

public section

namespace CslibFrontierTests.SQL.Expr

open Cslib.SQL Cslib.SQL.Expr

/-- The integer literal `z`. -/
abbrev int {n : ℕ} (z : ℤ) : Expr n := lit (.int z)

/-- The typing context `(int, int, text)`. -/
abbrev Γ : Fin 3 → SqlType := ![.int, .int, .text]

/-- The row `(1, NULL, 'x')`. -/
abbrev r : Row 3 := ![some (.int 1), none, some (.text "x")]

/-! ### Rows -/

example : r.Conforms Γ := by decide
example : ¬Row.Conforms Γ ![some (.text "1"), none, none] := by decide
example : r ≠ ![some (.int 1), none, none] := by decide
-- Rows computed by reindexing compare by `decide` too.
example : r ∘ Fin.rev = ![some (.text "x"), none, some (.int 1)] := by decide

/-! ### Evaluation -/

-- Column references read the row by position.
example : (col 0).eval r = .ok (some (.int 1)) := rfl
example : (binary (.arith .add) (col 0) (int 2)).eval r = .ok (some (.int 3)) := rfl

-- `NULL` propagates through `=`, so `x = x` is not `TRUE` when `x` is `NULL`: a rewriter may not
-- replace it by `TRUE` without knowing that `x` is non-null.
example : (binary (.cmp .eq) (col 1) (col 1)).evalTruth r = .ok .unknown := rfl
example : (unary .isNull (col 1)).evalTruth r = .ok .true := rfl
example : (binary .or (binary (.cmp .eq) (col 1) (int 1)) (unary .isNull (col 1))).evalTruth r =
    .ok .true := rfl
example : (inList (col 0) [some (.int 2), none]).evalTruth r = .ok .unknown := rfl

-- Errors: an ill-typed operand, a division by zero, and a non-boolean predicate.
example : (binary (.arith .add) (col 0) (col 2)).eval r = .error .typeMismatch := rfl
example : (binary (.arith .div) (col 0) (int 0)).eval r = .error .divisionByZero := rfl
example : (col 0).evalTruth r = .error .typeMismatch := rfl

-- Evaluation is strict: the left error is reported even though the right one comes later.
example : (binary (.cmp .lt) (binary (.arith .div) (col 0) (int 0)) (col 2)).eval r =
    .error .divisionByZero := rfl

-- `CASE` evaluates only the branch it takes: the error in the other branch is not raised.
example : (caseWhen (lit (.bool true)) (int 1) (binary (.arith .div) (col 0) (int 0))).eval r =
    .ok (some (.int 1)) := rfl
-- An `unknown` condition takes the `ELSE` branch.
example : (caseWhen (binary (.cmp .eq) (col 1) (int 1)) (binary (.arith .div) (col 0) (int 0))
    (int 2)).eval r = .ok (some (.int 2)) := rfl

/-! ### Renaming and substitution -/

-- A predicate on the left input of a join, moved onto the joined row.
example (s : Row 2) :
    ((binary (.cmp .gt) (col 0) (int 0)).rename (Fin.castAdd 2)).evalTruth (Fin.append r s) =
      .ok .true := by
  simp only [evalTruth, eval_rename_castAdd]
  rfl

-- A predicate on the output of `SELECT col 0 + 1, col 2` is a predicate on the input row.
example : ((binary (.cmp .eq) (col 0) (int 2)).subst
    ![binary (.arith .add) (col 0) (int 1), col 2]).evalTruth r = .ok .true := rfl

/-! ### Typing and safety -/

example : (binary (.arith .add) (col 0) (col 1)).typeOf Γ = some .int := rfl
example : (binary (.arith .add) (col 0) (col 2)).typeOf Γ = none := rfl
example : (caseWhen (unary .isNull (col 1)) (null .int) (col 0)).typeOf Γ = some .int := rfl
example : (inList (col 2) [some (.int 1)]).typeOf Γ = none := rfl

-- Type soundness: an `int`-typed expression never raises a type error on a conforming row.
example (s : Row 3) (hs : s.Conforms Γ) :
    (binary (.arith .add) (col 0) (col 1)).eval s ≠ .error .typeMismatch :=
  eval_ne_typeMismatch hs rfl

-- Division by a nonzero literal is safe; by a column it is not, even if the column is never zero.
example : (binary (.arith .div) (col 0) (int 2)).IsSafe Γ := by decide
example : ¬(binary (.arith .div) (col 0) (col 1)).IsSafe Γ := by decide
example : ¬(binary (.arith .div) (col 0) (int 0)).IsSafe Γ := by decide

-- A safe predicate selects or drops every conforming row without failing.
example (s : Row 3) (hs : s.Conforms Γ) :
    ∃ t, (binary (.cmp .le) (binary (.arith .mod) (col 0) (int 3)) (col 1)).evalTruth s = .ok t :=
  IsSafePredicate.exists_evalTruth_eq_ok (by decide) hs

/-! ### Equivalence -/

-- `NOT (a < b)` and `a >= b` are equivalent in any context.
example (a b : Expr 3) :
    Equiv Γ (unary .not (binary (.cmp .lt) a b)) (binary (.cmp .ge) a b) := by
  refine Equiv.of_eval_eq fun s _ => ?_
  simp only [eval_unary, eval_binary]
  rcases a.eval s with _ | x
  · rfl
  rcases b.eval s with _ | y
  · rfl
  exact (evalBinOp_cmp_negate .lt x y).symm

/-- `x IS NULL OR x IS NOT NULL` for the column `x = col 0`. -/
abbrev nullOrNotNull : Expr 1 := binary .or (unary .isNull (col 0)) (unary .isNotNull (col 0))

-- `TRUE` and `x IS NULL OR x IS NOT NULL` are equivalent …
example : Equiv ![.int] (lit (.bool true)) nullOrNotNull := by
  refine Equiv.of_eval_eq fun s _ => ?_
  cases h : s 0 <;> simp [eval_binary, eval_unary, h, evalUnOp, evalBinOp, Datum.toTruth,
    Truth.toDatum]

-- … but substituting `1 / 0` for `x` breaks the equivalence: `Equiv.subst` needs `divSafe`.
example : (((lit (.bool true)).subst ![binary (.arith .div) (int 1) (int 0)]).eval
      (Fin.elim0 : Row 0)).toOption = some (some (.bool true)) ∧
    ((nullOrNotNull.subst ![binary (.arith .div) (int 1) (int 0)]).eval
      (Fin.elim0 : Row 0)).toOption = none := by
  decide

/-! ### Name resolution -/

/-- The columns `t.a : int`, `t.b : int`, `u.a : text`. -/
abbrev cols : Fin 3 → Column :=
  ![⟨some "t", "a", .int⟩, ⟨some "t", "b", .int⟩, ⟨some "u", "a", .text⟩]

example : resolveColumn cols none "b" = .ok 1 := rfl
example : resolveColumn cols (some "u") "a" = .ok 2 := rfl
example : resolveColumn cols none "a" = .error .ambiguousColumn := rfl
example : resolveColumn cols none "c" = .error .unknownColumn := rfl
example : resolveColumn cols (some "u") "b" = .error .unknownColumn := rfl

-- A resolved reference has the requested name and qualifier, and an ambiguous one has two
-- different matching columns.
example {i : Fin 3} (h : resolveColumn cols (some "t") "a" = .ok i) :
    (cols i).name = "a" ∧ (cols i).qualifier = some "t" :=
  Column.matches_some.mp (Column.Matches.of_resolveColumn_eq_ok h)
example : ∃ i j, i ≠ j ∧ (cols i).Matches none "a" ∧ (cols j).Matches none "a" :=
  resolveColumn_eq_ambiguousColumn_iff.mp rfl

end CslibFrontierTests.SQL.Expr
