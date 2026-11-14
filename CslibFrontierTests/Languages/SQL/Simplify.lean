/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.SQL.Simplify
public import CslibFrontierTests.Languages.SQL.QueryLaws

/-! Checked runs of the SQL simplifier on the schema and instance of `CslibFrontierTests.SQL.Query`,
through ordinary imports: what it rewrites, what it refuses to rewrite when a guard fails (with a
checked counterexample showing that the guard is needed), and the certificate carrying a fact from
a simplified expression or query back to the original. Simplified expressions and queries are
compared by `rfl`: the simplifier builds a simplified `SELECT` list with `FinVec.map`, so that of a
literal `![…]` list is again a literal list. -/

public section

namespace CslibFrontierTests.SQL.Simplify

open Cslib.SQL Cslib.SQL.Query CslibFrontierTests.SQL.Query CslibFrontierTests.SQL.QueryLaws
open Cslib.SQL.Expr (col lit null unary binary inList caseWhen)

/-! ### Expressions over `emp(name text, dept int)` -/

/-- `NOT (dept < 1 + 1)`. -/
abbrev notLt : Expr 2 :=
  unary .not (binary (.cmp .lt) (col 1) (binary (.arith .add) (int 1) (int 1)))

-- The constant folds and the `NOT` flips the comparison: `dept >= 2`.
example : notLt.simplify Γemp = binary (.cmp .ge) (col 1) (int 2) := rfl

-- The certificate covers every row conforming to `(text, int)`, including those whose `dept` is
-- `NULL`; so the two predicates keep the same rows in any `WHERE`.
example {r : Row 2} (hr : r.Conforms Γemp) :
    (notLt.evalTruth r).toOption = ((binary (.cmp .ge) (col 1) (int 2)).evalTruth r).toOption :=
  (Expr.equiv_simplify Γemp notLt).evalTruth hr

-- `(dept + 0) * 1 = 3 AND TRUE` is `dept = 3`: `dept` is an integer and the comparison boolean.
example : (binary .and
      (binary (.cmp .eq) (binary (.arith .mul) (binary (.arith .add) (col 1) (int 0)) (int 1))
        (int 3))
      (lit (.bool true))).simplify Γemp =
    binary (.cmp .eq) (col 1) (int 3) := rfl

-- Double negation of a boolean, and `NOT` over a null test.
example : (unary .not (unary .not isAnn)).simplify Γemp = isAnn := rfl
example : (unary .not (unary .isNull (col 1)) : Expr 2).simplify Γemp =
    unary .isNotNull (col 1) := rfl

-- `IN` lists: the empty list over a safe operand, a singleton, and `NOT IN` of a singleton.
example : (inList (col 1) [] : Expr 2).simplify Γemp = lit (.bool false) := rfl
example : (inList (col 1) [some (.int 1)] : Expr 2).simplify Γemp = isOne := rfl
example : (unary .not (inList (col 1) [some (.int 2)]) : Expr 2).simplify Γemp =
    binary (.cmp .ne) (col 1) (int 2) := rfl

-- A `CASE` with a constant condition takes its branch, so the division by zero in the other branch
-- disappears.
example : (caseWhen (binary (.cmp .gt) (int 1) (int 2)) (binary (.arith .div) (col 1) (int 0))
      (col 1) : Expr 2).simplify Γemp = col 1 := rfl

-- `NULL + 1` folds to the integer `NULL`; `1 / 0` is an error and is not folded.
example : (binary (.arith .add) (null .int) (int 1) : Expr 2).simplify Γemp = null .int := rfl
example : (binary (.arith .div) (int 1) (int 0) : Expr 2).simplify Γemp =
    binary (.arith .div) (int 1) (int 0) := rfl

-- Folding and `CASE` elimination can make an ill-typed expression well-typed: `NULL::text + 0`
-- folds to a boolean `NULL`, and a `CASE` whose branches have different types becomes the branch
-- it takes. The certificate holds all the same, but typing must be checked on the input.
example : (binary (.arith .add) (null .text) (int 0) : Expr 2).typeOf Γemp = none := rfl
example : (binary (.arith .add) (null .text) (int 0) : Expr 2).simplify Γemp = null .bool := rfl
example : (caseWhen (lit (.bool true)) (int 1) (lit (.text "a")) : Expr 2).typeOf Γemp = none :=
  rfl
example : (caseWhen (lit (.bool true)) (int 1) (lit (.text "a")) : Expr 2).simplify Γemp =
    int 1 := rfl

/-! ### Guards that fail -/

/-- `dept * 0`. -/
abbrev mulZero : Expr 2 := binary (.arith .mul) (col 1) (int 0)

-- `x * 0` is not rewritten to `0` …
example : mulZero.simplify Γemp = mulZero := rfl

-- … because it is `NULL`, not `0`, when `x` is `NULL`.
example : ¬mulZero.Equiv Γemp (int 0) := fun h =>
  absurd (h ![some (.text "cy"), none] (by decide)) (by decide)

-- `p AND FALSE` becomes `FALSE` for a safe `p`, but not for the unsafe `dept / 0 = 1`, which
-- makes the conjunction fail on every row with a department.
example : (binary .and isOne (lit (.bool false))).simplify Γemp = lit (.bool false) := rfl
example : (binary .and divZeroEq (lit (.bool false))).simplify Γemp =
    binary .and divZeroEq (lit (.bool false)) := rfl
example : ¬(binary .and divZeroEq (lit (.bool false))).Equiv Γemp (lit (.bool false)) := fun h =>
  absurd (h ![some (.text "ann"), some (.int 1)] (by decide)) (by decide)

-- `p AND TRUE` is not `p` when `p` is not boolean: `dept AND TRUE` is a type error, `dept` is not.
example : (binary .and (col 1) (lit (.bool true)) : Expr 2).simplify Γemp =
    binary .and (col 1) (lit (.bool true)) := rfl
example : ¬(binary .and (col 1) (lit (.bool true)) : Expr 2).Equiv Γemp (col 1) := fun h =>
  absurd (h ![some (.text "ann"), some (.int 1)] (by decide)) (by decide)

-- Nor is `NOT (NOT p)`: `NOT (NOT dept)` is a type error, `dept` is not.
example : (unary .not (unary .not (col 1)) : Expr 2).simplify Γemp =
    unary .not (unary .not (col 1)) := rfl
example : ¬(unary .not (unary .not (col 1)) : Expr 2).Equiv Γemp (col 1) := fun h =>
  absurd (h ![some (.text "ann"), some (.int 1)] (by decide)) (by decide)

/-! ### Queries -/

/-- `SELECT * FROM (SELECT dept, name FROM emp) AS e JOIN dept ON e.dept = dept.id
WHERE e.name = 'ann' AND 1 < 2`. -/
abbrev pushQ : Query S 4 :=
  select (binary .and (binary (.cmp .eq) (col 1) (lit (.text "ann")))
      (binary (.cmp .lt) (int 1) (int 2)))
    (join (binary (.cmp .eq) (col 0) (col 2)) (project ![col 1, col 0] emp) dept)

-- `1 < 2` folds and the conjunction becomes `e.name = 'ann'`, which reads only the left input: it
-- moves into it, then through the derived table, where it becomes `name = 'ann'` on `emp`.
example : pushQ.simplify =
    join (binary (.cmp .eq) (col 0) (col 2)) (project ![col 1, col 0] (select isAnn emp)) dept :=
  rfl

-- The certificate transports results: on the test instance, as on every conforming one, the
-- original query returns what the simplified one does.
example : (pushQ.eval D).toOption = (pushQ.simplify.eval D).toOption :=
  equiv_ordered_iff.mp (equiv_simplify pushQ) D hD

-- A predicate on the right input moves there.
example : (select (idOne.rename (Fin.natAdd 2)) empDept).simplify =
    join (binary (.cmp .eq) (col 1) (col 2)) emp (select idOne dept) := rfl

-- A predicate on both inputs of a cross join becomes the join predicate.
example :
    (select (binary (.cmp .eq) (col 1) (col 2)) (join (lit (.bool true)) emp dept)).simplify =
      empDept := rfl

-- `WHERE 1 = 1` folds to `WHERE TRUE`, which is dropped.
example : (select (binary (.cmp .eq) (int 1) (int 1)) emp).simplify = emp := rfl

-- A safe outer `WHERE` merges with the one below it; over `UNION ALL` it goes into both inputs.
example : (select isAnn (select divZeroEq emp)).simplify =
    select (binary .and divZeroEq isAnn) emp := rfl
example : (select isOne (unionAll emp noDept)).simplify =
    unionAll (select isOne emp) (select (binary .and (unary .isNull (col 1)) isOne) emp) := rfl

-- The outer predicate's safety is checked after simplification: this `CASE` hides `dept / 0`
-- behind a constant condition and simplifies to the safe `dept = 1`, so it merges.
example : (select (caseWhen (binary (.cmp .gt) (int 1) (int 2)) divZeroEq isOne)
      (select isAnn emp)).simplify = select (binary .and isAnn isOne) emp := rfl

-- `WHERE` moves below `DISTINCT` and keeps moving, here into the left input of the join.
example : (select (isAnn.rename (Fin.castAdd 2)) (distinct empDept)).simplify =
    distinct (join (binary (.cmp .eq) (col 1) (col 2)) (select isAnn emp) dept) := rfl

-- Projections fuse, and a projection that becomes `SELECT *` disappears.
example : (project ![col 1, col 0] (project ![col 1, col 0] emp)).simplify = emp := rfl
example :
    (project ![binary (.arith .mul) (col 0) (int 2)] (project ![col 1, col 0] emp)).simplify =
      project ![binary (.arith .mul) (col 1) (int 2)] emp := rfl
example : (project ![binary (.arith .add) (col 1) (int 0)]
      (project ![col 1, col 0] (project ![col 1, col 0] emp))).simplify =
    project ![col 1] emp := rfl

/-! ### Refusals at the query level -/

/-- `WHERE emp.dept / 0 = 1` over `emp JOIN dept ON emp.dept = dept.id`. -/
abbrev unsafeQ : Query S 4 := select (divZeroEq.rename (Fin.castAdd 2)) empDept

-- The predicate reads only the left input but is unsafe, so it stays above the join: below it, it
-- would be evaluated on employees without a partner (`CslibFrontierTests.SQL.QueryLaws` shows the
-- difference with the empty table).
example : unsafeQ.simplify = unsafeQ := rfl

-- An unsafe outer `WHERE` does not merge with the one below it.
example : (select divZeroEq (select isAnn emp)).simplify = select divZeroEq (select isAnn emp) :=
  rfl

-- An unsafe inner projection does not fuse: the outer one ignores it, so fusion would drop the
-- division.
example : (project ![int 1] (project ![divZeroEq] emp)).simplify =
    project ![int 1] (project ![divZeroEq] emp) := rfl

/-- `SELECT name + 1, dept FROM emp`, a type error. -/
abbrev badProj : Query S 2 := project ![binary (.arith .add) (col 0) (int 1), col 1] emp

-- Over an ill-typed input, a projection is neither simplified nor fused: its list stays as
-- written, whether a literal list (`1 + 1` is not folded) or a function.
example : badProj.typeOf = none := rfl
example : (project ![col 1, binary (.arith .add) (int 1) (int 1)]
      (project ![col 1, col 0] badProj)).simplify =
    project ![col 1, binary (.arith .add) (int 1) (int 1)] (project ![col 1, col 0] badProj) := rfl
example : (project (fun _ : Fin 1 => col 1) badProj).simplify =
    project (fun _ => col 1) badProj := rfl

/-! ### Transporting a fact across the certificate -/

/-- A query whose simplification is safe succeeds on every conforming instance, even when the query
itself fails the syntactic safety check. -/
theorem exists_eval_eq_ok_of_isSafe_simplify {n : ℕ} {q : Query S n} (hs : q.simplify.IsSafe)
    {D' : Database S} (hD' : D'.Conforms) : ∃ rs, q.eval D' = .ok rs := by
  obtain ⟨rs, h⟩ := hs.exists_eval_eq_ok hD'
  have h' := equiv_ordered_iff.mp (equiv_simplify q) D' hD'
  rw [h, Except.toOption_ok] at h'
  exact ⟨rs, Except.toOption_eq_some_iff.mp h'⟩

/-- `SELECT * FROM emp WHERE CASE WHEN 1 > 2 THEN dept / 0 = 1 ELSE name = 'ann' END`. -/
abbrev caseQ : Query S 2 :=
  select (caseWhen (binary (.cmp .gt) (int 1) (int 2)) divZeroEq isAnn) emp

example : caseQ.simplify = select isAnn emp := rfl

-- The division makes the query fail the safety check, but its simplification passes it, so the
-- query never fails on a conforming instance.
example : ¬caseQ.IsSafe := by decide
example (D' : Database S) (hD' : D'.Conforms) : ∃ rs, caseQ.eval D' = .ok rs :=
  exists_eval_eq_ok_of_isSafe_simplify (by decide) hD'

end CslibFrontierTests.SQL.Simplify
