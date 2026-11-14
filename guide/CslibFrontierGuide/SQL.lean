/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/
import VersoManual
import CslibFrontier.Languages.SQL.JoinSize
import CslibFrontier.Languages.SQL.QueryEquiv

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 80

#doc (Manual) "SQL Query Semantics" =>
%%%
tag := "sql-query-semantics"
%%%

A query rewrite is correct when the rewritten query returns the same rows as the original on
every database. Stating that requires a semantics: what a query returns, when it fails, and what
`NULL` does. The library's SQL semantics evaluates queries in Lean, so a concrete query is checked
by computation and a law about all databases is a theorem. It adapts and redesigns Evelyn
Mitchell's [`sql_equiv`][sql-equiv].

This chapter builds a two-table database, evaluates queries over it, and applies the theorem that
an equijoin returns as many rows as the join size of its keys. The
[manual page][manual] describes the full semantic contract.

```
import CslibFrontier.Languages.SQL.JoinSize
import CslibFrontier.Languages.SQL.QueryEquiv

open Cslib.SQL Cslib.SQL.Query
```

```lean -show
open Cslib.SQL Cslib.SQL.Query
```

# Schemas and Instances
%%%
tag := "sql-schemas"
%%%

A {name}`Cslib.SQL.DbSchema` names the tables and declares each table's columns, independently of
any data. A {name}`Cslib.SQL.Database` instance gives each table a list of rows, which is a bag:
duplicates matter and the order does not. A row is a function from column positions to cells,
and a cell is `NULL` (`none`) or a value. The instance below has a duplicate employee, an employee
without a department, and two departments with id `1`.

```lean
inductive Tbl where
  | emp
  | dept
  deriving DecidableEq

instance : Fintype Tbl where
  elems := {.emp, .dept}
  complete t := by cases t <;> decide

/-- `emp(name text, dept int)` and `dept(id int, title text)`. -/
abbrev S : DbSchema where
  Table := Tbl
  arity _ := 2
  columns
    | .emp => ![⟨some "emp", "name", .text⟩, ⟨some "emp", "dept", .int⟩]
    | .dept => ![⟨some "dept", "id", .int⟩, ⟨some "dept", "title", .text⟩]

abbrev emp : Query S 2 := .table Tbl.emp
abbrev dept : Query S 2 := .table Tbl.dept

abbrev D : Database S
  | Tbl.emp => [![some (.text "ann"), some (.int 1)],
      ![some (.text "bob"), some (.int 1)],
      ![some (.text "cy"), none],
      ![some (.text "ann"), some (.int 1)]]
  | Tbl.dept => [![some (.int 1), some (.text "eng")],
      ![some (.int 1), some (.text "ops")],
      ![none, some (.text "tmp")]]

example : D.Conforms := by decide
```

An instance conforms to its schema when every cell is `NULL` or a value of its column's declared
type. Equivalences and type soundness quantify over conforming instances only.

# Evaluation
%%%
tag := "sql-evaluation"
%%%

{name}`Cslib.SQL.Query.eval` returns the list of result rows or an error. Columns are positions:
`.col 1` is `emp.dept`. Results are rows, which are functions, so they are compared after
{name}`Except.toOption` by `decide`.

A `WHERE` clause keeps a row only when its predicate is `TRUE`. SQL's logic has a third value,
`unknown`, and `NULL` produces it. Here `cy`'s department is `NULL`, so `dept <> 1` is `unknown`
and the row is dropped although `cy` is not in department `1`.

```lean
example : ((Query.select (.binary (.cmp .ne) (.col 1) (.lit (.int 1)))
    emp).eval D).toOption = some [] := by
  decide

example : ((Query.select (.unary .isNull (.col 1)) emp).eval D).toOption =
    some [![some (.text "cy"), none]] := by
  decide
```

Evaluation is strict: a predicate or a `SELECT` list is evaluated on every row, and the first
error fails the whole query. Dividing by zero is an error, not `NULL`.

```lean
example : (Query.project ![.binary (.arith .div) (.col 1) (.lit (.int 0))]
    emp).eval D = .error .divisionByZero := rfl
```

# Equijoins and Join Sizes
%%%
tag := "sql-join-sizes"
%%%

The equijoin `emp JOIN dept ON emp.dept = dept.id` uses the predicate
{name}`Cslib.SQL.Expr.eqCols`, which compares a column of the left input with a column of the
right input. Each of the three employees in department `1` meets both departments with id `1`.
The `NULL` keys match nothing, not even each other, because `NULL = NULL` is `unknown`.

```lean
abbrev empDept : Query S 4 :=
  .join (Expr.eqCols (1 : Fin 2) (0 : Fin 2)) emp dept

example : (empDept.eval D).toOption.map List.length = some 6 := by
  decide
```

The streaming library's {name}`Cslib.Streaming.joinSize` `u v` is `∑ₐ count a u · count a v`.
{name}`Cslib.SQL.Query.eval_join_table_eqCols_length_eq_joinSize_filterMap` says that, on every
conforming instance, the equijoin of two tables returns the join size of their non-null keys.
The key columns must be declared with the same type, which `rfl` checks here.

```lean
example (D' : Database S) (h : D'.Conforms) :
    ∃ ts, empDept.eval D' = .ok ts ∧
      ts.length = Cslib.Streaming.joinSize
        ((D' Tbl.emp).filterMap (· 1)) ((D' Tbl.dept).filterMap (· 0)) :=
  eval_join_table_eqCols_length_eq_joinSize_filterMap 1 0 h rfl

example : Cslib.Streaming.joinSize ((D Tbl.emp).filterMap (· 1))
    ((D Tbl.dept).filterMap (· 0)) = 6 := by
  decide
```

Counting with `NULL` equal to `NULL` would pair `cy` with the `tmp` department. That count is
correct when one input has no `NULL` key
({name}`Cslib.SQL.Query.eval_join_eqCols_length_eq_joinSize`); here both inputs have one.

# Equivalence
%%%
tag := "sql-equivalence"
%%%

{name}`Cslib.SQL.Query.Equiv` `ℓ q₁ q₂` says that on every conforming instance both queries fail,
or both succeed with results related at level `ℓ`: the same list, the same bag, or the same set.
Laws about expressions lift into queries by congruence. Here `AND` commutes inside a `WHERE`
clause; the input's typing context is needed because expression equivalence speaks about
conforming rows.

```lean
abbrev isOne : Expr 2 := .binary (.cmp .eq) (.col 1) (.lit (.int 1))
abbrev isAnn : Expr 2 := .binary (.cmp .eq) (.col 0) (.lit (.text "ann"))

example : Equiv .ordered (.select (.binary .and isOne isAnn) emp)
    (.select (.binary .and isAnn isOne) emp) :=
  Equiv.select_expr (Γ := S.ctx Tbl.emp) rfl
    (Expr.Equiv.binary_comm (fun a b => by rw [evalBinOp_and_comm]) _ _)
```

A law that moves or drops an evaluation needs a side condition. Because evaluation is strict,
moving a `WHERE` clause below a `SELECT` list that may fail can turn a failing query into a
succeeding one; the decidable check {name}`Cslib.SQL.Expr.IsSafe` (well-typed, dividing only by
nonzero literals) rules this out. The [join-size tests][tests] prove such a rewrite for a concrete
query with the check discharged by `decide`, and show a failing instance when the check fails.

The fragment has no subqueries, outer joins, aggregates or `ORDER BY` yet; the
[manual page][manual] lists the limitations and the known differences from SQLite.

[sql-equiv]: https://github.com/evelynmitchell/sql_equiv
[manual]: https://github.com/cslib-community/cslib-frontier/blob/main/manual/circuits-logic-and-other-models/sql-semantics.md
[tests]: https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/Languages/SQL/JoinSize.lean
