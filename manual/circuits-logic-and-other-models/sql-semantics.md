# SQL query semantics

`CslibFrontier/Languages/SQL/` gives an executable semantics for a fragment of SQL, so that a query
rewrite can be proved correct and an implementation can be checked against the rows a query
denotes. The development is tracked in [#5282](https://github.com/cslib-community/cslib-frontier/issues/5282),
whose semantic contract the modules implement. It adapts and redesigns Evelyn Mitchell's
[`sql_equiv`](https://github.com/evelynmitchell/sql_equiv) at revision `38030a6b`; the module
docstrings and [NOTICE](../../NOTICE) record what was taken and what changed. Everything lives in
the namespace `Cslib.SQL`.

The layers present so far are values with `NULL`, three-valued logic, scalar operators including
three-valued `IN`, and resolved expressions over rows with typing, safety and equivalence.
Queries, the query equivalence levels and the simplifier are later milestones of #5282 and will
extend this page.

## Values, `NULL` and errors

[Value.lean](../../CslibFrontier/Languages/SQL/Value.lean) defines the column types
`SqlType.int`, `SqlType.text` and `SqlType.bool`, and a `Value`, which is a non-null integer
(unbounded `ℤ`), string or boolean. A cell holds a `Datum`, an abbreviation for `Option Value` in
which `none` is SQL's `NULL`. `Datum.HasType d τ` says that `d` is `NULL` or a value of type `τ`;
`NULL` has every type. Errors are not datums: an operator returns `Except EvalError Datum`, so a
`NULL` result (`.ok none`) and a failure (`.error .typeMismatch` or `.error .divisionByZero`) stay
distinct. Decimals, bounded integers, collations and casts are not in the fragment.

## Three-valued logic

[Truth.lean](../../CslibFrontier/Languages/SQL/Truth.lean) defines `Truth` with
`false < unknown < true`. The order is a Mathlib `LinearOrder` and `BoundedOrder`, so `AND` is `⊓`,
`OR` is `⊔`, and Mathlib's lattice lemmas such as `inf_sup_left` apply unchanged. `Truth.not`
exchanges `false` and `true` and fixes `unknown` (Kleene's strong logic); it is an order
isomorphism onto the dual (`Truth.notOrderIso`) and satisfies De Morgan's laws (`Truth.not_inf`,
`Truth.not_sup`), but it is not a lattice complement: `unknown ⊔ not unknown = unknown`. It is
therefore not registered as `Compl`, whose Mathlib lemmas assume a Heyting or Boolean algebra.
`Truth.isTrue` is the test that `WHERE` and `ON` apply: only `true` keeps a row.

## Operators

[Scalar.lean](../../CslibFrontier/Languages/SQL/Scalar.lean) defines `evalUnOp` (`NOT`, unary
minus, `IS NULL`, `IS NOT NULL`) and `evalBinOp` (integer `+ - * / %`, the comparisons
`= <> < <= > >=`, `AND`, `OR` and text `||`) on datums. The rules are:

- A non-null operand of the wrong type is `typeMismatch`, even when the other operand is `NULL`.
  Otherwise a `NULL` operand gives `NULL`; so `NULL / 0` is `NULL` while `1 / 0` is
  `divisionByZero`.
- `/` truncates toward zero and `%` has the dividend's sign (`Int.tdiv`, `Int.tmod`).
- Comparisons need two values of one type: integers numerically, text by code points, booleans
  with `false < true`. The result is `TRUE`, `FALSE` or, for `unknown`, `NULL`.
- `AND`, `OR` and `NOT` act on `Datum.toTruth` of their operands: a boolean gives its value, `NULL`
  gives `unknown`, another value is a type error.
- Both operands are always evaluated and the left one's error is reported first, so `FALSE AND 1`
  is a type error.

Each primitive (`addInt`, `divInt`, `compareInt`, `compareText`, `concatText`, …) is a separately
named function, so a bounded-integer or collation variant can replace one primitive without
changing the operator rules.

The laws a rewriter needs are equations of results: `evalBinOp_cmp_negate` (`NOT (a < b)` is
`a >= b`), `evalBinOp_cmp_swap` (`a < b` is `b > a`), `evalBinOp_and_comm`, `not_evalBinOp_and`
and the other De Morgan law, `evalBinOp_add_comm` and `evalBinOp_mul_comm`. They hold even for
ill-typed operands, because every type error is the same `typeMismatch`. Identities that inspect
an operand need it to be integer-typed (`evalBinOp_add_zero`, `evalBinOp_arith_null_left`), and
some familiar ones fail on `NULL`: `NULL * 0` is `NULL`, not `0`.

## Membership and `NOT IN`

`Datum.inList e vs` is three-valued `e IN (v₁, …, vₖ)`: the Kleene disjunction of the comparisons
`e = vᵢ`, starting from `FALSE`, evaluated strictly from the left. When the probe and the list
share a type, `Datum.inList_eq_ok` gives its closed form: `FALSE` for an empty list, even for a
`NULL` probe; `TRUE` when the non-null probe occurs in the list; `FALSE` when, moreover, nothing is
`NULL`; and `unknown` otherwise. A list element of another type makes the membership fail.

`NOT IN` is the negation `Truth.not`, and it differs from `NOT EXISTS (… WHERE v = e)` whenever a
`NULL` makes the membership `unknown`. `Datum.isTrue_not_inList_iff_iff` states the exact
condition: over a common type the two filters keep the same rows exactly when the list is empty,
some element matches, or the probe is non-null and the list has no `NULL`. For example
`1 NOT IN (2, NULL)` is `unknown`, so a `WHERE` drops the row, while the `NOT EXISTS` form keeps
it. Subqueries are a later milestone that will reuse `Datum.inList`.

## Rows, columns and names

[Row.lean](../../CslibFrontier/Languages/SQL/Row.lean) defines `Row n := Fin n → Datum`. Columns
are positions, so a reference to a missing column cannot be written, and the types an expression
is checked against form a typing context `Γ : Fin n → SqlType`. `Row.Conforms Γ r` says that
every cell of `r` is `NULL` or a value of its column's type; it is decidable, and so is equality
of rows, which `decide` evaluates on concrete rows such as `![some (.int 1), none]`. The row of a
join is `Fin.append` of the input rows, with left columns at `Fin.castAdd` and right columns at
`Fin.natAdd`, and `Row.conforms_append_iff` splits its conformance.

Names are metadata in [Column.lean](../../CslibFrontier/Languages/SQL/Column.lean): a `Column`
has an optional qualifier, a name and a declared type. `resolveColumn cols q name` resolves the
reference `[q.]name` against `cols : Fin n → Column` to the only matching position, or fails with
`unknownColumn` or `ambiguousColumn`. An unqualified reference matches every column of that name,
and names compare exactly, so a parser normalizes case first. `resolveColumn_eq_ok_iff`,
`resolveColumn_eq_unknownColumn_iff` and `resolveColumn_eq_ambiguousColumn_iff` characterize the
three outcomes; they are what a future surface-SQL translator needs to prove its output
well-scoped.

## Expressions

[Expr.lean](../../CslibFrontier/Languages/SQL/Expr.lean) defines `Expr n` with literals, typed
`NULL` literals (`Expr.null τ`), column references `Expr.col i`, the unary and binary operators,
`Expr.inList e vs` over a list of datums and `Expr.caseWhen c a b`. `Expr.eval r e` is strict and
left to right, except that `CASE` evaluates only the branch it takes
(`Expr.eval_caseWhen_of_true`, `Expr.eval_caseWhen_of_ne_true`): an error in the untaken branch
is not raised. `Expr.evalTruth` reads a predicate as `WHERE` and `ON` do, failing on a
non-boolean result.

Expressions move between scopes by explicit renaming and substitution. `Expr.eval_rename` says
that `e.rename ρ` evaluates as `e` on the reindexed row `r ∘ ρ`; for a predicate pushed into a
join, `Expr.eval_rename_castAdd` and `Expr.eval_rename_natAdd` evaluate it on its own side of the
joined row. `e.subst σ` replaces column `i` by the expression `σ i`, as when a predicate over a
derived table `SELECT σ₀, …, σₖ FROM …` is moved onto the input rows; `Expr.eval_subst`
evaluates it as `e` on the row of results `d` once every `σ i` evaluates to `d i`.

## Typing and safety

[Typing.lean](../../CslibFrontier/Languages/SQL/Typing.lean) gives the result types of the
operators (`UnOp.typeOf`, `BinOp.typeOf`) and of expressions (`Expr.typeOf Γ e`): comparisons need
operands of one type, `IN` needs list elements of the probe's type, and `CASE` needs a boolean
condition and branches of one type. Type soundness, `Expr.eval_ok_or_divisionByZero`, says that
on a row conforming to `Γ` an expression of type `τ` returns `NULL` or a value of type `τ`, or
divides by zero; it never raises `typeMismatch` (`Expr.eval_ne_typeMismatch`).

Division by zero is excluded syntactically: `Expr.divSafe e` holds when every `/` and `%` in `e`
divides by a nonzero integer literal. `Expr.IsSafe Γ e` (well-typed and `divSafe`) and
`Expr.IsSafePredicate Γ e` (also boolean) are decidable, and a safe expression or predicate
succeeds on every conforming row (`Expr.IsSafe.exists_eval_eq_ok`,
`Expr.IsSafePredicate.exists_evalTruth_eq_ok`). This is the side condition that a law moving,
duplicating or dropping an evaluation needs. A divisor that is a column is not safe even if the
data never makes it zero: the check reads only the expression.

## Expression equivalence

[Equiv.lean](../../CslibFrontier/Languages/SQL/Equiv.lean) defines `Expr.Equiv Γ e₁ e₂`: on every
row conforming to `Γ`, both expressions fail or both succeed with the same datum. Equivalence
observes `Except.toOption`, not which error occurred, because SQL leaves the order of evaluation
to the engine and strict evaluation fixes only one order. It is an equivalence relation
(`Expr.equivSetoid`), a congruence for every constructor (`Expr.Equiv.unary`,
`Expr.Equiv.binary`, `Expr.Equiv.inList`, `Expr.Equiv.caseWhen`), and compatible with renaming
(`Expr.Equiv.rename`) and with substitution of equivalent expressions (`Expr.Equiv.subst_right`).
Substituting into equivalent expressions (`Expr.Equiv.subst`) needs the substituted expressions
to be `divSafe` and of the column types: `TRUE` and `x IS NULL OR x IS NOT NULL` are equivalent,
but after substituting `1 / 0` for `x` only the second fails. `Expr.Equiv.evalTruth` says that
equivalent predicates keep the same rows.

## Working with the API

Import `CslibFrontier.Languages.SQL.Scalar` for the operators, or
`CslibFrontier.Languages.SQL.Equiv` for expressions with typing and equivalence (each re-exports
the layers below it, except name resolution in `CslibFrontier.Languages.SQL.Column`), and open
`Cslib.SQL`. The definitions are exposed, so a concrete evaluation is checked by `rfl`, for
example `evalBinOp (.arith .div) (some (.int 1)) (some (.int 0)) = .error .divisionByZero`.
Use `rfl` rather than `decide` for results of type `Except`: Batteries derives
`DecidableEq (Except ε α)` without exposing its body, so `decide` cannot evaluate it from another
module. `decide` does work on datums, truth values and `Option`, for instance after
`Except.toOption`. To prove a law for all datums, case on the datums and their values, or rewrite
with the characterizations `Datum.exists_toTruth_eq_ok_iff`, `Datum.exists_asInt_eq_ok_iff` and
`CmpOp.exists_eval_eq_ok_iff`, which say when an operand is accepted. For expressions, prove a
law with `Expr.Equiv.of_eval_eq` and the evaluation equations `Expr.eval_unary`,
`Expr.eval_binary` and their siblings, then lift it into larger expressions with the congruence
lemmas. The checked examples are in [Truth.lean](../../CslibFrontierTests/Languages/SQL/Truth.lean),
[Scalar.lean](../../CslibFrontierTests/Languages/SQL/Scalar.lean) and
[Expr.lean](../../CslibFrontierTests/Languages/SQL/Expr.lean) under
`CslibFrontierTests/Languages/SQL/`.
