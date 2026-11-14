# SQL query semantics

`CslibFrontier/Languages/SQL/` gives an executable semantics for a fragment of SQL, so that a query
rewrite can be proved correct and an implementation can be checked against the rows a query
denotes. The development is tracked in [#5282](https://github.com/cslib-community/cslib-frontier/issues/5282),
whose semantic contract the modules implement. It adapts and redesigns Evelyn Mitchell's
[`sql_equiv`](https://github.com/evelynmitchell/sql_equiv) at revision `38030a6b`; the module
docstrings and [NOTICE](../../NOTICE) record what was taken and what changed. Everything lives in
the namespace `Cslib.SQL`.

The layers present so far are values with `NULL`, three-valued logic, scalar operators including
three-valued `IN`, resolved expressions over rows with typing, safety and equivalence,
bag-semantics queries over database schemas with typing, safety and three levels of equivalence,
proved query transformations, and the theorem that an equijoin returns as many rows as the
streaming library's join size of its keys. The simplifier is another milestone-1 PR of #5282 and
will extend this page. The [supported fragment](#supported-fragment-and-limitations) section lists
what is not covered, and [differences from SQLite](#differences-from-sqlite) records where a
common engine disagrees with the semantics.

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
(`Expr.equivSetoid`; equivalences chain with `calc`), a congruence for every constructor
(`Expr.Equiv.unary`, `Expr.Equiv.binary`, `Expr.Equiv.inList`, `Expr.Equiv.caseWhen`), and
compatible with renaming (`Expr.Equiv.rename`) and with substitution of equivalent expressions
(`Expr.Equiv.subst_right`).
Substituting into equivalent expressions (`Expr.Equiv.subst`) needs the substituted expressions
to be `divSafe` and of the column types: `TRUE` and `x IS NULL OR x IS NOT NULL` are equivalent,
but after substituting `1 / 0` for `x` only the second fails. `Expr.Equiv.evalTruth` says that
equivalent predicates keep the same rows.

A law whose two sides return the same `Except` value on every conforming row is proved with
`Expr.Equiv.of_eval_eq`. That is not enough when the sides may fail with different first errors:
`a AND b` reports `a`'s error first and `b AND a` reports `b`'s. Such laws are proved on
observations, by rewriting with `Except.toOption_bind` and casing on the operands' results;
`Expr.Equiv.binary_comm` does this once for every operator whose observations do not depend on
the order of its operands, so `Expr.Equiv.binary_comm (fun a b => by rw [evalBinOp_and_comm])`
proves `a AND b ≡ b AND a`.

## Schemas and database instances

[Schema.lean](../../CslibFrontier/Languages/SQL/Schema.lean) defines a database schema
`DbSchema`: a type `Table` of table names and, for each table `t`, its arity `arity t` and its
column declarations `columns t : Fin (arity t) → Column`. The schema does not depend on data, so an
empty table has its columns and types. `S.ctx t` is the typing context of table `t`, its list of
declared types. A database instance `D : Database S` gives each table its rows,
`D t : List (Row (S.arity t))`. The list is a bag: duplicates matter, and its order is a property
of the representation only. `D.Conforms` says that every row of every table conforms to its
table's declared types; it is decidable when the table type is a `Fintype`, and
`Database.conforms_empty` says that the instance with only empty tables conforms.

## Queries

[Query.lean](../../CslibFrontier/Languages/SQL/Query.lean) defines `Query S n`, a query over the
schema `S` whose result rows have `n` columns:

| Constructor | SQL | Result |
|---|---|---|
| `table t` | `t` | the rows of `t`, with arity `S.arity t` |
| `select p q` | `SELECT * FROM q WHERE p` | the rows of `q` on which `p` is `TRUE` |
| `project es q` | `SELECT es₀, …, esₖ₋₁ FROM q` | one row of results per row of `q` |
| `join θ q₁ q₂` | `q₁ JOIN q₂ ON θ` | the rows `Fin.append r s` of the pairs on which `θ` is `TRUE` |
| `unionAll q₁ q₂` | `q₁ UNION ALL q₂` | the rows of both |
| `distinct q` | `SELECT DISTINCT * FROM q` | one copy of each row of `q` |

A cross join is `join (lit (.bool true)) q₁ q₂` and an equijoin
`join (binary (.cmp .eq) (col i) (col (Fin.natAdd n j))) q₁ q₂`. The arity is the type index:
`es : Fin k → Expr n` and `θ : Expr (n + m)` cannot mention a column their input lacks, and the
right columns of a join are `Fin.natAdd n j`.

`Query.eval D q : Except EvalError (List (Row n))` is structural and total. Projection, join and
`UNION ALL` keep duplicates; `DISTINCT` removes them with `List.dedup`, which keeps the last copy
of each row, and rows with `NULL` in the same places are duplicates, as SQL's `DISTINCT` treats
them. The list order is a property of the representation: a table keeps its list order, `WHERE`
and projection keep their input's order, a join enumerates pairs with the left row outermost
(`Row.product`), and `UNION ALL` lists its left input first. SQL promises no order without
`ORDER BY`, so laws about SQL are stated at the bag level below.

Evaluation is strict. `Expr.filterRows p rs` evaluates `p` on every row of `rs` and
`Expr.evalRow es r` every expression of a `SELECT` list on `r`, from left to right, and the first
error fails the whole query, even if an engine would have stopped before the failing row. A query
over an empty input evaluates nothing and succeeds: `SELECT dept / 0 FROM emp` fails when `emp` has
a row and returns no rows when it is empty. `Expr.toOption_filterRows` and
`Expr.evalRow_eq_ok_iff` state what `WHERE` and a `SELECT` list compute when they succeed.

## Query typing and safety

`Query.typeOf q : Option (Fin n → SqlType)` is the typing context of the result rows: a table has
its declared types, `WHERE` and `ON` predicates must be boolean over their input
(`Query.typeOf_select_eq_some`, `Query.typeOf_join_eq_some`), the expressions of a `SELECT` list
must be well-typed (`Query.typeOf_project_eq_some`), and the two inputs of `UNION ALL` must have
the same types. Type soundness, `Query.eval_ok_or_divisionByZero`, says that on a conforming
instance a well-typed query returns rows conforming to its type, or divides by zero in a
predicate or projection that is not `divSafe`; it never raises `typeMismatch`
(`Query.eval_ne_typeMismatch`, `Query.conforms_of_eval_eq_ok`). `Query.IsSafe q` (well-typed,
every division by a nonzero literal) is decidable, and a safe query succeeds on every conforming
instance (`Query.IsSafe.exists_eval_eq_ok`).

## Query equivalence

[QueryEquiv.lean](../../CslibFrontier/Languages/SQL/QueryEquiv.lean) defines
`Query.Equiv ℓ q₁ q₂`: on every conforming instance, both queries fail, or both succeed with
results related at the level `ℓ : EquivLevel`:

- `ordered`: equal lists. Nothing in the fragment orders rows, so this level is about the list
  representation; a law that holds at it holds at the others.
- `bag`: lists that are permutations of each other (`List.Perm`), SQL's meaning of a query
  without `ORDER BY`.
- `set`: lists with the same members, which is all that `DISTINCT` observes.

Like expression equivalence, it observes success and result through `Except.toOption`, not which
error occurred. `Query.Equiv.mono` weakens an equivalence from a finer level to a coarser one
(`ordered ≤ bag ≤ set`), and `Query.Equiv.of_ordered` to every level. Each level is an
equivalence relation (`Query.equivSetoid`, with `calc` support). The levels differ:
`emp UNION ALL q` and `q UNION ALL emp` are bag- but not ordered-equivalent, and `emp UNION ALL
emp` and `emp` are set- but not bag-equivalent; the
[tests](../../CslibFrontierTests/Languages/SQL/Query.lean) check both on a concrete instance.

Every constructor is a congruence at every level. In its query arguments this holds without
conditions (`Query.Equiv.select`, `Query.Equiv.project`, `Query.Equiv.join`,
`Query.Equiv.unionAll`, `Query.Equiv.distinct`). In its expression arguments it holds for
expression equivalence in the typing context of the input, which the input must have
(`Query.Equiv.select_expr`, `Query.Equiv.project_expr` and `Query.Equiv.join_expr`, taking
`q.typeOf = some Γ`): the input's rows then conform to `Γ`, which is where `Expr.Equiv Γ` speaks.
`DISTINCT` turns set equivalence into bag equivalence (`Query.Equiv.distinct_of_set`). The
list-level facts behind these proofs, such as `EquivLevel.Rel.filterRows` for `WHERE` over related
inputs, are public for proofs of further laws.

## Query laws

[QueryLaws.lean](../../CslibFrontier/Languages/SQL/QueryLaws.lean) proves the rewrite laws of the
fragment, each at the strongest level that holds. Because evaluation is strict, a law that changes
the rows on which a predicate or projection is evaluated holds only when that evaluation cannot
fail. Its side condition is the safety of that expression (`Expr.IsSafePredicate Γ p` or
`Expr.IsSafe Γ e`) in the typing context `Γ` of its input, which must be well-typed
(`q.typeOf = some Γ`). Both are decidable, so `by decide` discharges them on a concrete query, and
`rfl` proves `q.typeOf = some (S.ctx t)` for a table. Laws that evaluate every expression on the
same rows on both sides need no condition.

| Law | SQL | Level | Condition |
|---|---|---|---|
| `Query.select_select` | `WHERE p` over `WHERE c` is `WHERE c AND p` | ordered | `p` safe |
| `Query.select_comm` | two `WHERE` clauses commute | ordered | both safe |
| `Query.select_project` | `WHERE p` over `SELECT es` is `SELECT es` over `WHERE p.subst es` | ordered | `es` safe |
| `Query.select_join_left` | `WHERE p.rename (Fin.castAdd m)` over a join is the join of `WHERE p` over its left input | ordered | `p` and `θ` safe |
| `Query.select_join_right` | the same for the right input, with `Fin.natAdd n` | ordered | `p` and `θ` safe |
| `Query.select_join_true` | `WHERE θ` over a cross join is the join `ON θ` | ordered | none |
| `Query.project_project` | `SELECT f` over `SELECT g` is `SELECT f.subst g` | ordered | `g` safe |
| `Query.project_col` | `SELECT *` is the identity | ordered | none |
| `Query.select_unionAll`, `Query.project_unionAll` | `WHERE` and `SELECT` distribute over `UNION ALL` | ordered | none |
| `Query.unionAll_assoc` | `UNION ALL` is associative | ordered | none |
| `Query.unionAll_comm` | `UNION ALL` is commutative | bag | none |
| `Query.join_comm` | a join is the exchanged join, with its columns put back through `finAddFlip` | bag | none |
| `Query.distinct_distinct`, `Query.distinct_unionAll_self` | `DISTINCT` is idempotent and absorbs `q UNION ALL q` | ordered | none |
| `Query.select_distinct` | `WHERE` commutes with `DISTINCT` | ordered | none |

Each condition is needed, and the [law tests](../../CslibFrontierTests/Languages/SQL/QueryLaws.lean)
show an instance for each. With `p` an unsafe predicate such as `dept / 0 = 1`: `WHERE p` over
`WHERE FALSE` succeeds with no rows, while `WHERE FALSE AND p` and `WHERE FALSE` over `WHERE p`
fail, which covers `Query.select_select` and both conditions of `Query.select_comm`. Pushing
`WHERE p` into either input of a join whose other input is an empty table makes the pushed side
fail, while the original evaluates nothing; with an unsafe join predicate, pushing `WHERE FALSE`
into either input leaves no pair for it to fail on. An unsafe projection fails under `WHERE FALSE`
but not after the `WHERE` moves below it, and an unsafe inner projection that the outer one
ignores disappears in fusion. The two commutativity laws fail at the ordered level: the inputs'
rows come in another order. `Query.select_distinct` needs no condition although `DISTINCT` changes
how often `p` is evaluated: the rows it removes are copies of rows it keeps, on which `p` has the
same result or fails alike.

Laws compose: an ordered law weakens to any level with `Query.Equiv.of_ordered`, chains with others
by `calc`, and applies inside a larger query through the congruences of the previous section.
`Query.select_comm`, for instance, is `Query.select_select` twice joined by `Query.Equiv.select_expr`
with `Expr.Equiv.binary_comm` for `AND`.

## Equijoin row counts

[JoinSize.lean](../../CslibFrontier/Languages/SQL/JoinSize.lean) connects query evaluation to the
join size of the streaming library,
`Cslib.Streaming.joinSize u v = ∑ₐ count a u · count a v`
([Frequency.lean](../../CslibFrontier/Computability/Streaming/Frequency.lean)). The equijoin
`q₁ JOIN q₂ ON q₁.i = q₂.j` is `join (Expr.eqCols i j) q₁ q₂`, where `Expr.eqCols i j` compares
column `Fin.castAdd m i` with column `Fin.natAdd n j` of the joined row.

`Query.length_eq_joinSize_filterMap_of_eval_join_eqCols_eq_ok` is the count: if `q₁` and `q₂`
evaluate to `rs` and `ss` and the join succeeds, it returns
`joinSize (rs.filterMap (· i)) (ss.filterMap (· j))` rows, with no hypothesis on the keys. A
`NULL` key matches nothing, not even another `NULL`, so `filterMap` drops the `NULL` keys before
counting; on non-null values `=` is `TRUE` exactly for equal values. Comparing keys as datums,
with `NULL` equal to `NULL`, counts `joinSize (rs.map (· i)) (ss.map (· j))` instead, which is the
same number when one input has no `NULL` key (`Query.eval_join_eqCols_length_eq_joinSize`).

The join need not succeed: comparing an integer with a text value is a type error, but a
comparison with a `NULL` operand is `unknown` whatever the other operand (`CmpOp.eval`). So when
the keys are integers on one side and text on the other, the join fails exactly when each input has
a row whose key is not `NULL`; otherwise every comparison is `unknown`, and the join succeeds with
no rows. `Query.eval_join_eqCols_length_eq_joinSize_filterMap` guarantees success, and so the
count, when every key cell holds `NULL` or a value of one type `τ`; the key domain is then the
non-null values of `τ`.

On a conforming instance the typing hypothesis comes from the schema.
`Query.eval_join_eqCols_length_eq_joinSize_filterMap_of_typeOf` takes well-typed inputs whose key
columns have the same type, and `Query.eval_join_table_eqCols_length_eq_joinSize_filterMap` two
tables whose key columns are declared with the same type; for tables, conformance and that
declaration are the only hypotheses. `Expr.isSafePredicate_eqCols_iff` says that the equijoin
predicate is safe exactly when the key types agree. The count reduces the join's evaluation to a
filter over the pairs of input rows and applies
`Cslib.Streaming.length_filter_product_eq_joinSize_filterMap`; success under the typing
hypothesis comes from `Query.eval_join_eq_ok_of_forall`.

The [tests](../../CslibFrontierTests/Languages/SQL/JoinSize.lean) check each count both by
evaluation and through the theorem: keys `1, 1, 1, 2` against `1, 1, 3` give `6` rows, an empty
input gives none, and keys `1, NULL, NULL, 2` against `NULL, 1, 1` give `2` rows where structural
equality would count `4`. The null-safe join `ON l.k = r.k OR (l.k IS NULL AND r.k IS NULL)`
returns those `4`. Keys `NULL, 1, NULL` against `1, 1` give `2` rows, and since the right input
has no `NULL` key the structural count agrees.

## Working with the API

Import `CslibFrontier.Languages.SQL.Scalar` for the operators,
`CslibFrontier.Languages.SQL.Equiv` for expressions with typing and equivalence,
`CslibFrontier.Languages.SQL.QueryEquiv` for schemas, queries and query equivalence,
`CslibFrontier.Languages.SQL.QueryLaws` for the query laws, or
`CslibFrontier.Languages.SQL.JoinSize` for queries with the equijoin row counts, and open
`Cslib.SQL`. Each re-exports the layers below it; name resolution
(`CslibFrontier.Languages.SQL.Column`) comes with the schemas, and `JoinSize` includes neither
query equivalence nor the laws. The definitions are exposed, so a concrete evaluation is checked by
`rfl`, as in `evalBinOp (.arith .div) (some (.int 1)) (some (.int 0)) = .error .divisionByZero`.
Use `rfl` rather than `decide` for results of type `Except`: Batteries derives
`DecidableEq (Except ε α)` without exposing its body, so `decide` cannot evaluate it from another
module. `decide` does work on datums, truth values, rows and `Option`, for instance after
`Except.toOption`. A query result is a list of rows, which are functions, so compare it through
`Except.toOption` by `decide`, as in `((project ![col 1] emp).eval D).toOption = some […]`; `rfl`
cannot compare a computed row such as `Fin.append r s` with a literal `![…]`. Conformance of a
concrete instance is `decide` once the table type has a `Fintype` instance. To prove a law for all
datums, case on the datums and their values, or rewrite
with the characterizations `Datum.exists_toTruth_eq_ok_iff`, `Datum.exists_asInt_eq_ok_iff` and
`CmpOp.exists_eval_eq_ok_iff`, which say when an operand is accepted. For expressions, prove a
law with `Expr.Equiv.of_eval_eq` and the evaluation equations `Expr.eval_unary`,
`Expr.eval_binary` and their siblings, or on observations as above, then lift it into larger
expressions with the congruence lemmas and into queries with `Query.Equiv.select_expr` and its
siblings. For queries, `Query.Equiv.of_eval_eq` proves a law whose sides evaluate equally; in
general, rewrite with the evaluation equations (`Query.eval_select`, …), `Except.toOption_bind`,
and `Expr.toOption_filterRows` or `Except.toOption_mapM`, which reduce a query's observation to
list operations. The checked examples are in
[Truth.lean](../../CslibFrontierTests/Languages/SQL/Truth.lean),
[Scalar.lean](../../CslibFrontierTests/Languages/SQL/Scalar.lean),
[Expr.lean](../../CslibFrontierTests/Languages/SQL/Expr.lean),
[Query.lean](../../CslibFrontierTests/Languages/SQL/Query.lean),
[QueryLaws.lean](../../CslibFrontierTests/Languages/SQL/QueryLaws.lean) and
[JoinSize.lean](../../CslibFrontierTests/Languages/SQL/JoinSize.lean) under
`CslibFrontierTests/Languages/SQL/`, and the [guide](https://www.cslib.io/cslib-frontier/guide/)
has a chapter that builds a database, evaluates queries over it and applies the join-size
theorem.

## A downstream example

A development that uses the semantics imports the layer it needs and states its facts about
`Query.eval`. The following is the core of
[the join-size tests](../../CslibFrontierTests/Languages/SQL/JoinSize.lean): a schema with two
tables, an instance, an equijoin, its row count by evaluation, and the theorem for every
conforming instance.

```lean
import CslibFrontier.Languages.SQL.JoinSize

open Cslib.SQL Cslib.SQL.Query Cslib.Streaming

inductive T where
  | l
  | r
  deriving DecidableEq

instance : Fintype T where
  elems := {.l, .r}
  complete t := by cases t <;> decide

/-- `l(k int, tag text)` and `r(k int, tag text)`. -/
abbrev S : DbSchema where
  Table := T
  arity _ := 2
  columns
    | .l => ![⟨some "l", "k", .int⟩, ⟨some "l", "tag", .text⟩]
    | .r => ![⟨some "r", "k", .int⟩, ⟨some "r", "tag", .text⟩]

abbrev row (k : ℤ) (tag : String) : Row 2 := ![some (.int k), some (.text tag)]

abbrev D : Database S
  | T.l => [row 1 "a", row 1 "b", row 1 "c", row 2 "d"]
  | T.r => [row 1 "x", row 1 "y", row 3 "z"]

/-- `l JOIN r ON l.k = r.k`. -/
abbrev lr : Query S 4 := join (Expr.eqCols (0 : Fin 2) (0 : Fin 2)) (table T.l) (table T.r)

example : D.Conforms := by decide
example : (lr.eval D).toOption.map List.length = some 6 := by decide

example (D' : Database S) (hD' : D'.Conforms) :
    ∃ ts, lr.eval D' = .ok ts ∧
      ts.length = joinSize ((D' T.l).filterMap (· 0)) ((D' T.r).filterMap (· 0)) :=
  eval_join_table_eqCols_length_eq_joinSize_filterMap 0 0 hD' rfl
```

The same file proves a rewrite of a concrete query: `SELECT * FROM (SELECT tag, k + 1 AS k1 FROM l)
WHERE k1 = 2` is ordered-equivalent to `SELECT tag, k + 1 FROM l WHERE k + 1 = 2`, as an instance of
`Query.select_project`. Its typing side condition holds by `rfl`, and its guard, that every
projected expression is safe, is checked by `decide`. With the projection `tag, 100 / k` the guard
fails, and an instance with a row whose key is `0` separates the two queries: the original divides
by zero, while the rewritten query never evaluates `100 / 0` because the `WHERE` clause drops that
row first.

## Supported fragment and limitations

The fragment covers:

- values: unbounded integers, text compared by code points, booleans, and `NULL`;
- scalar expressions: literals, typed `NULL`, column references by position, `NOT`, unary minus,
  `IS [NOT] NULL`, `+ - * / %`, the six comparisons, `AND`, `OR`, text `||`, `[NOT] IN` over a
  list of literals, and `CASE WHEN … THEN … ELSE … END`;
- queries: tables, `WHERE`, `SELECT` lists, inner joins `ON θ` (including cross joins and
  equijoins), `UNION ALL` and `DISTINCT`, over schemas whose tables are declared independently of
  the data.

Later milestones of #5282 are not formalized yet: subqueries (`IN`, `EXISTS`, scalar and
correlated), outer joins, grouping and aggregates, `ORDER BY`, `LIMIT` and `OFFSET`, window
functions, recursive queries, updates, decimals and casts, bounded integers, collations, dialect
parameters, and a surface-SQL parser with a verified name-resolution pass. Column names are
metadata resolved by `resolveColumn`; queries themselves are positional, so a translation from SQL
text must resolve names first. `UNION` is `DISTINCT` of `UNION ALL`; `INTERSECT` and `EXCEPT` are
not in the fragment. Set-semantics relational foundations and Yannakakis's algorithm belong to
#4036.

## Differences from SQLite

The semantics follows standard SQL and PostgreSQL where engines differ. A differential run of 44
queries in this fragment against SQLite 3.45.1, recorded in
[#5335](https://github.com/cslib-community/cslib-frontier/pull/5335), agreed on 39 as bags of
rows, including joins with duplicate and `NULL` keys, `NULL` in `WHERE`, `IN` and `NOT IN` (also
with an empty list), `UNION ALL`, `DISTINCT` with `NULL` rows, integer division and remainder with
negative operands, and text order. SQLite has no boolean type, so `TRUE` and `FALSE` are the
integers `1` and `0` there; results were compared after mapping booleans to those integers. That
run is evidence, not proof. The other five queries differ in three expected ways:

- Division and remainder by zero give `NULL` in SQLite; here they fail with `divisionByZero`, as in
  PostgreSQL.
- SQLite compares values of different types and converts text to numbers in arithmetic; here
  such an operation is a type error, and a well-typed query never raises one
  (`Query.eval_ne_typeMismatch`).
- SQLite reads an integer as a truth value in `WHERE`; here a predicate must be boolean.

SQLite also resolves a column name that occurs twice in one derived table to the first such
column, where standard SQL and PostgreSQL report an ambiguous reference; `resolveColumn` returns
`ambiguousColumn`. Strict evaluation is a further difference from engines in general: SQL leaves
the order of evaluation and short-circuiting to the implementation, an engine may skip a failing
operand or row that this semantics evaluates, and the equivalences therefore require safety
before they move or drop an evaluation.
