/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Control.Except
public import CslibFrontier.Languages.SQL.Schema
public import CslibFrontier.Languages.SQL.Typing
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.ProdSigma

/-!
# SQL queries with bag semantics

`Query S n` is a query over the database schema `S` whose result rows have `n` columns: a table,
`WHERE` (`Query.select`), a `SELECT` list (`Query.project`), an inner join `ON θ`
(`Query.join`; a cross join is `ON TRUE`), `UNION ALL` (`Query.unionAll`) and `DISTINCT`
(`Query.distinct`). The output arity is the type index, so a projection list or a join predicate
cannot refer to a column its input lacks.

`Query.eval D q` evaluates `q` on the instance `D` and returns a list of rows or an error. The
list is a bag: projection, join and `UNION ALL` keep duplicates, and only `DISTINCT` removes them,
treating rows with `NULL` in the same places as duplicates, as SQL's `DISTINCT` does (Mathlib's
`List.dedup`, which keeps the last copy). The list order is a property of this representation,
not of SQL, which promises no order without `ORDER BY`: here a table keeps its list order,
`WHERE` keeps the order of its input, a join enumerates pairs with the left row outermost, and
`UNION ALL` lists its left input first. The equivalences in `Cslib.SQL.Query.Equiv` decide how
much of the order a law may rely on.

Evaluation is strict. A `WHERE` or `ON` predicate is evaluated on every input row or pair, and a
projection on every input row, from left to right; the first error fails the whole query, even
when an engine might never have reached the failing row. On an empty input nothing is evaluated,
so the same query succeeds (`Expr.filterRows`, `Expr.evalRow`).

`Query.typeOf q` is the typing context of the result, if `q` is well-typed: predicates are
boolean in the context of their input, projections are well-typed, and `UNION ALL` combines two
inputs of the same types. Type soundness (`Query.eval_ok_or_divisionByZero`): on a conforming
instance, a well-typed query returns rows conforming to its type, or fails with
`divisionByZero`, which requires a division that is not `divSafe`; it never raises
`typeMismatch`. The decidable check `Query.IsSafe` (well-typed, every division by a nonzero
literal) guarantees that evaluation succeeds on every conforming instance.

It adapts and redesigns the queries of `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell. There,
queries were untyped syntax whose column names were looked up in the rows at run time, and the
evaluator for the richer fragment (aggregates, subqueries, set operations) was partial. Here the
fragment is the select–project–join–union core with `DISTINCT`, columns are positions checked by
the type index, evaluation is structural and total, and errors are results rather than rows
silently dropped.

## Main definitions

* `Cslib.SQL.Query`: queries over a schema, indexed by their output arity.
* `Cslib.SQL.Query.eval`: strict evaluation on a database instance.
* `Cslib.SQL.Expr.filterRows`, `Cslib.SQL.Expr.evalRow`: `WHERE` and `SELECT` lists on a list of
  rows and on one row.
* `Cslib.SQL.Row.product`: the rows of a cross join.
* `Cslib.SQL.Expr.eqCols`: the equijoin predicate `q₁.i = q₂.j` over a joined row.
* `Cslib.SQL.Query.typeOf`: the typing context of a query's result.
* `Cslib.SQL.Query.divSafe`, `Cslib.SQL.Query.IsSafe`: the decidable safety check.

## Main results

* `Cslib.SQL.Expr.toOption_filterRows`, `Cslib.SQL.Expr.evalRow_eq_ok_iff`: what `WHERE` and a
  `SELECT` list compute when they succeed, and when they do.
* `Cslib.SQL.Expr.mem_of_filterRows_eq_ok`: `WHERE` keeps some of its input rows.
* `Cslib.SQL.Query.eval_join_eq_ok_of_forall`: a join whose predicate succeeds on every pair
  returns the joined pairs on which it is `TRUE`.
* `Cslib.SQL.Expr.evalTruth_eqCols_eq_ok_true_iff`, `Cslib.SQL.Expr.isSafePredicate_eqCols_iff`:
  the equijoin predicate keeps the pairs with the same non-null key, and is safe exactly when the
  key columns have the same type.
* `Cslib.SQL.Query.eval_ok_or_divisionByZero`: type soundness.
* `Cslib.SQL.Query.eval_ne_typeMismatch`, `Cslib.SQL.Query.conforms_of_eval_eq_ok`: a well-typed
  query never raises a type error, and its rows have its types.
* `Cslib.SQL.Query.IsSafe.exists_eval_eq_ok`: a safe query succeeds on every conforming instance.
-/

@[expose] public section

namespace Cslib.SQL

variable {n m k : ℕ}

/-- The rows of the cross join of `rs` and `ss`: every row `r` of `rs` followed by every row `s` of
`ss` gives the joined row `Fin.append r s`, with the left row outermost. -/
def Row.product (rs : List (Row n)) (ss : List (Row m)) : List (Row (n + m)) :=
  (rs ×ˢ ss).map fun (r, s) => Fin.append r s

/-- A row of the cross join is a left row joined with a right row. -/
theorem Row.mem_product {rs : List (Row n)} {ss : List (Row m)} {t : Row (n + m)} :
    t ∈ Row.product rs ss ↔ ∃ r ∈ rs, ∃ s ∈ ss, Fin.append r s = t := by
  simp only [Row.product, List.mem_map, List.mem_product, Prod.exists]
  constructor
  · rintro ⟨r, s, ⟨hr, hs⟩, rfl⟩
    exact ⟨r, hr, s, hs, rfl⟩
  · rintro ⟨r, hr, s, hs, rfl⟩
    exact ⟨r, s, ⟨hr, hs⟩, rfl⟩

/-- The rows of a cross join of conforming rows conform to the joined typing context. -/
theorem Row.conforms_of_mem_product {Γ : Fin n → SqlType} {Δ : Fin m → SqlType}
    {rs : List (Row n)} {ss : List (Row m)} (hrs : ∀ r ∈ rs, r.Conforms Γ)
    (hss : ∀ s ∈ ss, s.Conforms Δ) {t : Row (n + m)} (ht : t ∈ Row.product rs ss) :
    t.Conforms (Fin.append Γ Δ) := by
  obtain ⟨r, hr, s, hs, rfl⟩ := Row.mem_product.mp ht
  exact Row.conforms_append_iff.mpr ⟨hrs r hr, hss s hs⟩

namespace Expr

/-! ### `SELECT` lists and `WHERE` on rows -/

/-- Evaluate a `SELECT` list on a row, from left to right: the row of results, or the first
error. -/
def evalRow : {k : ℕ} → (Fin k → Expr n) → Row n → Except EvalError (Row k)
  | 0, _, _ => .ok ![]
  | _ + 1, es, r => do
    let d ← (es 0).eval r
    let ds ← evalRow (fun i => es i.succ) r
    return Matrix.vecCons d ds

/-- Keep the rows on which the predicate is `TRUE`, in order, as `WHERE` and `ON` do. The predicate
is evaluated on every row, and the first error fails the whole filter. -/
def filterRows (p : Expr n) (rs : List (Row n)) : Except EvalError (List (Row n)) :=
  rs.filterMapM fun r => do return if (← p.evalTruth r).isTrue then some r else none

/-- A `SELECT` list succeeds with the row `d` exactly when each expression succeeds with its cell
of `d`. -/
theorem evalRow_eq_ok_iff {es : Fin k → Expr n} {r : Row n} {d : Row k} :
    evalRow es r = .ok d ↔ ∀ i, (es i).eval r = .ok (d i) := by
  induction k with
  | zero =>
    simp only [evalRow, Except.ok.injEq, IsEmpty.forall_iff, iff_true]
    exact Subsingleton.elim _ _
  | succ k ih =>
    simp only [evalRow, Fin.forall_fin_succ]
    constructor
    · intro h
      obtain ⟨d₀, h₀, h⟩ := Except.bind_eq_ok.mp h
      obtain ⟨ds, hds, h⟩ := Except.bind_eq_ok.mp h
      cases h
      exact ⟨h₀, ih.mp hds⟩
    · rintro ⟨h₀, hs⟩
      rw [h₀, Except.ok_bind, ih.mpr hs, Except.ok_bind]
      exact congrArg Except.ok (Matrix.cons_head_tail d)

/-- A `SELECT` list succeeds exactly when each of its expressions does. -/
theorem exists_evalRow_eq_ok_iff {es : Fin k → Expr n} {r : Row n} :
    (∃ d, evalRow es r = .ok d) ↔ ∀ i, ∃ d, (es i).eval r = .ok d := by
  simp only [evalRow_eq_ok_iff]
  exact (Classical.skolem (p := fun i d => (es i).eval r = .ok d)).symm

/-- When a `SELECT` list fails, one of its expressions fails with that error. -/
theorem exists_eval_eq_error_of_evalRow_eq_error {es : Fin k → Expr n} {r : Row n}
    {e : EvalError} (h : evalRow es r = .error e) : ∃ i, (es i).eval r = .error e := by
  induction k with
  | zero => simp [evalRow] at h
  | succ k ih =>
    rcases h₀ : (es 0).eval r with e₀ | d₀
    · simp only [evalRow, h₀, Except.error_bind, Except.error.injEq] at h
      exact ⟨0, h ▸ h₀⟩
    · rcases hs : evalRow (fun i => es i.succ) r with e' | ds
      · simp only [evalRow, h₀, hs, Except.ok_bind, Except.error_bind, Except.error.injEq] at h
        obtain ⟨i, hi⟩ := ih (h ▸ hs)
        exact ⟨i.succ, hi⟩
      · simp [evalRow, h₀, hs, pure, Except.pure] at h

/-- `SELECT` lists whose expressions have the same observations on a row have the same
observation on it. -/
theorem toOption_evalRow_congr {es es' : Fin k → Expr n} {r : Row n}
    (h : ∀ i, ((es i).eval r).toOption = ((es' i).eval r).toOption) :
    (evalRow es r).toOption = (evalRow es' r).toOption := by
  refine Option.ext fun d => ?_
  rw [Except.toOption_eq_some_iff, Except.toOption_eq_some_iff, evalRow_eq_ok_iff,
    evalRow_eq_ok_iff]
  simp only [← Except.toOption_eq_some_iff, h]

/-- `WHERE` succeeds exactly when the predicate succeeds on every row, and then keeps the rows on
which it is `TRUE`, in order. -/
theorem toOption_filterRows (p : Expr n) (rs : List (Row n)) :
    (p.filterRows rs).toOption =
      if ∀ r ∈ rs, (p.evalTruth r).toOption.isSome then
        some (rs.filter fun r => (p.evalTruth r).toOption = some .true)
      else none := by
  have key : ∀ r : Row n,
      ((do return if (← p.evalTruth r).isTrue then some r else none :
        Except EvalError (Option (Row n)))).toOption =
        (p.evalTruth r).toOption.map fun t => if t.isTrue then some r else none := by
    intro r
    cases p.evalTruth r <;> rfl
  rw [filterRows, Except.toOption_filterMapM]
  simp only [key, Option.isSome_map]
  split_ifs
  · rw [← List.filterMap_eq_filter]
    refine congrArg some (List.filterMap_congr fun r _ => ?_)
    rcases h : p.evalTruth r with e | t
    · simp [h, Option.guard]
    · cases t <;> simp [h, Option.guard]
  · rfl

/-- When `WHERE` succeeds, it keeps some of its input rows. -/
theorem mem_of_filterRows_eq_ok {p : Expr n} {rs rs' : List (Row n)}
    (h : p.filterRows rs = .ok rs') {r : Row n} (hr : r ∈ rs') : r ∈ rs := by
  have h' := congrArg Except.toOption h
  rw [toOption_filterRows] at h'
  split_ifs at h'
  · simp only [Except.toOption_ok, Option.some.injEq] at h'
    exact (List.mem_filter.mp (h' ▸ hr)).1
  · simp at h'

/-- When `WHERE` fails, the predicate fails with that error on one of the rows. -/
theorem exists_evalTruth_eq_error_of_filterRows_eq_error {p : Expr n} {rs : List (Row n)}
    {e : EvalError} (h : p.filterRows rs = .error e) : ∃ r ∈ rs, p.evalTruth r = .error e := by
  obtain ⟨r, hr, he⟩ := Except.exists_mem_eq_error_of_filterMapM_eq_error h
  refine ⟨r, hr, ?_⟩
  rcases ht : p.evalTruth r with e' | t
  · simpa [ht] using he
  · simp [ht, pure, Except.pure] at he

/-- Type soundness for predicates: on a conforming row, a boolean predicate either has a truth
value or divides by zero, which requires a division that is not `divSafe`. -/
theorem evalTruth_ok_or_divisionByZero {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    (∃ t, p.evalTruth r = .ok t) ∨
      (p.evalTruth r = .error .divisionByZero ∧ p.divSafe = false) := by
  rcases eval_ok_or_divisionByZero hr hp with ⟨d, hd, hdτ⟩ | ⟨hd, hs⟩
  · obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hdτ
    exact .inl ⟨t, by simp [evalTruth, hd, ht]⟩
  · exact .inr ⟨by simp [evalTruth, hd], hs⟩

/-- On rows conforming to `Γ`, `WHERE` with a boolean predicate keeps some of the rows, or divides
by zero. -/
private theorem filterRows_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    (∃ rs', p.filterRows rs = .ok rs' ∧ ∀ r ∈ rs', r ∈ rs) ∨
      (p.filterRows rs = .error .divisionByZero ∧ p.divSafe = false) := by
  rcases h : p.filterRows rs with e | rs'
  · obtain ⟨r, hr, he⟩ := exists_evalTruth_eq_error_of_filterRows_eq_error h
    rcases evalTruth_ok_or_divisionByZero (hrs r hr) hp with ⟨t, ht⟩ | ⟨ht, hs⟩
    · simp [ht] at he
    · rw [he, Except.error.injEq] at ht
      exact .inr ⟨by rw [ht], hs⟩
  · exact .inl ⟨rs', rfl, fun _ => mem_of_filterRows_eq_ok h⟩

/-- Type soundness for `SELECT` lists: on a conforming row, well-typed expressions give a row of
their types, or one of them divides by zero. -/
private theorem evalRow_ok_or_divisionByZero {Γ : Fin n → SqlType} {Δ : Fin k → SqlType}
    {r : Row n} (hr : r.Conforms Γ) {es : Fin k → Expr n}
    (hes : ∀ i, (es i).typeOf Γ = some (Δ i)) :
    (∃ d, evalRow es r = .ok d ∧ d.Conforms Δ) ∨
      (evalRow es r = .error .divisionByZero ∧ ∃ i, (es i).divSafe = false) := by
  rcases h : evalRow es r with e | d
  · obtain ⟨i, hi⟩ := exists_eval_eq_error_of_evalRow_eq_error h
    rcases eval_ok_or_divisionByZero hr (hes i) with ⟨d, hd, -⟩ | ⟨hd, hs⟩
    · simp [hd] at hi
    · rw [hi, Except.error.injEq] at hd
      exact .inr ⟨by rw [hd], i, hs⟩
  · exact .inl ⟨d, rfl, fun i => hasType_of_eval_eq_ok hr (hes i) (evalRow_eq_ok_iff.mp h i)⟩

/-! ### Equijoin predicates -/

/-- The equijoin predicate `q₁.i = q₂.j` over the joined row of an `n`-column left input and an
`m`-column right input: column `i` of the left input (`Fin.castAdd m i`) equals column `j` of the
right input (`Fin.natAdd n j`). -/
def eqCols (i : Fin n) (j : Fin m) : Expr (n + m) :=
  binary (.cmp .eq) (col (Fin.castAdd m i)) (col (Fin.natAdd n j))

/-- The equijoin predicate on a joined row is the three-valued comparison of the two keys. -/
theorem evalTruth_eqCols (i : Fin n) (j : Fin m) (r : Row n) (s : Row m) :
    (eqCols i j).evalTruth (Fin.append r s) = CmpOp.eq.eval (r i) (s j) := by
  simp only [evalTruth, eqCols, eval_binary, eval_col, Fin.append_left, Fin.append_right,
    Except.ok_bind, evalBinOp]
  rcases CmpOp.eq.eval (r i) (s j) with e | t
  · rfl
  · exact Datum.toTruth_toDatum t

/-- The equijoin predicate keeps a pair of rows exactly when both keys are the same non-null
value. -/
theorem evalTruth_eqCols_eq_ok_true_iff {i : Fin n} {j : Fin m} {r : Row n} {s : Row m} :
    (eqCols i j).evalTruth (Fin.append r s) = .ok .true ↔ ∃ v, r i = some v ∧ s j = some v := by
  rw [evalTruth_eqCols, CmpOp.eval_eq_ok_true_iff]
  cases r i <;> cases s j <;> simp [eq_comm]

/-- The equijoin predicate is a safe predicate on the joined rows exactly when the two key
columns have the same type. -/
theorem isSafePredicate_eqCols_iff {Γ : Fin n → SqlType} {Δ : Fin m → SqlType} {i : Fin n}
    {j : Fin m} : (eqCols i j).IsSafePredicate (Fin.append Γ Δ) ↔ Γ i = Δ j := by
  simp only [IsSafePredicate, eqCols, typeOf, Fin.append_left, Fin.append_right, BinOp.typeOf,
    divSafe, BinOp.isDivision, Bool.not_false, Bool.true_or, Bool.and_self, and_true,
    Option.bind_eq_bind, Option.bind_some]
  split_ifs with h <;> simp [h]

end Expr

/-! ### Queries -/

/-- A query over the schema `S` whose result rows have `n` columns. -/
inductive Query (S : DbSchema) : ℕ → Type where
  /-- The rows of a table, in the instance's list order. -/
  | table (t : S.Table) : Query S (S.arity t)
  /-- `SELECT * FROM q WHERE p`: the rows of `q` on which `p` is `TRUE`. -/
  | select {n : ℕ} (p : Expr n) (q : Query S n) : Query S n
  /-- `SELECT es₀, …, esₖ₋₁ FROM q`: one row of results per row of `q`; duplicates are kept. -/
  | project {n k : ℕ} (es : Fin k → Expr n) (q : Query S n) : Query S k
  /-- `q₁ JOIN q₂ ON θ`: the joined rows `Fin.append r s` of the pairs on which `θ` is `TRUE`.
  The left columns come first; a cross join is `ON TRUE`. -/
  | join {n m : ℕ} (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) : Query S (n + m)
  /-- `q₁ UNION ALL q₂`: the rows of both, with duplicates. -/
  | unionAll {n : ℕ} (q₁ q₂ : Query S n) : Query S n
  /-- `SELECT DISTINCT * FROM q`: one copy of each row of `q`. Rows with `NULL` in the same places
  and equal values elsewhere are duplicates. -/
  | distinct {n : ℕ} (q : Query S n) : Query S n

namespace Query

variable {S : DbSchema}

/-- Evaluate a query on a database instance: the bag of result rows as a list, or the first error.
Every predicate and projection is evaluated on every row of its input. -/
def eval (D : Database S) : {n : ℕ} → Query S n → Except EvalError (List (Row n))
  | _, table t => .ok (D t)
  | _, select p q => do p.filterRows (← q.eval D)
  | _, project es q => do (← q.eval D).mapM (Expr.evalRow es)
  | _, join θ q₁ q₂ => do
    let rs ← q₁.eval D
    let ss ← q₂.eval D
    θ.filterRows (Row.product rs ss)
  | _, unionAll q₁ q₂ => do
    let rs ← q₁.eval D
    let ss ← q₂.eval D
    return rs ++ ss
  | _, distinct q => do return (← q.eval D).dedup

section Eval

variable (D : Database S)

@[simp] theorem eval_table (t : S.Table) : (table t).eval D = .ok (D t) := rfl

theorem eval_select (p : Expr n) (q : Query S n) :
    (select p q).eval D = (do p.filterRows (← q.eval D)) := rfl

theorem eval_project (es : Fin k → Expr n) (q : Query S n) :
    (project es q).eval D = (do (← q.eval D).mapM (Expr.evalRow es)) := rfl

theorem eval_join (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) :
    (join θ q₁ q₂).eval D =
      (do let rs ← q₁.eval D; let ss ← q₂.eval D; θ.filterRows (Row.product rs ss)) := rfl

theorem eval_unionAll (q₁ q₂ : Query S n) :
    (unionAll q₁ q₂).eval D = (do let rs ← q₁.eval D; let ss ← q₂.eval D; return rs ++ ss) :=
  rfl

theorem eval_distinct (q : Query S n) :
    (distinct q).eval D = (do return (← q.eval D).dedup) := rfl

end Eval

/-- When the join predicate `θ` succeeds on every pair of input rows, the join succeeds and
returns the joined rows of the pairs on which `θ` is `TRUE`, in the order of `rs ×ˢ ss`. -/
theorem eval_join_eq_ok_of_forall {D : Database S} {θ : Expr (n + m)} {q₁ : Query S n}
    {q₂ : Query S m} {rs : List (Row n)} {ss : List (Row m)} (h₁ : q₁.eval D = .ok rs)
    (h₂ : q₂.eval D = .ok ss)
    (hθ : ∀ r ∈ rs, ∀ s ∈ ss, ∃ t, θ.evalTruth (Fin.append r s) = .ok t) :
    (join θ q₁ q₂).eval D =
      .ok (((rs ×ˢ ss).filter fun (r, s) => (θ.evalTruth (Fin.append r s)).toOption = some .true)
        |>.map fun (r, s) => Fin.append r s) := by
  have hall : ∀ t ∈ Row.product rs ss, (θ.evalTruth t).toOption.isSome := by
    intro t ht
    obtain ⟨r, hr, s, hs, rfl⟩ := Row.mem_product.mp ht
    obtain ⟨u, hu⟩ := hθ r hr s hs
    simp [hu]
  rw [eval_join, h₁, h₂, Except.ok_bind, Except.ok_bind, ← Except.toOption_eq_some_iff,
    Expr.toOption_filterRows, ite_eq_left hall, Row.product, List.filter_map]
  rfl

/-! ### Typing and safety -/

/-- The typing context of the query's result rows, if the query is well-typed: `WHERE` and `ON`
predicates are boolean over their input, the expressions of a `SELECT` list are well-typed, and
the inputs of `UNION ALL` have the same types. -/
def typeOf : {n : ℕ} → Query S n → Option (Fin n → SqlType)
  | _, table t => some (S.ctx t)
  | _, select p q => do
    let Γ ← q.typeOf
    if p.typeOf Γ = some .bool then some Γ else none
  | _, project es q => do
    let Γ ← q.typeOf
    if h : ∀ i, ((es i).typeOf Γ).isSome then some fun i => ((es i).typeOf Γ).get (h i)
    else none
  | _, join θ q₁ q₂ => do
    let Γ ← q₁.typeOf
    let Δ ← q₂.typeOf
    if θ.typeOf (Fin.append Γ Δ) = some .bool then some (Fin.append Γ Δ) else none
  | _, unionAll q₁ q₂ => do
    let Γ ← q₁.typeOf
    if q₂.typeOf = some Γ then some Γ else none
  | _, distinct q => q.typeOf

@[simp] theorem typeOf_table (t : S.Table) : (table t).typeOf = some (S.ctx t) := rfl

theorem typeOf_select_eq_some {p : Expr n} {q : Query S n} {Γ : Fin n → SqlType} :
    (select p q).typeOf = some Γ ↔ q.typeOf = some Γ ∧ p.typeOf Γ = some .bool := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h, hp, rfl⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨Γ, h, hp, rfl⟩

theorem typeOf_project_eq_some {es : Fin k → Expr n} {q : Query S n} {Δ : Fin k → SqlType} :
    (project es q).typeOf = some Δ ↔
      ∃ Γ, q.typeOf = some Γ ∧ ∀ i, (es i).typeOf Γ = some (Δ i) := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff]
  refine exists_congr fun Γ => and_congr_right fun _ => ?_
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl i
      simp
    · intro hΔ
      funext i
      simp [hΔ i]
  · simp only [false_iff, not_forall]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact ⟨i, fun h' => hi (by simp [h'])⟩

theorem typeOf_join_eq_some {θ : Expr (n + m)} {q₁ : Query S n} {q₂ : Query S m}
    {Γ' : Fin (n + m) → SqlType} :
    (join θ q₁ q₂).typeOf = some Γ' ↔
      ∃ Γ Δ, q₁.typeOf = some Γ ∧ q₂.typeOf = some Δ ∧
        θ.typeOf (Fin.append Γ Δ) = some .bool ∧ Fin.append Γ Δ = Γ' := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩
    exact ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
  · rintro ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
    exact ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩

theorem typeOf_unionAll_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (unionAll q₁ q₂).typeOf = some Γ ↔ q₁.typeOf = some Γ ∧ q₂.typeOf = some Γ := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

@[simp] theorem typeOf_distinct (q : Query S n) : (distinct q).typeOf = q.typeOf := rfl

/-- Every division in the query's predicates and projections is by a nonzero integer literal. -/
def divSafe : {n : ℕ} → Query S n → Bool
  | _, table _ => true
  | _, select p q => p.divSafe && q.divSafe
  | _, project es q => decide (∀ i, (es i).divSafe) && q.divSafe
  | _, join θ q₁ q₂ => θ.divSafe && q₁.divSafe && q₂.divSafe
  | _, unionAll q₁ q₂ => q₁.divSafe && q₂.divSafe
  | _, distinct q => q.divSafe

/-- The query is well-typed and every division in it is by a nonzero literal; then it succeeds
on every conforming instance (`Query.IsSafe.exists_eval_eq_ok`). -/
def IsSafe (q : Query S n) : Prop := q.typeOf.isSome ∧ q.divSafe

instance (q : Query S n) : Decidable q.IsSafe :=
  inferInstanceAs (Decidable (q.typeOf.isSome ∧ q.divSafe))

/-- Type soundness: on a conforming instance, a well-typed query returns rows of its type, or
divides by zero, which requires a division that is not `divSafe`. -/
theorem eval_ok_or_divisionByZero {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) :
    (∃ rs, q.eval D = .ok rs ∧ ∀ r ∈ rs, r.Conforms Γ) ∨
      (q.eval D = .error .divisionByZero ∧ q.divSafe = false) := by
  induction q with
  | table t =>
    cases hq
    exact .inl ⟨D t, rfl, hD t⟩
  | select p q ih =>
    obtain ⟨hq, hp⟩ := typeOf_select_eq_some.mp hq
    rcases ih hq with ⟨rs, hrs, hconf⟩ | ⟨he, hs⟩
    · rcases Expr.filterRows_ok_or_divisionByZero hconf hp with ⟨rs', h, hsub⟩ | ⟨h, hs⟩
      · exact .inl ⟨rs', by simp [eval_select, hrs, h], fun r hr => hconf r (hsub r hr)⟩
      · exact .inr ⟨by simp [eval_select, hrs, h], by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_select, he], by simp [divSafe, hs]⟩
  | project es q ih =>
    obtain ⟨Γ₀, hq, hes⟩ := typeOf_project_eq_some.mp hq
    rcases ih hq with ⟨rs, hrs, hconf⟩ | ⟨he, hs⟩
    · rcases h : rs.mapM (Expr.evalRow es) with e | ds
      · obtain ⟨r, hr, he⟩ := Except.exists_mem_eq_error_of_mapM_eq_error h
        rcases Expr.evalRow_ok_or_divisionByZero (hconf r hr) hes with ⟨d, hd, -⟩ | ⟨hd, i, hi⟩
        · simp [hd] at he
        · rw [he, Except.error.injEq] at hd
          refine .inr ⟨by simp [eval_project, hrs, h, hd], ?_⟩
          simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
          exact .inl ⟨i, by simp [hi]⟩
      · refine .inl ⟨ds, by simp [eval_project, hrs, h], fun d hd => ?_⟩
        have h' := congrArg Except.toOption h
        rw [Except.toOption_mapM] at h'
        split_ifs at h' with hall
        · simp only [Except.toOption_ok, Option.some.injEq] at h'
          obtain ⟨r, hr, hrd⟩ := List.mem_filterMap.mp (h' ▸ hd)
          rcases Expr.evalRow_ok_or_divisionByZero (hconf r hr) hes with ⟨d', hd', hd'Δ⟩ | ⟨hd', -⟩
          · rw [hd', Except.toOption_ok, Option.some.injEq] at hrd
            exact hrd ▸ hd'Δ
          · simp [hd'] at hrd
        · simp at h'
    · exact .inr ⟨by simp [eval_project, he], by simp [divSafe, hs]⟩
  | join θ q₁ q₂ ih₁ ih₂ =>
    obtain ⟨Γ₁, Γ₂, h₁, h₂, hθ, rfl⟩ := typeOf_join_eq_some.mp hq
    rcases ih₁ h₁ with ⟨rs, hrs, hconf₁⟩ | ⟨he, hs⟩
    · rcases ih₂ h₂ with ⟨ss, hss, hconf₂⟩ | ⟨he, hs⟩
      · have hconf : ∀ t ∈ Row.product rs ss, t.Conforms (Fin.append Γ₁ Γ₂) :=
          fun _ => Row.conforms_of_mem_product hconf₁ hconf₂
        rcases Expr.filterRows_ok_or_divisionByZero hconf hθ with ⟨ts, h, hsub⟩ | ⟨h, hs⟩
        · exact .inl ⟨ts, by simp [eval_join, hrs, hss, h], fun t ht => hconf t (hsub t ht)⟩
        · exact .inr ⟨by simp [eval_join, hrs, hss, h], by simp [divSafe, hs]⟩
      · exact .inr ⟨by simp [eval_join, hrs, he], by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_join, he], by simp [divSafe, hs]⟩
  | unionAll q₁ q₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := typeOf_unionAll_eq_some.mp hq
    rcases ih₁ h₁ with ⟨rs, hrs, hconf₁⟩ | ⟨he, hs⟩
    · rcases ih₂ h₂ with ⟨ss, hss, hconf₂⟩ | ⟨he, hs⟩
      · refine .inl ⟨rs ++ ss, by simp [eval_unionAll, hrs, hss, pure, Except.pure], ?_⟩
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hconf₁ r hr
        · exact hconf₂ r hr
      · exact .inr ⟨by simp [eval_unionAll, hrs, he], by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_unionAll, he], by simp [divSafe, hs]⟩
  | distinct q ih =>
    rcases ih hq with ⟨rs, hrs, hconf⟩ | ⟨he, hs⟩
    · exact .inl ⟨rs.dedup, by simp [eval_distinct, hrs, pure, Except.pure],
        fun r hr => hconf r (List.mem_dedup.mp hr)⟩
    · exact .inr ⟨by simp [eval_distinct, he], by simp [divSafe, hs]⟩

/-- A well-typed query never raises a type error on a conforming instance. -/
theorem eval_ne_typeMismatch {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) : q.eval D ≠ .error .typeMismatch := by
  rcases eval_ok_or_divisionByZero hD hq with ⟨rs, h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- The rows of a well-typed query on a conforming instance conform to its type. -/
theorem conforms_of_eval_eq_ok {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) {rs : List (Row n)} (h : q.eval D = .ok rs) :
    ∀ r ∈ rs, r.Conforms Γ := by
  rcases eval_ok_or_divisionByZero hD hq with ⟨rs', h', hconf⟩ | ⟨h', -⟩
  · rw [h, Except.ok.injEq] at h'
    exact h' ▸ hconf
  · simp [h] at h'

/-- A safe query succeeds on every conforming instance. -/
theorem IsSafe.exists_eval_eq_ok {q : Query S n} (hs : q.IsSafe) {D : Database S}
    (hD : D.Conforms) : ∃ rs, q.eval D = .ok rs := by
  obtain ⟨Γ, hΓ⟩ := Option.isSome_iff_exists.mp hs.1
  rcases eval_ok_or_divisionByZero hD hΓ with ⟨rs, h, -⟩ | ⟨-, h⟩
  · exact ⟨rs, h⟩
  · simp [hs.2] at h

end Query

end Cslib.SQL
