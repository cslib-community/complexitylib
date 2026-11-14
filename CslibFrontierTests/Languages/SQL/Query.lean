/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.SQL.QueryEquiv

/-! Checked examples of SQL queries over a small schema, through ordinary imports: bag semantics,
three-valued `WHERE`, joins with duplicate and `NULL` keys, strict errors, typing and safety, and
the separations between the equivalence levels. Results are compared through `Except.toOption` by
`decide`, since rows are functions and `rfl` cannot compare a computed row with a literal one;
errors are checked by `rfl`. -/

public section

namespace CslibFrontierTests.SQL.Query

open Cslib.SQL Cslib.SQL.Query
open Cslib.SQL.Expr (col lit unary binary inList)

/-- The tables of the test schema. -/
inductive T where
  | emp
  | dept
  | empty
  deriving DecidableEq

instance : Fintype T where
  elems := {.emp, .dept, .empty}
  complete t := by cases t <;> decide

/-- `emp(name text, dept int)`, `dept(id int, title text)` and `empty(x int, y text)`. -/
abbrev S : DbSchema where
  Table := T
  arity _ := 2
  columns
    | .emp => ![⟨some "emp", "name", .text⟩, ⟨some "emp", "dept", .int⟩]
    | .dept => ![⟨some "dept", "id", .int⟩, ⟨some "dept", "title", .text⟩]
    | .empty => ![⟨some "empty", "x", .int⟩, ⟨some "empty", "y", .text⟩]

/-- The integer literal `z`. -/
abbrev int {n : ℕ} (z : ℤ) : Expr n := lit (.int z)

/-- An instance: `ann` occurs twice in `emp`, `cy` has no department, department `1` occurs twice
in `dept` and one department has a `NULL` id; `empty` has no rows. -/
abbrev D : Database S
  | T.emp => [![some (.text "ann"), some (.int 1)], ![some (.text "bob"), some (.int 1)],
      ![some (.text "cy"), none], ![some (.text "ann"), some (.int 1)]]
  | T.dept => [![some (.int 1), some (.text "eng")], ![some (.int 1), some (.text "ops")],
      ![some (.int 2), some (.text "law")], ![none, some (.text "tmp")]]
  | T.empty => []

abbrev emp : Query S 2 := table T.emp
abbrev dept : Query S 2 := table T.dept
abbrev empty : Query S 2 := table T.empty

theorem hD : D.Conforms := by decide

-- An instance with an integer in a text column does not conform.
example : ¬Database.Conforms (S := S) fun
    | T.emp => [![some (.int 0), none]]
    | _ => [] := by
  decide

/-! ### Bags: duplicates are kept, except by `DISTINCT` -/

-- `SELECT dept FROM emp` keeps one row per employee, duplicates and `NULL` included.
example : ((project ![col 1] emp).eval D).toOption =
    some [![some (.int 1)], ![some (.int 1)], ![none], ![some (.int 1)]] := by
  decide

-- `UNION ALL` keeps the duplicates of both sides.
example : ((unionAll (project ![col 1] emp) (project ![col 0] dept)).eval D).toOption =
    some [![some (.int 1)], ![some (.int 1)], ![none], ![some (.int 1)],
      ![some (.int 1)], ![some (.int 1)], ![some (.int 2)], ![none]] := by
  decide

-- `DISTINCT` keeps one copy of each row; the two `NULL` rows are duplicates of each other.
example : ((distinct (unionAll (project ![col 1] emp) (project ![col 0] dept))).eval D).toOption =
    some [![some (.int 1)], ![some (.int 2)], ![none]] := by
  decide

/-! ### `WHERE` keeps only `TRUE` rows -/

-- `WHERE dept NOT IN (2)` drops `cy`, whose `NULL` department makes the predicate `unknown`.
example : ((select (unary .not (inList (col 1) [some (.int 2)])) emp).eval D).toOption =
    some [![some (.text "ann"), some (.int 1)], ![some (.text "bob"), some (.int 1)],
      ![some (.text "ann"), some (.int 1)]] := by
  decide

-- `WHERE dept NOT IN (2, NULL)` keeps nothing: with a `NULL` in the list, `NOT IN` is never
-- `TRUE`.
example : ((select (unary .not (inList (col 1) [some (.int 2), none])) emp).eval D).toOption =
    some [] := by
  decide

/-! ### Schemas do not depend on data -/

-- The empty table has its declared columns, and every query over it is typed from the schema.
example : empty.typeOf = some ![.int, .text] := by decide
example : (empty.eval D).toOption = some [] := by decide
example : (project ![col 1, col 0] empty).typeOf = some ![.text, .int] := by decide

/-! ### Joins -/

/-- `emp JOIN dept ON emp.dept = dept.id`. -/
abbrev empDept : Query S 4 := join (binary (.cmp .eq) (col 1) (col 2)) emp dept

-- Each employee of department `1` meets both rows with id `1`, so the duplicate `ann` row gives
-- two more; `cy`'s `NULL` key and the `NULL` id match nothing.
example : (empDept.eval D).toOption = some
    [![some (.text "ann"), some (.int 1), some (.int 1), some (.text "eng")],
     ![some (.text "ann"), some (.int 1), some (.int 1), some (.text "ops")],
     ![some (.text "bob"), some (.int 1), some (.int 1), some (.text "eng")],
     ![some (.text "bob"), some (.int 1), some (.int 1), some (.text "ops")],
     ![some (.text "ann"), some (.int 1), some (.int 1), some (.text "eng")],
     ![some (.text "ann"), some (.int 1), some (.int 1), some (.text "ops")]] := by
  decide

-- The cross join is `ON TRUE`: all 4 × 4 pairs.
example : ((join (lit (.bool true)) emp dept).eval D).toOption.map List.length = some 16 := by
  decide

example : empDept.typeOf = some ![SqlType.text, .int, .int, .text] := by decide

/-! ### Errors are strict -/

/-- `SELECT dept / 0 FROM t`. -/
abbrev divZero (t : Query S 2) : Query S 1 := project ![binary (.arith .div) (col 1) (int 0)] t

-- The first row divides by zero, so the whole query fails …
example : (divZero emp).eval D = .error .divisionByZero := rfl
-- … while the same query on an empty table evaluates nothing and succeeds.
example : ((divZero empty).eval D).toOption = some [] := by decide

-- An ill-typed predicate fails on a nonempty input: `name` is text, not boolean.
example : (select (col 0) emp).typeOf = none := by decide
example : (select (col 0) emp).eval D = .error .typeMismatch := rfl

/-! ### Typing and safety -/

-- Type soundness: a well-typed query never raises a type error on a conforming instance, and its
-- rows have its types.
example (D' : Database S) (hD' : D'.Conforms) : empDept.eval D' ≠ .error .typeMismatch :=
  eval_ne_typeMismatch hD' (Γ := ![.text, .int, .int, .text]) (by decide)
example (D' : Database S) (hD' : D'.Conforms) {rs : List (Row 4)} (h : empDept.eval D' = .ok rs) :
    ∀ r ∈ rs, r 1 = none ∨ ∃ z, r 1 = some (.int z) := fun r hr => by
  have hr := conforms_of_eval_eq_ok hD' (Γ := ![.text, .int, .int, .text]) (by decide) h r hr 1
  rcases hd : r 1 with _ | v
  · exact .inl rfl
  · rw [hd] at hr
    obtain ⟨z, rfl⟩ := Value.type_eq_int_iff.mp hr
    exact .inr ⟨z, rfl⟩

-- Safety is decidable and syntactic: division by a nonzero literal is safe, by zero it is not.
example : (project ![binary (.arith .div) (col 1) (int 2)] emp).IsSafe := by decide
example : ¬(divZero emp).IsSafe := by decide
example : ¬(divZero empty).IsSafe := by decide

-- A safe query succeeds on every conforming instance.
example (D' : Database S) (hD' : D'.Conforms) : ∃ rs, (empDept.eval D').toOption = some rs := by
  obtain ⟨rs, h⟩ := IsSafe.exists_eval_eq_ok (q := empDept) (by decide) hD'
  exact ⟨rs, by rw [h]; rfl⟩

/-! ### Equivalence levels -/

/-- The employees without a department. -/
abbrev noDept : Query S 2 := select (unary .isNull (col 1)) emp

-- `UNION ALL` in either order gives the same bag …
example : Equiv .bag (unionAll emp noDept) (unionAll noDept emp) := fun D' _ => by
  simp only [eval_unionAll]
  rcases emp.eval D' with _ | rs <;> rcases noDept.eval D' with _ | ss
  exacts [.none, .none, .none, .some List.perm_append_comm]

-- … but not the same list.
example : ¬Equiv .ordered (unionAll emp noDept) (unionAll noDept emp) := by
  rw [equiv_ordered_iff]
  intro h
  exact absurd (h D hD) (by decide)

-- A table and its `UNION ALL` with itself have the same rows …
example : Equiv .set (unionAll emp emp) emp := fun D' _ =>
  .some fun r => by simp only [List.mem_append, or_self]

-- … but not the same multiplicities.
example : ¬Equiv .bag (unionAll emp emp) emp := by
  intro h
  have h' := h D hD
  simp only [eval_unionAll, eval_table, Except.ok_bind] at h'
  exact absurd (Option.rel_some_some.mp h').length_eq (by decide)

-- `DISTINCT` sees only sets, so it makes them bag-equivalent.
example : Equiv .bag (distinct (unionAll emp emp)) (distinct emp) :=
  Equiv.distinct_of_set fun D' _ => .some fun r => by simp only [List.mem_append, or_self]

-- Equivalences compose by `calc` and weaken to coarser levels.
example (q₁ q₂ q₃ : Query S 2) (h₁₂ : Equiv .ordered q₁ q₂) (h₂₃ : Equiv .bag q₂ q₃) :
    Equiv .set q₁ q₃ :=
  (calc Equiv .bag q₁ q₂ := h₁₂.of_ordered
    Equiv .bag _ q₃ := h₂₃).mono (by decide)

/-! ### Congruence -/

/-- `dept = 1` and `name = 'ann'` over `emp`. -/
abbrev isOne : Expr 2 := binary (.cmp .eq) (col 1) (int 1)
abbrev isAnn : Expr 2 := binary (.cmp .eq) (col 0) (lit (.text "ann"))

-- `AND` commutes inside a `WHERE` clause: the expression law lifts to queries over a well-typed
-- input, at every level.
example :
    Equiv .ordered (select (binary .and isOne isAnn) emp) (select (binary .and isAnn isOne) emp) :=
  Equiv.select_expr (Γ := S.ctx T.emp) rfl
    (Expr.Equiv.binary_comm (fun a b => by rw [evalBinOp_and_comm]) _ _)

-- Query arguments are congruences without any typing condition.
example (q q' : Query S 2) (h : Equiv .bag q q') :
    Equiv .bag (distinct (select isOne q)) (distinct (select isOne q')) :=
  (h.select isOne).distinct

end CslibFrontierTests.SQL.Query
