/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.SQL.QueryLaws
public import CslibFrontierTests.Languages.SQL.Query

/-! Checked uses of the SQL query laws on the schema and instance of
`CslibFrontierTests.SQL.Query`, through ordinary imports: each law applied to a concrete query with
its side conditions discharged by `decide`, and, for each side condition, a concrete instance on
which the law fails without it. -/

public section

namespace CslibFrontierTests.SQL.QueryLaws

open Cslib.SQL Cslib.SQL.Query CslibFrontierTests.SQL.Query
open Cslib.SQL.Expr (col lit unary binary)

/-- A query that succeeds on an instance and one that fails there are not equivalent, at any
level. -/
theorem not_equiv_of_toOption {n : ℕ} {ℓ : EquivLevel} {q₁ q₂ : Query S n} {rs : List (Row n)}
    (h₁ : (q₁.eval D).toOption = some rs) (h₂ : (q₂.eval D).toOption = none) :
    ¬Equiv ℓ q₁ q₂ := fun h => by
  have h' := h D hD
  rw [h₁, h₂] at h'
  exact Option.not_rel_some_none h'

/-- `dept / 0 = 1`: well-typed but unsafe, and failing on every employee with a department. -/
abbrev divZeroEq : Expr 2 := binary (.cmp .eq) (binary (.arith .div) (col 1) (int 0)) (int 1)

/-- The typing contexts of `emp` and `dept`. -/
abbrev Γemp : Fin 2 → SqlType := S.ctx T.emp
abbrev Γdept : Fin 2 → SqlType := S.ctx T.dept

example : ¬divZeroEq.IsSafePredicate Γemp := by decide

/-! ### Selections -/

-- `WHERE dept = 1` then `WHERE name = 'ann'` is one `WHERE dept = 1 AND name = 'ann'`.
example : Equiv .ordered (select isAnn (select isOne emp)) (select (binary .and isOne isAnn) emp) :=
  select_select rfl (by decide) isOne

-- Without safety of the outer predicate: the inner `WHERE FALSE` keeps nothing, so the left side
-- never evaluates `dept / 0`, while the conjunction evaluates it on every row.
example : ¬Equiv .set (select divZeroEq (select (lit (.bool false)) emp))
    (select (binary .and (lit (.bool false)) divZeroEq) emp) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

example : Equiv .ordered (select isAnn (select isOne emp)) (select isOne (select isAnn emp)) :=
  select_comm rfl (by decide) (by decide)

-- Without safety of the inner predicate: `WHERE dept / 0 = 1` fails on `emp`, while after the
-- exchange `WHERE FALSE` leaves it no row to fail on.
example : ¬Equiv .set (select (lit (.bool false)) (select divZeroEq emp))
    (select divZeroEq (select (lit (.bool false)) emp)) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- Without safety of the outer predicate: the same two queries, exchanged.
example : ¬Equiv .set (select divZeroEq (select (lit (.bool false)) emp))
    (select (lit (.bool false)) (select divZeroEq emp)) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

/-- `SELECT dept, dept + 1 FROM emp`. -/
abbrev deptSucc : Fin 2 → Expr 2 := ![col 1, binary (.arith .add) (col 1) (int 1)]

-- `SELECT * FROM (SELECT dept, dept + 1 FROM emp) WHERE col 1 > 1` filters `emp` by
-- `dept + 1 > 1`, the predicate with the projection substituted.
example : Equiv .ordered (select (binary (.cmp .gt) (col 1) (int 1)) (project deptSucc emp))
    (project deptSucc (select (binary (.cmp .gt) (binary (.arith .add) (col 1) (int 1)) (int 1))
      emp)) :=
  select_project (es := deptSucc) rfl (by decide) _

-- Without safety of the projection: the left side evaluates `dept / 0` on every row, the right
-- side only on the rows that `WHERE FALSE` keeps.
example : ¬Equiv .set (select (lit (.bool false)) (project ![divZeroEq] emp))
    (project ![divZeroEq] (select ((lit (.bool false)).subst ![divZeroEq]) emp)) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- Pushing `name = 'ann'` into the left input of `emp JOIN dept ON emp.dept = dept.id`, and
-- `id = 1` into the right input.
example : Equiv .ordered (select (isAnn.rename (Fin.castAdd 2)) empDept)
    (join (binary (.cmp .eq) (col 1) (col 2)) (select isAnn emp) dept) :=
  select_join_left (Γ := Γemp) (Δ := Γdept) rfl rfl (by decide) (by decide)

/-- `id = 1` over `dept`. -/
abbrev idOne : Expr 2 := binary (.cmp .eq) (col 0) (int 1)

example : Equiv .ordered (select (idOne.rename (Fin.natAdd 2)) empDept)
    (join (binary (.cmp .eq) (col 1) (col 2)) emp (select idOne dept)) :=
  select_join_right (Γ := Γemp) (Δ := Γdept) rfl rfl (by decide) (by decide)

/-- `id / 0 = 1` over `dept`: unsafe, and failing on every department. -/
abbrev idDivZeroEq : Expr 2 := binary (.cmp .eq) (binary (.arith .div) (col 0) (int 0)) (int 1)

-- Without safety of the pushed predicate: joined with the empty table, the left side evaluates
-- nothing, while the pushed `WHERE` evaluates `dept / 0` on every employee.
example : ¬Equiv .set (select (divZeroEq.rename (Fin.castAdd 2))
      (join (binary (.cmp .eq) (col 1) (col 2)) emp empty))
    (join (binary (.cmp .eq) (col 1) (col 2)) (select divZeroEq emp) empty) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

-- The same for the right input: joined with the empty table on the left by `ON x = id`, a safe
-- predicate, the left side evaluates nothing, while the pushed `WHERE` evaluates `id / 0` on every
-- department.
example : (binary (.cmp .eq) (col 0) (col 2) : Expr 4).IsSafePredicate
    (Fin.append (S.ctx T.empty) Γdept) := by decide
example : ¬Equiv .set (select (idDivZeroEq.rename (Fin.natAdd 2))
      (join (binary (.cmp .eq) (col 0) (col 2)) empty dept))
    (join (binary (.cmp .eq) (col 0) (col 2)) empty (select idDivZeroEq dept)) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

-- Without safety of the join predicate: pushing `WHERE FALSE` into the left input leaves no pair
-- for `ON dept / 0 = 1` to fail on.
example : ¬Equiv .set (select ((lit (.bool false)).rename (Fin.castAdd 2))
      (join (divZeroEq.rename (Fin.castAdd 2)) emp dept))
    (join (divZeroEq.rename (Fin.castAdd 2)) (select (lit (.bool false)) emp) dept) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- The same for the right input: pushing `WHERE FALSE` into `dept` leaves no pair for
-- `ON dept / 0 = 1` to fail on.
example : ¬Equiv .set (select ((lit (.bool false)).rename (Fin.natAdd 2))
      (join (divZeroEq.rename (Fin.castAdd 2)) emp dept))
    (join (divZeroEq.rename (Fin.castAdd 2)) emp (select (lit (.bool false)) dept)) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- A `WHERE` over a cross join is the inner join.
example : Equiv .ordered
    (select (binary (.cmp .eq) (col 1) (col 2)) (join (lit (.bool true)) emp dept)) empDept :=
  select_join_true _ _ _

/-! ### Projections -/

-- `SELECT 2 * c0 FROM (SELECT dept, name FROM emp)` is `SELECT 2 * dept FROM emp`.
example : Equiv .ordered
    (project ![binary (.arith .mul) (col 0) (int 2)] (project ![col 1, col 0] emp))
    (project ![binary (.arith .mul) (col 1) (int 2)] emp) := by
  have h := project_project (q := emp) (g := ![col 1, col 0]) rfl (by decide)
    ![binary (.arith .mul) (col 0) (int 2)]
  have hf : (fun j => (![binary (.arith .mul) (col 0) (int 2)] j).subst ![col 1, col 0]) =
      (![binary (.arith .mul) (col 1) (int 2)] : Fin 1 → Expr 2) := by
    decide
  rwa [hf] at h

-- Without safety of the inner projection: the outer projection does not use it, so the fused
-- projection never evaluates `dept / 0`.
example : ¬Equiv .set (project ![int 1] (project ![divZeroEq] emp))
    (project (fun j => (![int 1] j).subst ![divZeroEq]) emp) := by
  refine fun h => not_equiv_of_toOption (ℓ := .set)
    (rs := [![some (.int 1)], ![some (.int 1)], ![some (.int 1)], ![some (.int 1)]]) ?_ ?_ h.symm
  <;> decide

example : Equiv .ordered (project Expr.col emp) emp := project_col emp

/-! ### `UNION ALL` -/

example : Equiv .ordered (select isOne (unionAll emp noDept))
    (unionAll (select isOne emp) (select isOne noDept)) :=
  select_unionAll _ _ _

example : Equiv .ordered (project ![col 0] (unionAll emp noDept))
    (unionAll (project ![col 0] emp) (project ![col 0] noDept)) :=
  project_unionAll _ _ _

example :
    Equiv .ordered (unionAll (unionAll emp noDept) emp) (unionAll emp (unionAll noDept emp)) :=
  unionAll_assoc _ _ _

-- Commutativity holds for bags; `CslibFrontierTests.SQL.Query` checks that it fails for lists.
example : Equiv .bag (unionAll emp noDept) (unionAll noDept emp) := unionAll_comm _ _

/-! ### Joins -/

/-- `dept JOIN emp ON dept.id = emp.dept`, with the columns put back in the order of `empDept`. -/
abbrev deptEmp : Query S 4 :=
  project (fun i => col (finAddFlip (m := 2) (n := 2) i))
    (join ((binary (.cmp .eq) (col 1) (col 2)).rename (finAddFlip (m := 2) (n := 2))) dept emp)

example : Equiv .bag empDept deptEmp := join_comm _ _ _

-- The join predicate after the exchange compares the same columns.
example : ((binary (.cmp .eq) (col 1) (col 2) : Expr 4).rename (finAddFlip (m := 2) (n := 2))) =
    binary (.cmp .eq) (col 3) (col 0) := by
  decide

-- The pairs come in another order, so the two joins are not equal as lists.
example : ¬Equiv .ordered empDept deptEmp := by
  rw [equiv_ordered_iff]
  intro h
  exact absurd (h D hD) (by decide)

/-! ### `DISTINCT` -/

example :
    Equiv .ordered (distinct (distinct (project ![col 1] emp))) (distinct (project ![col 1] emp)) :=
  distinct_distinct _

example : Equiv .ordered (distinct (unionAll noDept noDept)) (distinct noDept) :=
  distinct_unionAll_self _

-- `WHERE` commutes with `DISTINCT` over a query with repeated rows, with no condition: an unsafe
-- predicate such as `dept / 0 = 1` fails on both sides alike.
example : Equiv .ordered (select isOne (distinct (unionAll emp emp)))
    (distinct (select isOne (unionAll emp emp))) :=
  select_distinct _ _

example : ((select divZeroEq (distinct emp)).eval D).toOption = none ∧
    ((distinct (select divZeroEq emp)).eval D).toOption = none := by
  decide

/-! ### Congruence in the expression arguments -/

/-- `AND` has the same observations in either order. -/
theorem and_comm_toOption (a b : Datum) :
    (evalBinOp .and a b).toOption = (evalBinOp .and b a).toOption := by
  rw [evalBinOp_and_comm]

-- Commuting an `AND` inside a `SELECT` list: the input's typing hypothesis is `rfl` for a table
-- and `decide` for a derived table.
example : Equiv .bag (project ![binary .and isOne isAnn] emp)
    (project ![binary .and isAnn isOne] emp) :=
  Equiv.project_expr (Γ := Γemp) rfl
    (Fin.forall_fin_one.mpr (Expr.Equiv.binary_comm and_comm_toOption _ _))

example : Equiv .ordered (project ![binary .and isOne isAnn] (select isOne emp))
    (project ![binary .and isAnn isOne] (select isOne emp)) :=
  Equiv.project_expr (Γ := Γemp) (by decide)
    (Fin.forall_fin_one.mpr (Expr.Equiv.binary_comm and_comm_toOption _ _))

-- Commuting an `AND` in a join predicate, in the joined typing context.
example : Equiv .set (join (binary .and (binary (.cmp .eq) (col 1) (col 2)) (isAnn.rename
      (Fin.castAdd 2))) emp dept)
    (join (binary .and (isAnn.rename (Fin.castAdd 2)) (binary (.cmp .eq) (col 1) (col 2)))
      emp dept) :=
  Equiv.join_expr (Γ := Γemp) (Δ := Γdept) rfl rfl (Expr.Equiv.binary_comm and_comm_toOption _ _)

-- Levels form a linear order, so `Query.Equiv.mono` composes with order lemmas.
example (q₁ q₂ : Query S 2) (h : Equiv .bag q₁ q₂) : Equiv .bag q₁ q₂ := h.mono le_rfl
example (q₁ q₂ : Query S 2) (h : Equiv .ordered q₁ q₂) : Equiv .set q₁ q₂ :=
  h.mono (le_trans (EquivLevel.ordered_le .bag) (by decide))

end CslibFrontierTests.SQL.QueryLaws
