/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.SQL.JoinSize
public import CslibFrontier.Languages.SQL.QueryLaws

/-! Checked examples for the equijoin row count and for a rewrite of a concrete query, through
ordinary imports. Each count is checked twice: by evaluating the query, and by the theorem
`Query.eval_join_table_eqCols_length_eq_joinSize_filterMap`, whose `joinSize` is evaluated by
`decide`. The examples cover duplicate keys, an empty input, `NULL` keys (contrasted with the
count under structural equality of datums, and with the null-safe join that realizes it), and a
key type mismatch, which shows that the typing hypothesis cannot be dropped. The rewrite of a
`WHERE` clause through a derived table is an instance of `Query.select_project`, whose safety guard
is checked by `decide`, and an unsafe instance of the same rewrite changes the result. -/

public section

namespace CslibFrontierTests.SQL.JoinSize

open Cslib.SQL Cslib.SQL.Query Cslib.Streaming
open Cslib.SQL.Expr (col lit unary binary eqCols)

/-- The tables of the test schema. -/
inductive T where
  | l
  | r
  | words
  deriving DecidableEq

instance : Fintype T where
  elems := {.l, .r, .words}
  complete t := by cases t <;> decide

/-- `l(k int, tag text)`, `r(k int, tag text)` and `words(w text, tag text)`. -/
abbrev S : DbSchema where
  Table := T
  arity _ := 2
  columns
    | .l => ![⟨some "l", "k", .int⟩, ⟨some "l", "tag", .text⟩]
    | .r => ![⟨some "r", "k", .int⟩, ⟨some "r", "tag", .text⟩]
    | .words => ![⟨some "words", "w", .text⟩, ⟨some "words", "tag", .text⟩]

/-- The row `(k, tag)` with a non-null integer key. -/
abbrev row (k : ℤ) (tag : String) : Row 2 := ![some (.int k), some (.text tag)]

/-- The row `(NULL, tag)`. -/
abbrev nullRow (tag : String) : Row 2 := ![none, some (.text tag)]

/-- The integer literal `z`. -/
abbrev int {n : ℕ} (z : ℤ) : Expr n := lit (.int z)

/-- `l JOIN r ON l.k = r.k`. -/
abbrev lr : Query S 4 := join (eqCols (0 : Fin 2) (0 : Fin 2)) (table T.l) (table T.r)

/-! ### Duplicate keys -/

/-- Keys `1, 1, 1, 2` against `1, 1, 3`: each of the three left rows with key `1` meets both
right rows with key `1`, and nothing else matches, so the join has `3 · 2 = 6` rows. -/
abbrev D : Database S
  | T.l => [row 1 "a", row 1 "b", row 1 "c", row 2 "d"]
  | T.r => [row 1 "x", row 1 "y", row 3 "z"]
  | T.words => [![some (.text "1"), some (.text "w")]]

theorem hD : D.Conforms := by decide

-- By evaluation.
example : (lr.eval D).toOption.map List.length = some 6 := by decide

-- By the theorem, for this instance: the join size of the key lists.
example : (D T.l).filterMap (· 0) = [.int 1, .int 1, .int 1, .int 2] := by decide
example : ∃ ts, lr.eval D = .ok ts ∧ ts.length = 6 := by
  obtain ⟨ts, h, hlen⟩ := eval_join_table_eqCols_length_eq_joinSize_filterMap
    (t₁ := T.l) (t₂ := T.r) 0 0 hD rfl
  exact ⟨ts, h, hlen.trans (by decide)⟩

-- No key is `NULL`, so the structural count agrees.
example : ∃ ts, lr.eval D = .ok ts ∧ ts.length = joinSize ((D T.l).map (· 0)) ((D T.r).map (· 0)) :=
  eval_join_eqCols_length_eq_joinSize 0 0 (eval_table D T.l) (eval_table D T.r)
    (fun r hr => hD T.l r hr 0) (fun s hs => hD T.r s hs 0) (.inl (by decide))

-- The theorem holds on every conforming instance, without evaluating anything.
example (D' : Database S) (hD' : D'.Conforms) :
    ∃ ts, lr.eval D' = .ok ts ∧
      ts.length = joinSize ((D' T.l).filterMap (· 0)) ((D' T.r).filterMap (· 0)) :=
  eval_join_table_eqCols_length_eq_joinSize_filterMap 0 0 hD' rfl

/-! ### Empty inputs -/

/-- An empty right table. -/
abbrev DEmptyRight : Database S
  | T.l => [row 1 "a", row 1 "b"]
  | _ => []

/-- An empty left table. -/
abbrev DEmptyLeft : Database S
  | T.r => [row 1 "x"]
  | _ => []

example : (lr.eval DEmptyRight).toOption.map List.length = some 0 := by decide
example : (lr.eval DEmptyLeft).toOption.map List.length = some 0 := by decide
example : joinSize ((DEmptyRight T.l).filterMap (· 0)) ((DEmptyRight T.r).filterMap (· 0)) = 0 := by
  decide
example : joinSize ((DEmptyLeft T.l).filterMap (· 0)) ((DEmptyLeft T.r).filterMap (· 0)) = 0 := by
  decide

/-! ### `NULL` keys -/

/-- Keys `1, NULL, NULL, 2` against `NULL, 1, 1`. -/
abbrev DNull : Database S
  | T.l => [row 1 "a", nullRow "b", nullRow "c", row 2 "d"]
  | T.r => [nullRow "x", row 1 "y", row 1 "z"]
  | T.words => []

theorem hDNull : DNull.Conforms := by decide

-- Only the left key `1` matches, twice: `NULL = NULL` is `unknown`, so `NULL` keys match nothing.
example : (lr.eval DNull).toOption.map List.length = some 2 := by decide
example : joinSize ((DNull T.l).filterMap (· 0)) ((DNull T.r).filterMap (· 0)) = 2 := by decide
example : ∃ ts, lr.eval DNull = .ok ts ∧ ts.length = 2 := by
  obtain ⟨ts, h, hlen⟩ := eval_join_table_eqCols_length_eq_joinSize_filterMap
    (t₁ := T.l) (t₂ := T.r) 0 0 hDNull rfl
  exact ⟨ts, h, hlen.trans (by decide)⟩

-- Structural equality of datums would also pair each of the two left `NULL` keys with the right
-- one, counting `2 + 2 = 4`.
example : joinSize ((DNull T.l).map (· 0)) ((DNull T.r).map (· 0)) = 4 := by decide

/-- `NULL` keys only on the left: keys `NULL, 1, NULL` against `1, 1`. -/
abbrev DNullLeft : Database S
  | T.l => [nullRow "a", row 1 "b", nullRow "c"]
  | T.r => [row 1 "x", row 1 "y"]
  | T.words => []

theorem hDNullLeft : DNullLeft.Conforms := by decide

-- The right input has no `NULL` key, so the structural count is right: the `NULL` keys meet no
-- `NULL` on the right, and the join has `1 · 2 = 2` rows.
example : (lr.eval DNullLeft).toOption.map List.length = some 2 := by decide
example : ∃ ts, lr.eval DNullLeft = .ok ts ∧ ts.length = 2 := by
  obtain ⟨ts, h, hlen⟩ := eval_join_eqCols_length_eq_joinSize 0 0 (eval_table DNullLeft T.l)
    (eval_table DNullLeft T.r) (fun r hr => hDNullLeft T.l r hr 0)
    (fun s hs => hDNullLeft T.r s hs 0) (.inr (by decide))
  exact ⟨ts, h, hlen.trans (by decide)⟩

/-- The null-safe predicate `l.k = r.k OR (l.k IS NULL AND r.k IS NULL)`, standard SQL's
`l.k IS NOT DISTINCT FROM r.k`. -/
abbrev nullSafe : Expr 4 :=
  binary .or (eqCols (0 : Fin 2) (0 : Fin 2))
    (binary .and (unary .isNull (col 0)) (unary .isNull (col 2)))

-- The null-safe join realizes the structural count.
example :
    ((join nullSafe (table T.l) (table T.r)).eval DNull).toOption.map List.length = some 4 := by
  decide

/-! ### The typing hypothesis is needed -/

/-- `l JOIN words ON l.k = words.w`, comparing an integer key with a text key. -/
abbrev lw : Query S 4 := join (eqCols (0 : Fin 2) (0 : Fin 2)) (table T.l) (table T.words)

-- The predicate is not safe, and the join is ill-typed …
example :
    ¬(eqCols (0 : Fin 2) (0 : Fin 2)).IsSafePredicate (Fin.append (S.ctx T.l) (S.ctx T.words)) :=
  fun h => absurd (Expr.isSafePredicate_eqCols_iff.mp h) (by decide)
example : lw.typeOf = none := by decide

-- … so on a conforming instance with a non-null key on both sides it fails instead of counting:
-- there are no rows whose number `joinSize` could give.
example : lw.eval D = .error .typeMismatch := rfl

/-- Only `NULL` keys on the left, against a non-null text key. -/
abbrev DNullKeys : Database S
  | T.l => [nullRow "a", nullRow "b"]
  | T.r => []
  | T.words => [![some (.text "1"), some (.text "w")]]

example : DNullKeys.Conforms := by decide

-- A comparison with a `NULL` operand is `unknown`, not a type error, so without a non-null key on
-- the left the join succeeds with no rows.
example : (lw.eval DNullKeys).toOption = some [] := by decide

-- With an empty side nothing is compared, and the join succeeds with no rows.
example : (lw.eval DNull).toOption = some [] := by decide

/-! ### A rewrite through a derived table -/

/-- The `SELECT` list `tag, k + 1` over `l`. -/
abbrev es : Fin 2 → Expr 2 := ![col 1, binary (.arith .add) (col 0) (int 1)]

/-- `k1 = 2` over the derived table `(SELECT tag, k + 1 AS k1 FROM l)`. -/
abbrev p : Expr 2 := binary (.cmp .eq) (col 1) (int 2)

/-- `SELECT * FROM (SELECT tag, k + 1 AS k1 FROM l) WHERE k1 = 2`. -/
abbrev before : Query S 2 := select p (project es (table T.l))

/-- `SELECT tag, k + 1 FROM l WHERE k + 1 = 2`: the predicate is moved below the projection by
substituting the projected expressions for the derived table's columns. -/
abbrev after : Query S 2 := project es (select (p.subst es) (table T.l))

example : p.subst es = binary (.cmp .eq) (binary (.arith .add) (col 0) (int 1)) (int 2) := rfl

/-- The guard of the rewrite: every projected expression is safe over `l`, so it succeeds on every
conforming row. -/
theorem es_safe : ∀ i, (es i).IsSafe (S.ctx T.l) := by decide

/-- The rewrite is an ordered equivalence: on every conforming instance both queries return the
same list of rows. It is an instance of `Query.select_project`, whose guard is `es_safe`. -/
theorem before_equiv_after : Equiv .ordered before after :=
  select_project rfl es_safe p

/-! ### The guard is needed -/

/-- The `SELECT` list `tag, 100 / k`, which divides by a column. -/
abbrev es' : Fin 2 → Expr 2 := ![col 1, binary (.arith .div) (int 100) (col 0)]

/-- `tag = 'x'` over the derived table. -/
abbrev p' : Expr 2 := binary (.cmp .eq) (col 0) (lit (.text "x"))

-- The guard fails: `100 / k` is not safe.
example : ¬(es' 1).IsSafe (S.ctx T.l) := by decide

/-- A row with key `0`, which only the unrewritten query divides by. -/
abbrev DZero : Database S
  | T.l => [row 0 "a", row 5 "x"]
  | _ => []

example : DZero.Conforms := by decide

-- `SELECT * FROM (SELECT tag, 100 / k FROM l) WHERE tag = 'x'` divides by zero on the first row …
example : (select p' (project es' (table T.l))).eval DZero = .error .divisionByZero := rfl

-- … while `SELECT tag, 100 / k FROM l WHERE tag = 'x'` keeps only the second row and succeeds.
example : ((project es' (select (p'.subst es') (table T.l))).eval DZero).toOption =
    some [![some (.text "x"), some (.int 20)]] := by
  decide

end CslibFrontierTests.SQL.JoinSize
