/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Streaming.Frequency
public import CslibFrontier.Languages.SQL.Query

/-!
# Equijoin row counts are join sizes

An equijoin `q₁ JOIN q₂ ON q₁.i = q₂.j` pairs the rows of its inputs whose key columns are equal.
Its predicate is `Expr.eqCols i j` (in `Cslib.SQL.Query`), which compares column `i` of the left
input with column `j` of the right one in the joined row. This module connects SQL evaluation of
such a join to the join size of the streaming library,
`Cslib.Streaming.joinSize u v = ∑ₐ count a u · count a v`: the number of rows an equijoin returns
is the join size of the lists of key values of its inputs.

The key domain is the non-null values of one SQL type `τ`, on which `=` is `TRUE` exactly for
equal values (`Expr.evalTruth_eqCols_eq_ok_true_iff`). A `NULL` key matches nothing, not even
another `NULL`, because `NULL = NULL` is `unknown` and `ON` keeps only `TRUE` pairs. The faithful
count therefore drops the `NULL` keys first: `joinSize (rs.filterMap (· i)) (ss.filterMap (· j))`,
where `(· i) : Row n → Option Value` reads the key and `filterMap` keeps only the non-null ones
(`Query.eval_join_eqCols_length_eq_joinSize_filterMap`). Counting with structural equality of
datums, `joinSize (rs.map (· i)) (ss.map (· j))`, would also pair `NULL` with `NULL`; it gives the
same count when one input has no `NULL` key (`Query.eval_join_eqCols_length_eq_joinSize`).
On a conforming instance, a well-typed query, and in particular a table, supplies the typing
hypothesis by itself (`Query.eval_join_eqCols_length_eq_joinSize_filterMap_of_typeOf`,
`Query.eval_join_table_eqCols_length_eq_joinSize_filterMap`).

The count itself needs no typing hypothesis: whenever the equijoin succeeds, its rows number the
join size of the non-null keys (`Query.length_eq_joinSize_filterMap_of_eval_join_eqCols_eq_ok`),
which applies `Cslib.Streaming.length_filter_product_eq_joinSize_filterMap` once. The typing
hypothesis of the other forms guarantees success (`Query.eval_join_eq_ok_of_forall`); without it
the join may fail, for instance on an integer key compared with a text key.

It adapts and redesigns material from `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell, whose
joins compared name-addressed columns at run time; the connection to join sizes is new.

## Main results

* `Cslib.SQL.Query.length_eq_joinSize_filterMap_of_eval_join_eqCols_eq_ok`: whenever an equijoin
  succeeds, it returns as many rows as the join size of the inputs' non-null keys.
* `Cslib.SQL.Query.eval_join_eqCols_length_eq_joinSize_filterMap`: an equijoin on keys of one type
  succeeds and returns as many rows as the join size of the inputs' non-null keys.
* `Cslib.SQL.Query.eval_join_eqCols_length_eq_joinSize`: the same count with `NULL` treated as a
  value, when one input has no `NULL` key.
* `Cslib.SQL.Query.eval_join_eqCols_length_eq_joinSize_filterMap_of_typeOf`,
  `Cslib.SQL.Query.eval_join_table_eqCols_length_eq_joinSize_filterMap`: on a conforming instance,
  for well-typed inputs and for tables, with key columns of the same declared type.
-/

public section

namespace Cslib.SQL

open Cslib.Streaming

variable {n m : ℕ}

namespace Query

variable {S : DbSchema} {q₁ : Query S n} {q₂ : Query S m} {D : Database S} {rs : List (Row n)}
  {ss : List (Row m)}

/-- **Equijoin row counts are join sizes, whenever the join succeeds.** If `q₁` and `q₂` evaluate
to `rs` and `ss` and the equijoin `q₁ JOIN q₂ ON q₁.i = q₂.j` succeeds with `ts`, then `ts` has
`joinSize (rs.filterMap (· i)) (ss.filterMap (· j))` rows: the join size of the non-null keys of
both inputs. No typing hypothesis is needed, since a key comparison that fails fails the join. A
`NULL` key matches nothing, since SQL's `=` is `unknown` on `NULL`; on non-null values `=` is
`TRUE` exactly on equal values. -/
theorem length_eq_joinSize_filterMap_of_eval_join_eqCols_eq_ok {i : Fin n} {j : Fin m}
    {ts : List (Row (n + m))} (h₁ : q₁.eval D = .ok rs) (h₂ : q₂.eval D = .ok ss)
    (h : (join (Expr.eqCols i j) q₁ q₂).eval D = .ok ts) :
    ts.length = joinSize (rs.filterMap (· i)) (ss.filterMap (· j)) := by
  have h' := congrArg Except.toOption h
  rw [eval_join, h₁, h₂, Except.ok_bind, Except.ok_bind, Expr.toOption_filterRows] at h'
  split_ifs at h'
  · rw [Except.toOption_ok, Option.some.injEq] at h'
    rw [← h', Row.product, List.filter_map, List.length_map,
      ← length_filter_product_eq_joinSize_filterMap]
    refine congrArg List.length (List.filter_congr fun (r, s) _ => decide_eq_decide.mpr ?_)
    dsimp only
    rw [Except.toOption_eq_some_iff, Expr.evalTruth_eqCols_eq_ok_true_iff]
  · exact absurd h' (by simp)

/-- **Equijoin row counts are join sizes.** If `q₁` and `q₂` evaluate to `rs` and `ss`, and the
key columns `i` and `j` hold `NULL` or values of one type `τ`, then the equijoin
`q₁ JOIN q₂ ON q₁.i = q₂.j` succeeds and returns `joinSize (rs.filterMap (· i))
(ss.filterMap (· j))` rows: the join size of the non-null keys of both inputs. The typing
hypothesis gives success; `Query.length_eq_joinSize_filterMap_of_eval_join_eqCols_eq_ok` gives the
count. -/
theorem eval_join_eqCols_length_eq_joinSize_filterMap (i : Fin n) (j : Fin m)
    (h₁ : q₁.eval D = .ok rs) (h₂ : q₂.eval D = .ok ss) {τ : SqlType}
    (hrs : ∀ r ∈ rs, (r i).HasType τ) (hss : ∀ s ∈ ss, (s j).HasType τ) :
    ∃ ts, (join (Expr.eqCols i j) q₁ q₂).eval D = .ok ts ∧
      ts.length = joinSize (rs.filterMap (· i)) (ss.filterMap (· j)) := by
  have h := eval_join_eq_ok_of_forall (θ := Expr.eqCols i j) h₁ h₂ fun r hr s hs => by
    rw [Expr.evalTruth_eqCols]
    exact CmpOp.exists_eval_eq_ok (hrs r hr) (hss s hs)
  exact ⟨_, h, length_eq_joinSize_filterMap_of_eval_join_eqCols_eq_ok h₁ h₂ h⟩

/-- **Equijoin row counts with `NULL` as a value.** Under the hypotheses of
`Query.eval_join_eqCols_length_eq_joinSize_filterMap`, if one of the inputs has no `NULL` key,
the equijoin returns `joinSize (rs.map (· i)) (ss.map (· j))` rows: comparing the keys as datums,
with `NULL` equal to `NULL`, counts the same pairs. When both inputs have a `NULL` key, it also
counts the pairs of `NULL` keys, which the join does not return. -/
theorem eval_join_eqCols_length_eq_joinSize (i : Fin n) (j : Fin m)
    (h₁ : q₁.eval D = .ok rs) (h₂ : q₂.eval D = .ok ss) {τ : SqlType}
    (hrs : ∀ r ∈ rs, (r i).HasType τ) (hss : ∀ s ∈ ss, (s j).HasType τ)
    (hnull : (∀ r ∈ rs, r i ≠ none) ∨ ∀ s ∈ ss, s j ≠ none) :
    ∃ ts, (join (Expr.eqCols i j) q₁ q₂).eval D = .ok ts ∧
      ts.length = joinSize (rs.map (· i)) (ss.map (· j)) := by
  obtain ⟨ts, h, hlen⟩ := eval_join_eqCols_length_eq_joinSize_filterMap i j h₁ h₂ hrs hss
  refine ⟨ts, h, ?_⟩
  rw [hlen, ← length_filter_product_eq_joinSize_filterMap, ← length_filter_product_eq_joinSize]
  refine congrArg List.length (List.filter_congr fun (r, s) hrs' => decide_eq_decide.mpr ?_)
  obtain ⟨hr, hs⟩ := List.mem_product.mp hrs'
  have hne : r i ≠ none ∨ s j ≠ none := hnull.imp (· r hr) (· s hs)
  cases hri : r i <;> cases hsj : s j <;> simp_all [eq_comm]

/-- **Equijoin row counts for well-typed inputs.** On a conforming instance, if `q₁` and `q₂` are
well-typed, their key columns `i` and `j` have the same type, and both evaluate successfully, the
equijoin returns as many rows as the join size of their non-null keys. -/
theorem eval_join_eqCols_length_eq_joinSize_filterMap_of_typeOf (i : Fin n) (j : Fin m)
    (hD : D.Conforms) {Γ : Fin n → SqlType} {Δ : Fin m → SqlType} (hq₁ : q₁.typeOf = some Γ)
    (hq₂ : q₂.typeOf = some Δ) (hτ : Γ i = Δ j)
    (h₁ : q₁.eval D = .ok rs) (h₂ : q₂.eval D = .ok ss) :
    ∃ ts, (join (Expr.eqCols i j) q₁ q₂).eval D = .ok ts ∧
      ts.length = joinSize (rs.filterMap (· i)) (ss.filterMap (· j)) :=
  eval_join_eqCols_length_eq_joinSize_filterMap i j h₁ h₂
    (fun r hr => conforms_of_eval_eq_ok hD hq₁ h₁ r hr i)
    (fun s hs => hτ ▸ conforms_of_eval_eq_ok hD hq₂ h₂ s hs j)

/-- **Equijoin row counts for tables.** On a conforming instance `D`, the equijoin of tables `t₁`
and `t₂` on key columns `i` and `j` declared with the same type returns
`joinSize ((D t₁).filterMap (· i)) ((D t₂).filterMap (· j))` rows. -/
theorem eval_join_table_eqCols_length_eq_joinSize_filterMap {t₁ t₂ : S.Table}
    (i : Fin (S.arity t₁)) (j : Fin (S.arity t₂)) (hD : D.Conforms) (hτ : S.ctx t₁ i = S.ctx t₂ j) :
    ∃ ts, (join (Expr.eqCols i j) (table t₁) (table t₂)).eval D = .ok ts ∧
      ts.length = joinSize ((D t₁).filterMap (· i)) ((D t₂).filterMap (· j)) :=
  eval_join_eqCols_length_eq_joinSize_filterMap_of_typeOf i j hD (typeOf_table t₁)
    (typeOf_table t₂) hτ (eval_table D t₁) (eval_table D t₂)

end Query

end Cslib.SQL
