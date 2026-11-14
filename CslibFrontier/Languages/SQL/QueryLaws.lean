/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Fin.AddFlip
public import CslibFrontier.Foundations.Data.List.Product
public import CslibFrontier.Languages.SQL.QueryEquiv
-- `List.dedup_filter`
import CslibFrontier.Foundations.Data.List.Dedup
-- `Fin.append_comp_castAdd` and `Fin.append_comp_natAdd`
import Cslib.Computability.Circuit.Composition

/-!
# Proved SQL query transformations

The rewrite laws of the select–project–join–union fragment, each at the strongest equivalence level
that holds (`Cslib.SQL.Query.Equiv`) and with the side conditions that strict evaluation needs.
Evaluation fails as soon as a predicate or projection fails on any row of its input, so a law that
changes the rows on which an expression is evaluated holds only when that evaluation cannot fail.
Its side condition is then the decidable safety check (`Expr.IsSafePredicate`, `Expr.IsSafe`) of
that expression, in the typing context of its input, which must be well-typed (`q.typeOf = some Γ`).
Laws that evaluate every expression on the same rows on both sides need no condition. The tests
show for each condition a concrete instance on which the law fails without it.

* Selections: merge into a conjunction (`Query.select_select`, the outer predicate safe), commute
  (`Query.select_comm`, both safe), move through a projection, as when a `WHERE` over a derived
  table moves into it with the projection substituted (`Query.select_project`, the projection safe),
  and push into either input of a join (`Query.select_join_left`, `Query.select_join_right`, the
  predicate and the join predicate safe); a `WHERE` over a cross join is an inner join
  (`Query.select_join_true`), and `WHERE TRUE` is the identity (`Query.select_true`).
* Projections: fusion by substitution (`Query.project_project`, the inner projection safe) and
  `SELECT *` (`Query.project_col`).
* `UNION ALL`: `WHERE` and `SELECT` lists distribute over it (`Query.select_unionAll`,
  `Query.project_unionAll`), it is associative (`Query.unionAll_assoc`), and it is commutative as a
  bag only (`Query.unionAll_comm`).
* Joins are commutative as bags, exchanging the blocks of columns of the predicate and the result
  through `finAddFlip` (`Query.join_comm`).
* `DISTINCT` is idempotent, absorbs a `UNION ALL` of a query with itself, and commutes with `WHERE`
  (`Query.distinct_distinct`, `Query.distinct_unionAll_self`, `Query.select_distinct`).

All laws are ordered equivalences except the two commutativity laws, which hold for bags only.

It adapts and redesigns the query laws of `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell.
There, a `WHERE` predicate that failed on a row dropped that row, so filter laws needed no
conditions, and pushdown passed column names through derived tables; here a failure fails the
query, each law states the safety condition it needs, and moving a predicate across a derived
table or into a join is explicit substitution or renaming.

## Main results

* `Cslib.SQL.Query.select_select`, `Cslib.SQL.Query.select_comm`: selection merge and
  commutation.
* `Cslib.SQL.Query.select_project`: selection through a projection.
* `Cslib.SQL.Query.select_join_left`, `Cslib.SQL.Query.select_join_right`,
  `Cslib.SQL.Query.select_join_true`: predicate pushdown into joins.
* `Cslib.SQL.Query.select_true`: `WHERE TRUE` keeps every row.
* `Cslib.SQL.Query.project_project`, `Cslib.SQL.Query.project_col`: projection fusion and
  `SELECT *`.
* `Cslib.SQL.Query.select_unionAll`, `Cslib.SQL.Query.project_unionAll`,
  `Cslib.SQL.Query.unionAll_assoc`, `Cslib.SQL.Query.unionAll_comm`: `UNION ALL` laws.
* `Cslib.SQL.Query.join_comm`: join commutativity as bags.
* `Cslib.SQL.Query.distinct_distinct`, `Cslib.SQL.Query.distinct_unionAll_self`,
  `Cslib.SQL.Query.select_distinct`: `DISTINCT` laws.
* `Cslib.SQL.Query.eval_select_of_isSafePredicate`, `Cslib.SQL.Query.eval_join_of_isSafePredicate`:
  a safe `WHERE` or join predicate is a filter.
* `Cslib.SQL.Expr.IsSafePredicate.filterRows_eq_ok`, `Cslib.SQL.Expr.toOption_filterRows_map`,
  `Cslib.SQL.Expr.toOption_evalTruth_and`: what the laws need about `WHERE` on lists of rows.
-/

public section

namespace Cslib.SQL

variable {n m k l : ℕ}

namespace Expr

/-- A safe predicate never makes `WHERE` fail on conforming rows: it keeps the rows on which the
predicate is `TRUE`. -/
theorem IsSafePredicate.filterRows_eq_ok {Γ : Fin n → SqlType} {p : Expr n}
    (hp : p.IsSafePredicate Γ) {rs : List (Row n)} (hrs : ∀ r ∈ rs, r.Conforms Γ) :
    p.filterRows rs = .ok (rs.filter fun r => (p.evalTruth r).toOption = some .true) := by
  have hall : ∀ r ∈ rs, (p.evalTruth r).toOption.isSome := fun r hr => by
    obtain ⟨t, ht⟩ := hp.exists_evalTruth_eq_ok (hrs r hr)
    simp [ht]
  rw [← Except.toOption_eq_some_iff, toOption_filterRows, ite_eq_left hall]

/-- `TRUE` keeps every row. -/
@[simp] theorem filterRows_true (rs : List (Row n)) :
    (lit (.bool true)).filterRows rs = .ok rs := by
  have hall : ∀ r ∈ rs, ((lit (.bool true) : Expr n).evalTruth r).toOption.isSome :=
    fun _ _ => rfl
  rw [← Except.toOption_eq_some_iff, toOption_filterRows, ite_eq_left hall]
  exact congrArg some (List.filter_eq_self.mpr fun _ _ => rfl)

/-- `WHERE` on rows computed by `f` is `WHERE` on their sources with a predicate that reads
through `f`, followed by `f`. -/
theorem toOption_filterRows_map {p : Expr k} {p' : Expr n} {f : Row n → Row k}
    {rs : List (Row n)} (h : ∀ r ∈ rs, p.evalTruth (f r) = p'.evalTruth r) :
    (p.filterRows (rs.map f)).toOption = (p'.filterRows rs).toOption.map (List.map f) := by
  rw [toOption_filterRows, toOption_filterRows]
  have hc : (∀ x ∈ rs.map f, (p.evalTruth x).toOption.isSome) ↔
      ∀ r ∈ rs, (p'.evalTruth r).toOption.isSome := by
    simp only [List.forall_mem_map]
    exact forall₂_congr fun r hr => by rw [h r hr]
  split_ifs with h₁ h₂ h₂
  · rw [Option.map_some, List.filter_map]
    exact congrArg some (congrArg (List.map f) (List.filter_congr fun r hr => by
      simp only [Function.comp_apply, h r hr]))
  · exact absurd (hc.mp h₁) h₂
  · exact absurd (hc.mpr h₂) h₁
  · rfl

/-- `c AND p` as a predicate: both sides are evaluated, and the truth value is their Kleene
conjunction. -/
theorem toOption_evalTruth_and (c p : Expr n) (r : Row n) :
    ((binary .and c p).evalTruth r).toOption =
      (c.evalTruth r).toOption.bind fun s => (p.evalTruth r).toOption.map (s ⊓ ·) := by
  simp only [evalTruth, eval_binary, evalBinOp]
  rcases c.eval r with _ | a
  · rfl
  rcases p.eval r with _ | b <;> rcases ha : a.toTruth with _ | s
  · simp [ha]
  · simp [ha]
  · simp [ha]
  · rcases hb : b.toTruth with _ | t <;> simp [ha, hb, pure, Except.pure]

/-- `WHERE` on two lists one after the other is `WHERE` on their concatenation. -/
theorem toOption_filterRows_append (p : Expr n) (rs ss : List (Row n)) :
    (p.filterRows (rs ++ ss)).toOption =
      (p.filterRows rs).toOption.bind fun a => (p.filterRows ss).toOption.map (a ++ ·) := by
  rw [toOption_filterRows, toOption_filterRows, toOption_filterRows]
  simp only [List.forall_mem_append, List.filter_append]
  by_cases h₁ : ∀ r ∈ rs, (p.evalTruth r).toOption.isSome
  · by_cases h₂ : ∀ r ∈ ss, (p.evalTruth r).toOption.isSome
    · rw [ite_eq_left ⟨h₁, h₂⟩, ite_eq_left h₁, Option.bind_some, ite_eq_left h₂]
      rfl
    · rw [ite_eq_right fun h => h₂ h.2, ite_eq_left h₁, Option.bind_some, ite_eq_right h₂]
      rfl
  · rw [ite_eq_right fun h => h₁ h.1, ite_eq_right h₁]
    rfl

/-- A `SELECT` list depends on the row only through the results of its expressions. -/
theorem evalRow_congr {es : Fin k → Expr n} {es' : Fin k → Expr m} {r : Row n} {r' : Row m}
    (h : ∀ i, (es i).eval r = (es' i).eval r') : evalRow es r = evalRow es' r' := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [evalRow, h 0, ih fun i => h i.succ]

/-- A `SELECT` list of column references reindexes the row. -/
theorem evalRow_col_comp (ρ : Fin k → Fin n) (r : Row n) :
    evalRow (fun i => col (ρ i)) r = .ok (r ∘ ρ) :=
  evalRow_eq_ok_iff.mpr fun _ => rfl

end Expr

namespace Query

variable {S : DbSchema}

open Expr (col lit binary)

/-! ### Selections -/

/-- Selection merge: two successive `WHERE` clauses are one `WHERE` with their conjunction, when
the outer predicate is safe. The conjunction evaluates `p` on rows that the inner `WHERE` drops,
so an unsafe `p` could make only the right side fail. -/
theorem select_select {q : Query S n} {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ)
    {p : Expr n} (hp : p.IsSafePredicate Γ) (c : Expr n) :
    Equiv .ordered (select p (select c q)) (select (binary .and c p) q) := by
  refine equiv_ordered_iff.mpr fun D hD => ?_
  simp only [eval_select]
  rcases h : q.eval D with e | rs
  · rfl
  have hrs := conforms_of_eval_eq_ok hD hq h
  choose t ht using fun r (hr : r ∈ rs) => hp.exists_evalTruth_eq_ok (hrs r hr)
  simp only [Except.ok_bind, Except.toOption_bind, Expr.toOption_filterRows c rs,
    Expr.toOption_filterRows (binary .and c p) rs, Expr.toOption_evalTruth_and]
  by_cases hC : ∀ r ∈ rs, (c.evalTruth r).toOption.isSome
  · have hAnd : ∀ r ∈ rs, ((c.evalTruth r).toOption.bind
        fun s => (p.evalTruth r).toOption.map (s ⊓ ·)).isSome := fun r hr => by
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hC r hr)
      simp [hs, ht r hr]
    rw [ite_eq_left hC, ite_eq_left hAnd, Option.bind_some,
      hp.filterRows_eq_ok fun r hr => hrs r (List.mem_filter.mp hr).1, Except.toOption_ok,
      List.filter_filter]
    refine congrArg some (List.filter_congr fun r hr => ?_)
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hC r hr)
    simp only [hs, ht r hr, Except.toOption_ok, Option.bind_some, Option.map_some,
      Option.some.injEq, Truth.inf_eq_true_iff, Bool.decide_and]
    exact Bool.and_comm _ _
  · have hAnd : ¬∀ r ∈ rs, ((c.evalTruth r).toOption.bind
        fun s => (p.evalTruth r).toOption.map (s ⊓ ·)).isSome := fun hall => hC fun r hr => by
      have := hall r hr
      rcases hs : (c.evalTruth r).toOption <;> simp_all
    rw [ite_eq_right hC, ite_eq_right hAnd]
    rfl

/-- Selection commutation: two safe `WHERE` clauses may be applied in either order. -/
theorem select_comm {q : Query S n} {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ)
    {p c : Expr n} (hp : p.IsSafePredicate Γ) (hc : c.IsSafePredicate Γ) :
    Equiv .ordered (select p (select c q)) (select c (select p q)) :=
  calc Equiv .ordered (select p (select c q)) (select (binary .and c p) q) :=
        select_select hq hp c
    Equiv .ordered _ (select (binary .and p c) q) :=
        Equiv.select_expr hq (Expr.Equiv.binary_comm (fun a b => by rw [evalBinOp_and_comm]) c p)
    Equiv .ordered _ (select c (select p q)) := (select_select hq hc p).symm

/-- Selection through a projection, or a `WHERE` over a derived table: filtering the rows of
`SELECT es FROM q` by `p` is filtering the rows of `q` by `p` with the projection substituted,
then projecting, when the projection is safe. The right side evaluates `es` only on the rows it
keeps, so an unsafe projection could make only the left side fail. -/
theorem select_project {q : Query S n} {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ)
    {es : Fin k → Expr n} (hes : ∀ i, (es i).IsSafe Γ) (p : Expr k) :
    Equiv .ordered (select p (project es q)) (project es (select (p.subst es) q)) := by
  refine equiv_ordered_iff.mpr fun D hD => ?_
  simp only [eval_select, eval_project]
  rcases h : q.eval D with e | rs
  · rfl
  have hrs := conforms_of_eval_eq_ok hD hq h
  choose! d hd using fun r (hr : r ∈ rs) =>
    Expr.exists_evalRow_eq_ok_iff.mpr fun i => (hes i).exists_eval_eq_ok (hrs r hr)
  have hsubst : ∀ r ∈ rs, p.evalTruth (d r) = (p.subst es).evalTruth r := fun r hr => by
    simp only [Expr.evalTruth, Expr.eval_subst (Expr.evalRow_eq_ok_iff.mp (hd r hr))]
  simp only [Except.ok_bind, Except.toOption_bind, Except.mapM_eq_ok_map hd,
    Expr.toOption_filterRows_map hsubst]
  rcases hf : (p.subst es).filterRows rs with e | rs'
  · rfl
  · rw [Except.toOption_ok, Option.map_some, Option.bind_some,
      Except.mapM_eq_ok_map fun r hr => hd r (Expr.mem_of_filterRows_eq_ok hf hr)]
    rfl

/-- A safe `WHERE` over a well-typed query is a filter of its rows. -/
theorem eval_select_of_isSafePredicate {q : Query S n} {Γ : Fin n → SqlType}
    (hq : q.typeOf = some Γ) {p : Expr n} (hp : p.IsSafePredicate Γ) {D : Database S}
    (hD : D.Conforms) :
    (select p q).eval D =
      (List.filter fun r => (p.evalTruth r).toOption = some .true) <$> q.eval D := by
  rw [eval_select]
  rcases h : q.eval D with e | rs
  · rfl
  · exact hp.filterRows_eq_ok (conforms_of_eval_eq_ok hD hq h)

/-- A join with a safe predicate over well-typed inputs filters the pairs of input rows, as
`Query.eval_join_eq_ok_of_forall` says, whenever both inputs succeed. -/
theorem eval_join_of_isSafePredicate {q₁ : Query S n} {q₂ : Query S m} {Γ : Fin n → SqlType}
    {Δ : Fin m → SqlType} (h₁ : q₁.typeOf = some Γ) (h₂ : q₂.typeOf = some Δ)
    {θ : Expr (n + m)} (hθ : θ.IsSafePredicate (Fin.append Γ Δ)) {D : Database S}
    (hD : D.Conforms) :
    (join θ q₁ q₂).eval D = (do
      let rs ← q₁.eval D
      let ss ← q₂.eval D
      return ((rs ×ˢ ss).filter fun (r, s) =>
          (θ.evalTruth (Fin.append r s)).toOption = some .true)
        |>.map fun (r, s) => Fin.append r s) := by
  rcases hrs : q₁.eval D with e | rs
  · rw [eval_join, hrs]
    rfl
  rcases hss : q₂.eval D with e | ss
  · rw [eval_join, hrs, hss]
    rfl
  exact eval_join_eq_ok_of_forall hrs hss fun r hr s hs => hθ.exists_evalTruth_eq_ok
    (Row.conforms_append_iff.mpr ⟨conforms_of_eval_eq_ok hD h₁ hrs r hr,
      conforms_of_eval_eq_ok hD h₂ hss s hs⟩)

/-- Filtering joined pairs by `Θ` and then by a predicate `P'` of the joined rows is filtering by
`Θ` the pairs that `P'` keeps. -/
private theorem filter_map_filter (Θ : Row n × Row m → Bool) (P' : Row (n + m) → Bool)
    (L : List (Row n × Row m)) :
    ((L.filter Θ).map fun (r, s) => Fin.append r s).filter P' =
      ((L.filter fun (r, s) => P' (Fin.append r s)).filter Θ).map fun (r, s) => Fin.append r s := by
  simp only [List.filter_map, List.filter_filter]
  exact congrArg (List.map _) (List.filter_congr fun _ _ => Bool.and_comm _ _)

/-- Both sides of a pushdown law evaluate their inputs once each and then compute a list, so they
agree when the lists agree for all input rows. -/
private theorem pushdown_of_lists {α β γ : Type} (x : Except EvalError α)
    (y : Except EvalError β) (f g : α → β → γ) (h : ∀ a b, f a b = g a b) :
    (do let a ← x; let b ← y; return f a b) = (do let a ← x; let b ← y; return g a b) :=
  bind_congr fun a => bind_congr fun b => congrArg pure (h a b)

/-- Predicate pushdown into the left input of a join: a safe predicate on the left columns may be
applied before the join, when the join predicate is safe too. Without safety the sides evaluate
the predicates on different rows: with an empty right input, the left side evaluates nothing
while the right side evaluates `p` on every left row. -/
theorem select_join_left {q₁ : Query S n} {q₂ : Query S m} {Γ : Fin n → SqlType}
    {Δ : Fin m → SqlType} (h₁ : q₁.typeOf = some Γ) (h₂ : q₂.typeOf = some Δ) {p : Expr n}
    (hp : p.IsSafePredicate Γ) {θ : Expr (n + m)} (hθ : θ.IsSafePredicate (Fin.append Γ Δ)) :
    Equiv .ordered (select (p.rename (Fin.castAdd m)) (join θ q₁ q₂))
      (join θ (select p q₁) q₂) := by
  refine Equiv.of_eval_eq fun D hD => ?_
  rw [eval_select_of_isSafePredicate (typeOf_join_eq_some.mpr ⟨Γ, Δ, h₁, h₂, hθ.1, rfl⟩)
      (Expr.IsSafePredicate.rename _ (by rwa [Fin.append_comp_castAdd])) hD,
    eval_join_of_isSafePredicate h₁ h₂ hθ hD,
    eval_join_of_isSafePredicate (typeOf_select_eq_some.mpr ⟨h₁, hp.1⟩) h₂ hθ hD,
    eval_select_of_isSafePredicate h₁ hp hD]
  simp only [map_bind, map_pure, bind_map_left]
  refine pushdown_of_lists _ _ _ _ fun rs ss => ?_
  rw [filter_map_filter, ← List.filter_product_left]
  refine congrArg (fun L => (List.filter _ L).map _) (List.filter_congr fun ⟨r, s⟩ _ => ?_)
  simp only [Expr.evalTruth, Expr.eval_rename_castAdd]
  rfl

/-- Predicate pushdown into the right input of a join, under the same conditions as
`Query.select_join_left`. -/
theorem select_join_right {q₁ : Query S n} {q₂ : Query S m} {Γ : Fin n → SqlType}
    {Δ : Fin m → SqlType} (h₁ : q₁.typeOf = some Γ) (h₂ : q₂.typeOf = some Δ) {p : Expr m}
    (hp : p.IsSafePredicate Δ) {θ : Expr (n + m)} (hθ : θ.IsSafePredicate (Fin.append Γ Δ)) :
    Equiv .ordered (select (p.rename (Fin.natAdd n)) (join θ q₁ q₂))
      (join θ q₁ (select p q₂)) := by
  refine Equiv.of_eval_eq fun D hD => ?_
  rw [eval_select_of_isSafePredicate (typeOf_join_eq_some.mpr ⟨Γ, Δ, h₁, h₂, hθ.1, rfl⟩)
      (Expr.IsSafePredicate.rename _ (by rwa [Fin.append_comp_natAdd])) hD,
    eval_join_of_isSafePredicate h₁ h₂ hθ hD,
    eval_join_of_isSafePredicate h₁ (typeOf_select_eq_some.mpr ⟨h₂, hp.1⟩) hθ hD,
    eval_select_of_isSafePredicate h₂ hp hD]
  simp only [map_bind, map_pure, bind_map_left]
  refine pushdown_of_lists _ _ _ _ fun rs ss => ?_
  rw [filter_map_filter, ← List.filter_product_right]
  refine congrArg (fun L => (List.filter _ L).map _) (List.filter_congr fun ⟨r, s⟩ _ => ?_)
  simp only [Expr.evalTruth, Expr.eval_rename_natAdd]
  rfl

/-- A `WHERE` over a cross join is an inner join `ON` the same predicate. Both evaluate the
predicate on every pair, so no condition is needed. -/
theorem select_join_true (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) :
    Equiv .ordered (select θ (join (lit (.bool true)) q₁ q₂)) (join θ q₁ q₂) :=
  Equiv.of_eval_eq fun D _ => by
    simp only [eval_select, eval_join, Expr.filterRows_true]
    rcases q₁.eval D with e | rs
    · rfl
    rcases q₂.eval D with e | ss <;> rfl

/-- `WHERE TRUE` keeps every row. -/
theorem select_true (q : Query S n) : Equiv .ordered (select (lit (.bool true)) q) q :=
  Equiv.of_eval_eq fun D _ => by
    simp only [eval_select, Expr.filterRows_true]
    rcases q.eval D with e | rs <;> rfl

/-! ### Projections -/

/-- Projection fusion: projecting twice is projecting once with the inner projection substituted,
when the inner projection is safe. The fused projection evaluates only the inner expressions that
the outer one uses, so an unsafe inner projection could make only the left side fail. -/
theorem project_project {q : Query S n} {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ)
    {g : Fin k → Expr n} (hg : ∀ i, (g i).IsSafe Γ) (f : Fin l → Expr k) :
    Equiv .ordered (project f (project g q)) (project (fun j => (f j).subst g) q) := by
  refine equiv_ordered_iff.mpr fun D hD => ?_
  simp only [eval_project]
  rcases h : q.eval D with e | rs
  · rfl
  have hrs := conforms_of_eval_eq_ok hD hq h
  choose! d hd using fun r (hr : r ∈ rs) =>
    Expr.exists_evalRow_eq_ok_iff.mpr fun i => (hg i).exists_eval_eq_ok (hrs r hr)
  simp only [Except.ok_bind, Except.mapM_eq_ok_map hd, List.mapM_map]
  exact Except.toOption_mapM_congr fun r hr => congrArg Except.toOption
    (Expr.evalRow_congr fun j => (Expr.eval_subst (Expr.evalRow_eq_ok_iff.mp (hd r hr)) _).symm)

/-- `SELECT *`: projecting on every column in order is the identity. -/
theorem project_col (q : Query S n) : Equiv .ordered (project Expr.col q) q :=
  Equiv.of_eval_eq fun D _ => by
    simp only [eval_project]
    rcases q.eval D with e | rs
    · rfl
    rw [Except.ok_bind, Except.mapM_eq_ok_map (g := id) fun _ _ => Expr.evalRow_eq_ok_iff.mpr
      fun _ => rfl, List.map_id]

/-! ### `UNION ALL` -/

/-- `WHERE` distributes over `UNION ALL`. -/
theorem select_unionAll (p : Expr n) (q₁ q₂ : Query S n) :
    Equiv .ordered (select p (unionAll q₁ q₂)) (unionAll (select p q₁) (select p q₂)) := by
  refine equiv_ordered_iff.mpr fun D _ => ?_
  simp only [eval_select, eval_unionAll]
  rcases q₁.eval D with e | rs
  · rfl
  rcases q₂.eval D with e | ss
  · simp only [Except.ok_bind]
    rcases p.filterRows rs <;> rfl
  simp only [Except.ok_bind, pure_bind, Except.toOption_bind, Expr.toOption_filterRows_append,
    Except.toOption_pure]
  rcases (p.filterRows rs).toOption <;> rcases (p.filterRows ss).toOption <;> rfl

/-- A `SELECT` list distributes over `UNION ALL`. -/
theorem project_unionAll (es : Fin k → Expr n) (q₁ q₂ : Query S n) :
    Equiv .ordered (project es (unionAll q₁ q₂)) (unionAll (project es q₁) (project es q₂)) := by
  refine equiv_ordered_iff.mpr fun D _ => ?_
  simp only [eval_project, eval_unionAll]
  rcases q₁.eval D with e | rs
  · rfl
  rcases q₂.eval D with e | ss
  · simp only [Except.ok_bind]
    rcases rs.mapM (Expr.evalRow es) <;> rfl
  simp only [Except.ok_bind, pure_bind, List.mapM_append]

/-- `UNION ALL` is associative. -/
theorem unionAll_assoc (q₁ q₂ q₃ : Query S n) :
    Equiv .ordered (unionAll (unionAll q₁ q₂) q₃) (unionAll q₁ (unionAll q₂ q₃)) :=
  Equiv.of_eval_eq fun D _ => by
    simp only [eval_unionAll]
    rcases q₁.eval D with e | rs
    · rfl
    rcases q₂.eval D with e | ss
    · rfl
    rcases q₃.eval D with e | ts
    · rfl
    simp only [Except.ok_bind, pure_bind, List.append_assoc]

/-- `UNION ALL` is commutative as a bag. It is not as a list: the left input comes first. -/
theorem unionAll_comm (q₁ q₂ : Query S n) : Equiv .bag (unionAll q₁ q₂) (unionAll q₂ q₁) :=
  fun D _ => by
    simp only [eval_unionAll]
    rcases q₁.eval D with e | rs <;> rcases q₂.eval D with e' | ss
    exacts [.none, .none, .none, .some List.perm_append_comm]

/-! ### Joins -/

/-- Join commutativity: exchanging the inputs of a join, and the two blocks of columns of its
predicate and its result, gives the same bag of rows. The pairs are enumerated in another order,
so it is not an equality of lists. -/
theorem join_comm (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) :
    Equiv .bag (join θ q₁ q₂)
      (project (fun i => col (finAddFlip i)) (join (θ.rename finAddFlip) q₂ q₁)) := fun D _ => by
  simp only [eval_join, eval_project]
  rcases q₁.eval D with e | rs <;> rcases q₂.eval D with e' | ss
  · exact .none
  · exact .none
  · exact .none
  have hcols : ∀ ts : List (Row (m + n)),
      ts.mapM (Expr.evalRow fun i => col (finAddFlip i)) = .ok (ts.map (· ∘ finAddFlip)) :=
    fun ts => Except.mapM_eq_ok_map fun t _ => Expr.evalRow_col_comp _ t
  have hflip : ∀ t ∈ Row.product ss rs,
      θ.evalTruth (t ∘ finAddFlip) = (θ.rename finAddFlip).evalTruth t :=
    fun t _ => by simp only [Expr.evalTruth, Expr.eval_rename]
  simp only [Except.ok_bind, Except.toOption_bind, hcols, Except.toOption_ok]
  have hrhs : (((θ.rename finAddFlip).filterRows (Row.product ss rs)).toOption.bind
      fun ts => some (ts.map (· ∘ finAddFlip))) =
      (θ.filterRows ((Row.product ss rs).map (· ∘ finAddFlip))).toOption := by
    rw [Expr.toOption_filterRows_map hflip]
    rcases ((θ.rename finAddFlip).filterRows (Row.product ss rs)).toOption <;> rfl
  rw [hrhs]
  refine EquivLevel.Rel.filterRows (ℓ := .bag) ?_ fun _ _ => rfl
  simp only [EquivLevel.rel_bag, Row.product, List.map_map]
  refine ((List.perm_map_swap_product ss rs).map _).symm.trans (List.Perm.of_eq ?_)
  rw [List.map_map]
  exact List.map_congr_left fun ⟨s, r⟩ _ => (Fin.append_comp_finAddFlip r s).symm

/-! ### `DISTINCT` -/

/-- `DISTINCT` is idempotent. -/
theorem distinct_distinct (q : Query S n) : Equiv .ordered (distinct (distinct q)) (distinct q) :=
  Equiv.of_eval_eq fun D _ => by
    simp only [eval_distinct]
    rcases q.eval D with e | rs
    · rfl
    simp only [Except.ok_bind, pure, Except.pure, List.dedup_idem]

/-- `DISTINCT` ignores the duplicates that `UNION ALL` of a query with itself creates. -/
theorem distinct_unionAll_self (q : Query S n) :
    Equiv .ordered (distinct (unionAll q q)) (distinct q) :=
  Equiv.of_eval_eq fun D _ => by
    simp only [eval_distinct, eval_unionAll]
    rcases q.eval D with e | rs
    · rfl
    simp only [Except.ok_bind, pure, Except.pure,
      List.Subset.dedup_append_right (List.Subset.refl rs)]

/-- `WHERE` commutes with `DISTINCT`. The left side evaluates `p` on one copy of each row and the
right side on every copy, but the copies are equal rows, so `p` has the same result, or fails, on
all of them, and no condition is needed. Both sides keep the last copy of each kept row. -/
theorem select_distinct (p : Expr n) (q : Query S n) :
    Equiv .ordered (select p (distinct q)) (distinct (select p q)) := by
  refine equiv_ordered_iff.mpr fun D _ => ?_
  simp only [eval_select, eval_distinct]
  rcases q.eval D with e | rs
  · rfl
  simp only [Except.ok_bind, pure_bind, Except.toOption_bind, Except.toOption_pure,
    Expr.toOption_filterRows, List.mem_dedup]
  split_ifs
  · rw [Option.bind_some, List.dedup_filter]
  · rfl

end Query

end Cslib.SQL
