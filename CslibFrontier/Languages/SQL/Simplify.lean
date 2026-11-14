/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.SQL.QueryLaws
public import Mathlib.Data.Fin.Tuple.Reflection

/-!
# A proof-producing SQL simplifier

`Expr.simplify Γ e` simplifies an expression over the typing context `Γ`, and
`Query.simplify q` simplifies a query. Both are ordinary functions that the kernel evaluates, and
each comes with its certificate: `Expr.equiv_simplify` says that `e` and `e.simplify Γ` are
equivalent on every row conforming to `Γ` (`Expr.Equiv`), and `Query.equiv_simplify` that `q` and
`q.simplify` are ordered-equivalent on every conforming instance (`Query.Equiv .ordered`), so a
fact about the result of one transfers to the other at every level. Equivalence observes failure
under strict evaluation, so no rewrite turns a failing expression or query into a succeeding one,
or the reverse.

Every rewrite is one of the laws of `Cslib.SQL.Expr.Equiv` or `Cslib.SQL.Query`. A rewrite whose
law has a side condition is guarded by the decidable check of that condition (a type from
`Expr.typeOf`, safety from `Expr.IsSafe` or `Expr.IsSafePredicate`, in the typing context of the
input from `Query.typeOf`), and when the check fails the node is left as it is.

## Expressions

`Expr.simplify` works bottom up: it simplifies the operands of a node, then rewrites the node once
(`Expr.simpUnary`, `Expr.simpBinary`, `Expr.simpInList`, `Expr.simpCaseWhen`):

* an operator or `IN` whose operands are literals is evaluated, and replaced by the literal of its
  result when evaluation succeeds; an error is never folded, so `1 / 0` stays;
* `NOT (a op b)` becomes `a (negate op) b`, `NOT (e IS NULL)` becomes `e IS NOT NULL` and the
  reverse, and `NOT (NOT p)` and `-(-x)` become `p` and `x` when `p` is boolean and `x` an integer;
* `p AND TRUE`, `TRUE AND p`, `p OR FALSE` and `FALSE OR p` become `p` when `p` is boolean, while
  `p AND FALSE`, `FALSE AND p`, `p OR TRUE` and `TRUE OR p` become the constant only when `p` is a
  safe predicate, since an erroring `p` must still make the whole expression fail;
* `x + 0`, `0 + x`, `x - 0`, `x * 1` and `1 * x` become `x` when `x` is an integer; `x * 0` is not
  rewritten, since it is `NULL` when `x` is;
* `e IN ()` becomes `FALSE` when `e` is safe, and `e IN (v)` becomes `e = v`;
* `CASE WHEN c THEN a ELSE b END` with a literal condition becomes `a` for `TRUE` and `b` for
  `FALSE` and `NULL`.

A `NULL` produced by folding gets the type of the node it replaces, or `BOOLEAN` when that node is
ill-typed. Folding and `CASE` elimination can therefore turn an ill-typed expression into a
well-typed one: `NULL::text + 0` becomes a boolean `NULL`, and
`CASE WHEN TRUE THEN 1 ELSE 'a' END` becomes `1`. The certificate covers such inputs too, since it
compares evaluations on conforming rows, but typing does not transfer back from the result: check
`Expr.typeOf`, `Query.typeOf` or `Query.IsSafe` on the input when its typing matters. (A result
that passes `Query.IsSafe` still shows, through the certificate, that the input succeeds on every
conforming instance.)

## Queries

`Query.simplify` also works bottom up, in one pass. At each node it simplifies the expressions of
the node in the typing context of the node's input, when that input is well-typed, and then:

* `WHERE p` over another `WHERE c` merges into `WHERE c AND p` when `p`, after simplification, is
  safe (`Query.select_select`); over a projection it moves below it with the projection substituted
  when the projection is safe (`Query.select_project`); over a join it moves into the left or
  right input when, after simplification, it mentions only that input's columns and both it and
  the join predicate are safe (`Query.select_join_left`, `Query.select_join_right`, with the
  decidable `Expr.lowerLeft` and `Expr.lowerRight` recognizing such a predicate); over a cross join
  that it cannot enter it becomes the join predicate (`Query.select_join_true`); over `UNION ALL` it
  is copied into both inputs (`Query.select_unionAll`), and it moves below `DISTINCT`
  (`Query.select_distinct`). A moved predicate keeps moving down in the same way, and where it
  stops it is simplified in the context it reached; `WHERE TRUE` is dropped (`Query.select_true`).
  This is `Query.pushSelect`.
* A projection over a projection fuses by substitution when the inner one is safe
  (`Query.project_project`), and a projection that becomes `SELECT *` is dropped
  (`Query.project_col`). This is `Query.fuseProject`. The simplified `SELECT` list is built by
  `FinVec.map`, so the simplification of a literal `![…]` list is again a literal list, which
  callers can compare by `rfl`.
* A join predicate is simplified in the context of the joined rows (`Query.simpJoin`).

Each of these recursions follows the structure of the query, so the simplifier terminates by
structural recursion. Merged conjunctions are not split again, so a conjunction that mentions both
inputs of a join stays above it even if one of its conjuncts could move.

It adapts and redesigns the certified rewriter of `sql_equiv` (revision `38030a6b`) by Evelyn
Mitchell, which returned each rewritten expression with its equivalence proof and guarded
conditional rules by syntactic type checks. Here the guards are the typing and safety checks of a
typing context, the guarantee covers every conforming row and every conforming instance under
strict errors (so the absorbing rules `p AND FALSE` and `p OR TRUE` need a safe `p`), and the
simplifier also rewrites queries.

## Main definitions

* `Cslib.SQL.Expr.simplify`: the expression simplifier.
* `Cslib.SQL.Expr.simpUnary`, `Cslib.SQL.Expr.simpBinary`, `Cslib.SQL.Expr.simpInList`,
  `Cslib.SQL.Expr.simpCaseWhen`: one rewrite at the root.
* `Cslib.SQL.Query.simplify`: the query simplifier.
* `Cslib.SQL.Query.pushSelect`, `Cslib.SQL.Query.fuseProject`: moving `WHERE` down and fusing
  projections.
* `Cslib.SQL.Query.simpSelect`, `Cslib.SQL.Query.simpProject`, `Cslib.SQL.Query.simpJoin`:
  simplifying the expressions of a node in place.

## Main results

* `Cslib.SQL.Expr.equiv_simplify`: an expression is equivalent to its simplification.
* `Cslib.SQL.Query.equiv_simplify`: a query is ordered-equivalent to its simplification.
-/

public section

namespace Cslib.SQL

variable {n m k : ℕ}

namespace Expr

/-! ### Expressions -/

/-- `op e` rewritten at the root, for an operand `e` that is already simplified: folded when `e`
is a literal and the operator succeeds on it, otherwise rewritten by the laws for `NOT` over a
comparison, a null test or a negation, and for double negation. -/
@[expose] def simpUnary (Γ : Fin n → SqlType) (op : UnOp) (e : Expr n) : Expr n :=
  match e.asLiteral.bind fun d => (evalUnOp op d).toOption with
  | some d => ofDatum (((unary op e).typeOf Γ).getD .bool) d
  | none =>
    match op, e with
    | .not, binary (.cmp c) a b => binary (.cmp c.negate) a b
    | .not, unary .not p => if p.typeOf Γ = some .bool then p else unary .not (unary .not p)
    | .not, unary .isNull x => unary .isNotNull x
    | .not, unary .isNotNull x => unary .isNull x
    | .neg, unary .neg x => if x.typeOf Γ = some .int then x else unary .neg (unary .neg x)
    | op, e => unary op e

/-- `e₁ op e₂` rewritten at the root, for operands that are already simplified: folded when both
are literals and the operator succeeds on them, otherwise rewritten by the identity and absorption
laws of `AND` and `OR` and the identity laws of `+`, `-` and `*`, each under its guard. -/
@[expose] def simpBinary (Γ : Fin n → SqlType) (op : BinOp) (e₁ e₂ : Expr n) : Expr n :=
  match e₁.asLiteral.bind fun d₁ => e₂.asLiteral.bind fun d₂ => (evalBinOp op d₁ d₂).toOption with
  | some d => ofDatum (((binary op e₁ e₂).typeOf Γ).getD .bool) d
  | none =>
    match op with
    | .and =>
      if e₂ = lit (.bool true) ∧ e₁.typeOf Γ = some .bool then e₁
      else if e₁ = lit (.bool true) ∧ e₂.typeOf Γ = some .bool then e₂
      else if e₂ = lit (.bool false) ∧ e₁.IsSafePredicate Γ then lit (.bool false)
      else if e₁ = lit (.bool false) ∧ e₂.IsSafePredicate Γ then lit (.bool false)
      else binary .and e₁ e₂
    | .or =>
      if e₂ = lit (.bool false) ∧ e₁.typeOf Γ = some .bool then e₁
      else if e₁ = lit (.bool false) ∧ e₂.typeOf Γ = some .bool then e₂
      else if e₂ = lit (.bool true) ∧ e₁.IsSafePredicate Γ then lit (.bool true)
      else if e₁ = lit (.bool true) ∧ e₂.IsSafePredicate Γ then lit (.bool true)
      else binary .or e₁ e₂
    | .arith .add =>
      if e₂ = lit (.int 0) ∧ e₁.typeOf Γ = some .int then e₁
      else if e₁ = lit (.int 0) ∧ e₂.typeOf Γ = some .int then e₂
      else binary (.arith .add) e₁ e₂
    | .arith .sub =>
      if e₂ = lit (.int 0) ∧ e₁.typeOf Γ = some .int then e₁ else binary (.arith .sub) e₁ e₂
    | .arith .mul =>
      if e₂ = lit (.int 1) ∧ e₁.typeOf Γ = some .int then e₁
      else if e₁ = lit (.int 1) ∧ e₂.typeOf Γ = some .int then e₂
      else binary (.arith .mul) e₁ e₂
    | op => binary op e₁ e₂

/-- `e IN vs` rewritten at the root, for an operand `e` that is already simplified: folded when
`e` is a literal and the membership succeeds, otherwise `e IN ()` is `FALSE` when `e` is safe and
`e IN (v)` is `e = v`. -/
@[expose] def simpInList (Γ : Fin n → SqlType) (e : Expr n) (vs : List Datum) : Expr n :=
  match e.asLiteral.bind fun d => (d.inList vs).toOption with
  | some t => ofDatum .bool t.toDatum
  | none =>
    match vs with
    | [] => if e.IsSafe Γ then lit (.bool false) else inList e []
    | [v] => binary (.cmp .eq) e (ofDatum ((e.typeOf Γ).getD .bool) v)
    | vs => inList e vs

/-- `CASE WHEN c THEN a ELSE b END` with a literal condition is the branch it takes. -/
@[expose] def simpCaseWhen (c a b : Expr n) : Expr n :=
  match c with
  | lit (.bool true) => a
  | lit (.bool false) => b
  | null _ => b
  | c => caseWhen c a b

/-- The expression simplifier: simplify the operands of each node, then rewrite the node once.
`Expr.equiv_simplify` certifies it on the rows conforming to `Γ`. -/
@[expose] def simplify (Γ : Fin n → SqlType) : Expr n → Expr n
  | lit v => lit v
  | null τ => null τ
  | col i => col i
  | unary op e => simpUnary Γ op (e.simplify Γ)
  | binary op e₁ e₂ => simpBinary Γ op (e₁.simplify Γ) (e₂.simplify Γ)
  | inList e vs => simpInList Γ (e.simplify Γ) vs
  | caseWhen c a b => simpCaseWhen (c.simplify Γ) (a.simplify Γ) (b.simplify Γ)

variable {Γ : Fin n → SqlType}

theorem equiv_simpUnary (Γ : Fin n → SqlType) (op : UnOp) (e : Expr n) :
    Equiv Γ (unary op e) (simpUnary Γ op e) := by
  unfold simpUnary
  split
  next d h =>
    obtain ⟨d₀, h₀, h⟩ := Option.bind_eq_some_iff.mp h
    refine Equiv.of_eval_eq_ok (fun r _ => ?_) _
    rw [eval_unary, eval_of_asLiteral_eq_some h₀, Except.ok_bind]
    exact Except.toOption_eq_some_iff.mp h
  next =>
    split
    · exact Equiv.not_cmp _ _ _
    · split_ifs with h
      · exact Equiv.not_not h
      · rfl
    · exact Equiv.not_isNull _
    · exact Equiv.not_isNotNull _
    · split_ifs with h
      · exact Equiv.neg_neg h
      · rfl
    · rfl

theorem equiv_simpBinary (Γ : Fin n → SqlType) (op : BinOp) (e₁ e₂ : Expr n) :
    Equiv Γ (binary op e₁ e₂) (simpBinary Γ op e₁ e₂) := by
  unfold simpBinary
  split
  next d h =>
    obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
    refine Equiv.of_eval_eq_ok (fun r _ => ?_) _
    rw [eval_binary, eval_of_asLiteral_eq_some h₁, eval_of_asLiteral_eq_some h₂, Except.ok_bind,
      Except.ok_bind]
    exact Except.toOption_eq_some_iff.mp h
  next =>
    split
    · split_ifs with h₁ h₂ h₃ h₄
      · obtain ⟨rfl, h⟩ := h₁
        exact Equiv.and_true h
      · obtain ⟨rfl, h⟩ := h₂
        exact Equiv.true_and h
      · obtain ⟨rfl, h⟩ := h₃
        exact Equiv.and_false h
      · obtain ⟨rfl, h⟩ := h₄
        exact Equiv.false_and h
      · rfl
    · split_ifs with h₁ h₂ h₃ h₄
      · obtain ⟨rfl, h⟩ := h₁
        exact Equiv.or_false h
      · obtain ⟨rfl, h⟩ := h₂
        exact Equiv.false_or h
      · obtain ⟨rfl, h⟩ := h₃
        exact Equiv.or_true h
      · obtain ⟨rfl, h⟩ := h₄
        exact Equiv.true_or h
      · rfl
    · split_ifs with h₁ h₂
      · obtain ⟨rfl, h⟩ := h₁
        exact Equiv.add_zero h
      · obtain ⟨rfl, h⟩ := h₂
        exact Equiv.zero_add h
      · rfl
    · split_ifs with h₁
      · obtain ⟨rfl, h⟩ := h₁
        exact Equiv.sub_zero h
      · rfl
    · split_ifs with h₁ h₂
      · obtain ⟨rfl, h⟩ := h₁
        exact Equiv.mul_one h
      · obtain ⟨rfl, h⟩ := h₂
        exact Equiv.one_mul h
      · rfl
    · rfl

theorem equiv_simpInList (Γ : Fin n → SqlType) (e : Expr n) (vs : List Datum) :
    Equiv Γ (inList e vs) (simpInList Γ e vs) := by
  unfold simpInList
  split
  next t h =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    refine Equiv.of_eval_eq_ok (fun r _ => ?_) _
    rw [eval_inList, eval_of_asLiteral_eq_some hd, Except.ok_bind,
      Except.toOption_eq_some_iff.mp h]
    rfl
  next =>
    split
    · split_ifs with h
      · exact Equiv.inList_nil h
      · rfl
    · exact Equiv.inList_singleton _ _ _
    · rfl

theorem equiv_simpCaseWhen (c a b : Expr n) :
    Equiv Γ (caseWhen c a b) (simpCaseWhen c a b) := by
  unfold simpCaseWhen
  split
  · exact Equiv.caseWhen_true a b
  · exact Equiv.caseWhen_false a b
  · exact Equiv.caseWhen_null _ a b
  · rfl

/-- The expression simplifier is sound: on every row conforming to `Γ`, an expression and its
simplification both fail or both succeed with the same datum. -/
theorem equiv_simplify (Γ : Fin n → SqlType) (e : Expr n) : Equiv Γ e (e.simplify Γ) := by
  induction e with
  | lit | null | col => rfl
  | unary op e ih => exact (ih.unary op).trans (equiv_simpUnary Γ op _)
  | binary op e₁ e₂ ih₁ ih₂ => exact (ih₁.binary op ih₂).trans (equiv_simpBinary Γ op _ _)
  | inList e vs ih => exact (ih.inList vs).trans (equiv_simpInList Γ _ vs)
  | caseWhen c a b ihc iha ihb => exact (ihc.caseWhen iha ihb).trans (equiv_simpCaseWhen _ _ _)

end Expr

/-! ### Queries -/

namespace Query

variable {S : DbSchema}

open Expr (col lit binary)

/-- `WHERE p` over `q`, simplified in place: `p` is simplified in the typing context of `q` when
`q` is well-typed, and dropped when it becomes `TRUE`. -/
@[expose] def simpSelect (p : Expr n) (q : Query S n) : Query S n :=
  match q.typeOf with
  | some Γ => if p.simplify Γ = lit (.bool true) then q else select (p.simplify Γ) q
  | none => select p q

/-- `SELECT es FROM q`, simplified in place: the expressions are simplified in the typing context
of `q` when `q` is well-typed, and the projection is dropped when it becomes `SELECT *`. The
simplified list is built by `FinVec.map`, so that of a literal `![…]` list is a literal list. Over
an ill-typed input, the list is returned as written. -/
@[expose] def simpProject (es : Fin k → Expr n) (q : Query S n) : Query S k :=
  match q.typeOf with
  | some Γ =>
    let es' := FinVec.map (Expr.simplify Γ) es
    if h : k = n then
      if ∀ i, es' i = col (Fin.cast h i) then h ▸ q else project es' q
    else project es' q
  | none => project es q

/-- `q₁ JOIN q₂ ON θ` with `θ` simplified in the typing context of the joined rows, when both
inputs are well-typed. -/
@[expose] def simpJoin (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) : Query S (n + m) :=
  match q₁.typeOf, q₂.typeOf with
  | some Γ, some Δ => join (θ.simplify (Fin.append Γ Δ)) q₁ q₂
  | _, _ => join θ q₁ q₂

/-- `WHERE p` over `q`, moved as far down as the guarded laws allow: simplified and merged into a
`WHERE` below it when it simplifies to a safe predicate, moved below a safe projection with the
projection substituted, into the input of a join that it reads when it and the join predicate are
safe, into both inputs of a `UNION ALL`, or below a `DISTINCT`, and made the predicate of a cross
join that it cannot enter. Where it stops, it is simplified in place (`Query.simpSelect`). -/
@[expose] def pushSelect : {n : ℕ} → Expr n → Query S n → Query S n
  | _, p, q@(table _) => simpSelect p q
  | _, p, select c q =>
    match q.typeOf with
    | some Γ =>
      let p' := p.simplify Γ
      if p'.IsSafePredicate Γ then pushSelect (binary .and c p') q else simpSelect p (select c q)
    | none => simpSelect p (select c q)
  | _, p, project es q =>
    match q.typeOf with
    | some Γ =>
      if ∀ i, (es i).IsSafe Γ then project es (pushSelect (p.subst es) q)
      else simpSelect p (project es q)
    | none => simpSelect p (project es q)
  | _, p, join θ q₁ q₂ =>
    match q₁.typeOf, q₂.typeOf with
    | some Γ, some Δ =>
      if θ.IsSafePredicate (Fin.append Γ Δ) then
        let p' := p.simplify (Fin.append Γ Δ)
        match p'.lowerLeft.filter (fun p₁ => decide (p₁.IsSafePredicate Γ)),
          p'.lowerRight.filter (fun p₂ => decide (p₂.IsSafePredicate Δ)) with
        | some p₁, _ => join θ (pushSelect p₁ q₁) q₂
        | none, some p₂ => join θ q₁ (pushSelect p₂ q₂)
        | none, none =>
          if θ = lit (.bool true) then join p' q₁ q₂ else simpSelect p (join θ q₁ q₂)
      else simpSelect p (join θ q₁ q₂)
    | _, _ => simpSelect p (join θ q₁ q₂)
  | _, p, unionAll q₁ q₂ => unionAll (pushSelect p q₁) (pushSelect p q₂)
  | _, p, distinct q => distinct (pushSelect p q)

/-- `SELECT es FROM q` with projections fused: over a safe projection, the two fuse by
substitution, and the result fuses further down. Where it stops, it is simplified in place
(`Query.simpProject`). -/
@[expose] def fuseProject : {n k : ℕ} → (Fin k → Expr n) → Query S n → Query S k
  | _, _, es, q@(table _) => simpProject es q
  | _, _, es, select p q => simpProject es (select p q)
  | _, _, es, project g q =>
    match q.typeOf with
    | some Γ =>
      if ∀ i, (g i).IsSafe Γ then fuseProject (fun j => (es j).subst g) q
      else simpProject es (project g q)
    | none => simpProject es (project g q)
  | _, _, es, join θ q₁ q₂ => simpProject es (join θ q₁ q₂)
  | _, _, es, unionAll q₁ q₂ => simpProject es (unionAll q₁ q₂)
  | _, _, es, distinct q => simpProject es (distinct q)

/-- The query simplifier: simplify the inputs of each node, then move its `WHERE` down, fuse its
projections or simplify its join predicate. `Query.equiv_simplify` certifies it on every
conforming instance. -/
@[expose] def simplify : {n : ℕ} → Query S n → Query S n
  | _, table t => table t
  | _, select p q => pushSelect p q.simplify
  | _, project es q => fuseProject es q.simplify
  | _, join θ q₁ q₂ => simpJoin θ q₁.simplify q₂.simplify
  | _, unionAll q₁ q₂ => unionAll q₁.simplify q₂.simplify
  | _, distinct q => distinct q.simplify

theorem equiv_simpSelect (p : Expr n) (q : Query S n) :
    Equiv .ordered (select p q) (simpSelect p q) := by
  unfold simpSelect
  split
  next Γ hq =>
    have h := Equiv.select_expr (ℓ := .ordered) hq (Expr.equiv_simplify Γ p)
    split_ifs with ht
    · rw [ht] at h
      exact h.trans (select_true q)
    · exact h
  next => rfl

theorem equiv_simpProject (es : Fin k → Expr n) (q : Query S n) :
    Equiv .ordered (project es q) (simpProject es q) := by
  unfold simpProject
  split
  next Γ hq =>
    have h : Equiv .ordered (project es q) (project (FinVec.map (Expr.simplify Γ) es) q) :=
      Equiv.project_expr hq fun i =>
        FinVec.map_eq (Expr.simplify Γ) es ▸ Expr.equiv_simplify Γ (es i)
    dsimp only
    split_ifs with hk hcol
    · subst hk
      have hcol' : FinVec.map (Expr.simplify Γ) es = Expr.col :=
        funext fun i => by simpa using hcol i
      rw [hcol'] at h
      exact h.trans (project_col q)
    · exact h
    · exact h
  next => rfl

theorem equiv_simpJoin (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) :
    Equiv .ordered (join θ q₁ q₂) (simpJoin θ q₁ q₂) := by
  unfold simpJoin
  split
  next Γ Δ h₁ h₂ => exact Equiv.join_expr h₁ h₂ (Expr.equiv_simplify _ θ)
  next => rfl

theorem equiv_pushSelect (p : Expr n) (q : Query S n) :
    Equiv .ordered (select p q) (pushSelect p q) := by
  induction q with
  | table t => exact equiv_simpSelect p _
  | select c q ih =>
    rw [pushSelect]
    split
    next Γ hq =>
      dsimp only
      split_ifs with hp
      · exact (Equiv.select_select_expr hq (Expr.equiv_simplify Γ p) c).trans
          ((select_select hq hp c).trans (ih _))
      · exact equiv_simpSelect p _
    next => exact equiv_simpSelect p _
  | project es q ih =>
    rw [pushSelect]
    split
    next Γ hq =>
      split_ifs with hes
      · exact (select_project hq hes p).trans (Equiv.project es (ih _))
      · exact equiv_simpSelect p _
    next => exact equiv_simpSelect p _
  | join θ q₁ q₂ ih₁ ih₂ =>
    rw [pushSelect]
    split
    next Γ Δ h₁ h₂ =>
      by_cases hθ : θ.IsSafePredicate (Fin.append Γ Δ)
      · rw [ite_eq_left hθ]
        have hp := Equiv.select_expr (ℓ := .ordered)
          (typeOf_join_eq_some.mpr ⟨Γ, Δ, h₁, h₂, hθ.1, rfl⟩)
          (Expr.equiv_simplify (Fin.append Γ Δ) p)
        refine hp.trans ?_
        dsimp only
        split
        next p₁ _ hl =>
          obtain ⟨hl, hs⟩ := Option.filter_eq_some_iff.mp hl
          rw [← Expr.rename_castAdd_of_lowerLeft_eq_some hl]
          exact (select_join_left h₁ h₂ (of_decide_eq_true hs) hθ).trans
            (Equiv.join θ (ih₁ _) (Equiv.refl _))
        next p₂ _ hr =>
          obtain ⟨hr, hs⟩ := Option.filter_eq_some_iff.mp hr
          rw [← Expr.rename_natAdd_of_lowerRight_eq_some hr]
          exact (select_join_right h₁ h₂ (of_decide_eq_true hs) hθ).trans
            (Equiv.join θ (Equiv.refl _) (ih₂ _))
        next =>
          split_ifs with hT
          · subst hT
            exact select_join_true _ _ _
          · exact hp.symm.trans (equiv_simpSelect p _)
      · rw [ite_eq_right hθ]
        exact equiv_simpSelect p _
    next => exact equiv_simpSelect p _
  | unionAll q₁ q₂ ih₁ ih₂ =>
    rw [pushSelect]
    exact (select_unionAll p q₁ q₂).trans (Equiv.unionAll (ih₁ p) (ih₂ p))
  | distinct q ih =>
    rw [pushSelect]
    exact (select_distinct p q).trans (Equiv.distinct (ih p))

theorem equiv_fuseProject (es : Fin k → Expr n) (q : Query S n) :
    Equiv .ordered (project es q) (fuseProject es q) := by
  induction q with
  | project g q ih =>
    rw [fuseProject]
    split
    next Γ hq =>
      split_ifs with hg
      · exact (project_project hq hg es).trans (ih _)
      · exact equiv_simpProject es _
    next => exact equiv_simpProject es _
  | _ =>
    rw [fuseProject]
    exact equiv_simpProject es _

/-- The query simplifier is sound: on every conforming instance, a query and its simplification
both fail or both succeed with the same list of rows. -/
theorem equiv_simplify (q : Query S n) : Equiv .ordered q q.simplify := by
  induction q with
  | table t => rfl
  | select p q ih => exact (Equiv.select p ih).trans (equiv_pushSelect p _)
  | project es q ih => exact (Equiv.project es ih).trans (equiv_fuseProject es _)
  | join θ q₁ q₂ ih₁ ih₂ => exact (Equiv.join θ ih₁ ih₂).trans (equiv_simpJoin θ _ _)
  | unionAll q₁ q₂ ih₁ ih₂ => exact Equiv.unionAll ih₁ ih₂
  | distinct q ih => exact Equiv.distinct ih

end Query

end Cslib.SQL
