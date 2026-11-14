/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Option.Rel
public import CslibFrontier.Languages.SQL.Equiv
public import CslibFrontier.Languages.SQL.Query

/-!
# Equivalence of SQL queries

A query law says that two queries return the same result on every database instance. What "the
same" means depends on what the reader of the result may observe, so equivalence comes in three
levels (`EquivLevel`):

* `ordered`: the same list of rows; nothing in this fragment orders rows, so this is a property of
  the list representation, used for laws that hold for it exactly;
* `bag`: the same rows with the same multiplicities, in any order (`List.Perm`), which is SQL's
  meaning of a query without `ORDER BY` or `DISTINCT`;
* `set`: the same rows, ignoring multiplicities, which is what `DISTINCT` or `EXISTS` sees.

`Query.Equiv ℓ q₁ q₂` holds when, on every conforming instance, both queries fail or both
succeed with results related at level `ℓ`. Like expression equivalence (`Expr.Equiv`), it
observes `Except.toOption`: whether evaluation succeeds and with what, not which error it raises.
Ordered equivalence implies bag equivalence, which implies set equivalence (`Query.Equiv.mono`),
and each level is an equivalence relation.

Every query constructor is a congruence at every level, unconditionally in its query arguments
(`Query.Equiv.select`, `Query.Equiv.project`, `Query.Equiv.join`, `Query.Equiv.unionAll`,
`Query.Equiv.distinct`). In its expression arguments it is a congruence for expression
equivalence in the typing context of its input (`Query.Equiv.select_expr`,
`Query.Equiv.project_expr`, `Query.Equiv.join_expr`), which needs the input to be well-typed, so
that its rows conform to that context. Over `WHERE c`, an outer predicate can be replaced in the
typing context of the inner input whatever the type of `c`, since `c` keeps some of the input's
rows (`Query.Equiv.select_select_expr`). `DISTINCT` sees only sets: set-equivalent inputs give
bag-equivalent `DISTINCT` (`Query.Equiv.distinct_of_set`).

It adapts and redesigns the equivalence levels of `sql_equiv` (revision `38030a6b`) by Evelyn
Mitchell, which compared results on every database, with errors identified with empty or missing
results; here equivalences quantify over the instances conforming to the schema and keep a
failure distinct from every result.

## Main definitions

* `Cslib.SQL.EquivLevel`: the ordered, bag and set levels, ordered by how much they observe.
* `Cslib.SQL.EquivLevel.Rel`: lists related at a level.
* `Cslib.SQL.Query.Equiv`: equivalence of queries at a level, over conforming instances.

## Main results

* `Cslib.SQL.Query.Equiv.mono`: ordered ⇒ bag ⇒ set.
* `Cslib.SQL.Query.equivSetoid`: each level is an equivalence relation.
* `Cslib.SQL.Query.Equiv.select`, `Cslib.SQL.Query.Equiv.project`, `Cslib.SQL.Query.Equiv.join`,
  `Cslib.SQL.Query.Equiv.unionAll`, `Cslib.SQL.Query.Equiv.distinct`: congruence in the query
  arguments.
* `Cslib.SQL.Query.Equiv.select_expr`, `Cslib.SQL.Query.Equiv.project_expr`,
  `Cslib.SQL.Query.Equiv.join_expr`: congruence in the expression arguments.
* `Cslib.SQL.Query.Equiv.select_select_expr`: congruence in the outer predicate of `WHERE` over
  `WHERE`, in the typing context of the inner input.
* `Cslib.SQL.Query.Equiv.distinct_of_set`: set-equivalent inputs give bag-equivalent `DISTINCT`.
-/

@[expose] public section

namespace Cslib.SQL

/-- How much of a query's result an equivalence observes. -/
inductive EquivLevel where
  /-- The list of rows, in order. -/
  | ordered
  /-- The bag of rows: the list up to order. -/
  | bag
  /-- The set of rows: which rows occur, not how often. -/
  | set
  deriving DecidableEq, Repr

namespace EquivLevel

/-- The position of a level in `ordered < bag < set`, from finest to coarsest. -/
def rank : EquivLevel → ℕ
  | ordered => 0
  | bag => 1
  | set => 2

/-- Distinct levels have distinct ranks. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The order `ordered < bag < set`, transported along `rank`: `ℓ ≤ ℓ'` when `ℓ` observes at least
as much as `ℓ'`. -/
instance : LinearOrder EquivLevel := LinearOrder.lift' rank rank_injective

theorem le_iff_rank_le {ℓ ℓ' : EquivLevel} : ℓ ≤ ℓ' ↔ ℓ.rank ≤ ℓ'.rank := Iff.rfl

theorem ordered_le (ℓ : EquivLevel) : ordered ≤ ℓ := Nat.zero_le _

/-- Two lists are related at the level: equal; permutations of each other; or with the same
members. -/
def Rel {α : Type*} : EquivLevel → List α → List α → Prop
  | ordered => (· = ·)
  | bag => List.Perm
  | set => fun l₁ l₂ => ∀ a, a ∈ l₁ ↔ a ∈ l₂

variable {α β : Type*} {ℓ ℓ' : EquivLevel} {l₁ l₂ l₃ l₄ : List α}

@[simp] theorem rel_ordered : ordered.Rel l₁ l₂ ↔ l₁ = l₂ := Iff.rfl

@[simp] theorem rel_bag : bag.Rel l₁ l₂ ↔ l₁.Perm l₂ := Iff.rfl

@[simp] theorem rel_set : set.Rel l₁ l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂ := Iff.rfl

theorem Rel.refl (ℓ : EquivLevel) (l : List α) : ℓ.Rel l l := by
  cases ℓ
  exacts [rfl, List.Perm.refl l, fun _ => Iff.rfl]

theorem Rel.symm (h : ℓ.Rel l₁ l₂) : ℓ.Rel l₂ l₁ := by
  cases ℓ
  exacts [Eq.symm h, List.Perm.symm h, fun a => (h a).symm]

theorem Rel.trans (h₁₂ : ℓ.Rel l₁ l₂) (h₂₃ : ℓ.Rel l₂ l₃) : ℓ.Rel l₁ l₃ := by
  cases ℓ
  exacts [Eq.trans h₁₂ h₂₃, List.Perm.trans h₁₂ h₂₃, fun a => (h₁₂ a).trans (h₂₃ a)]

/-- Lists related at a level have the same members. -/
theorem Rel.mem_iff (h : ℓ.Rel l₁ l₂) (a : α) : a ∈ l₁ ↔ a ∈ l₂ := by
  cases ℓ
  exacts [h ▸ Iff.rfl, List.Perm.mem_iff h, h a]

/-- A relation at a finer level holds at every coarser one. -/
theorem Rel.mono (hℓ : ℓ ≤ ℓ') (h : ℓ.Rel l₁ l₂) : ℓ'.Rel l₁ l₂ := by
  cases ℓ <;> cases ℓ'
  all_goals first
    | exact h
    | exact absurd hℓ (by decide)
    | exact h ▸ Rel.refl _ _
    | exact fun a => Rel.mem_iff (ℓ := bag) h a

theorem Rel.append (h₁ : ℓ.Rel l₁ l₂) (h₂ : ℓ.Rel l₃ l₄) : ℓ.Rel (l₁ ++ l₃) (l₂ ++ l₄) := by
  cases ℓ
  · exact h₁ ▸ h₂ ▸ rfl
  · exact List.Perm.append h₁ h₂
  · intro a
    simp only [List.mem_append, h₁ a, h₂ a]

theorem Rel.filter (p : α → Bool) (h : ℓ.Rel l₁ l₂) : ℓ.Rel (l₁.filter p) (l₂.filter p) := by
  cases ℓ
  · exact h ▸ rfl
  · exact List.Perm.filter p h
  · intro a
    simp only [List.mem_filter, h a]

theorem Rel.filterMap (f : α → Option β) (h : ℓ.Rel l₁ l₂) :
    ℓ.Rel (l₁.filterMap f) (l₂.filterMap f) := by
  cases ℓ
  · exact h ▸ rfl
  · exact List.Perm.filterMap f h
  · intro b
    simp only [List.mem_filterMap]
    exact exists_congr fun a => and_congr_left' (h a)

theorem Rel.map (f : α → β) (h : ℓ.Rel l₁ l₂) : ℓ.Rel (l₁.map f) (l₂.map f) := by
  cases ℓ
  · exact h ▸ rfl
  · exact List.Perm.map f h
  · intro b
    simp only [List.mem_map]
    exact exists_congr fun a => and_congr_left' (h a)

theorem Rel.product {t₁ t₂ : List β} (h : ℓ.Rel l₁ l₂) (h' : ℓ.Rel t₁ t₂) :
    ℓ.Rel (l₁ ×ˢ t₁) (l₂ ×ˢ t₂) := by
  cases ℓ
  · exact h ▸ h' ▸ rfl
  · exact List.Perm.product h h'
  · rintro ⟨a, b⟩
    simp only [List.mem_product, h a, h' b]

theorem Rel.dedup [DecidableEq α] (h : ℓ.Rel l₁ l₂) : ℓ.Rel l₁.dedup l₂.dedup := by
  cases ℓ
  · exact h ▸ rfl
  · exact List.Perm.dedup h
  · intro a
    simp only [List.mem_dedup, h a]

/-- Lists with the same members, related at any level, have permuted deduplications. -/
theorem Rel.perm_dedup [DecidableEq α] (h : ℓ.Rel l₁ l₂) : l₁.dedup.Perm l₂.dedup :=
  (List.perm_ext_iff_of_nodup (List.nodup_dedup l₁) (List.nodup_dedup l₂)).mpr fun a => by
    simp only [List.mem_dedup, h.mem_iff a]

variable {n m k : ℕ}

theorem Rel.rowProduct {rs rs' : List (Row n)} {ss ss' : List (Row m)} (h : ℓ.Rel rs rs')
    (h' : ℓ.Rel ss ss') : ℓ.Rel (Row.product rs ss) (Row.product rs' ss') :=
  (h.product h').map _

/-- `WHERE` with predicates that agree on the members of related inputs gives related results,
or fails on both. -/
theorem Rel.filterRows {rs rs' : List (Row n)} (h : ℓ.Rel rs rs') {p p' : Expr n}
    (hp : ∀ r ∈ rs, (p.evalTruth r).toOption = (p'.evalTruth r).toOption) :
    Option.Rel ℓ.Rel (p.filterRows rs).toOption (p'.filterRows rs').toOption := by
  have hp' : ∀ r ∈ rs', (p.evalTruth r).toOption = (p'.evalTruth r).toOption :=
    fun r hr => hp r ((h.mem_iff r).mpr hr)
  rw [Expr.toOption_filterRows, Expr.toOption_filterRows]
  have hc : (∀ r ∈ rs, (p.evalTruth r).toOption.isSome) ↔
      ∀ r ∈ rs', (p'.evalTruth r).toOption.isSome :=
    ⟨fun hall r hr => hp' r hr ▸ hall r ((h.mem_iff r).mpr hr),
      fun hall r hr => (hp r hr).symm ▸ hall r ((h.mem_iff r).mp hr)⟩
  split_ifs with hall hall' hall'
  · rw [Option.rel_some_some]
    convert h.filter (fun r => decide ((p.evalTruth r).toOption = some .true)) using 1
    exact List.filter_congr fun r hr => by rw [hp' r hr]
  · exact absurd (hc.mp hall) hall'
  · exact absurd (hc.mpr hall') hall
  · exact .none

/-- `SELECT` lists that agree on the members of related inputs give related results, or fail on
both. -/
theorem Rel.mapM_evalRow {rs rs' : List (Row n)} (h : ℓ.Rel rs rs') {es es' : Fin k → Expr n}
    (hes : ∀ r ∈ rs, (Expr.evalRow es r).toOption = (Expr.evalRow es' r).toOption) :
    Option.Rel ℓ.Rel (rs.mapM (Expr.evalRow es)).toOption
      (rs'.mapM (Expr.evalRow es')).toOption := by
  have hes' : ∀ r ∈ rs', (Expr.evalRow es r).toOption = (Expr.evalRow es' r).toOption :=
    fun r hr => hes r ((h.mem_iff r).mpr hr)
  rw [Except.toOption_mapM, Except.toOption_mapM]
  have hc : (∀ r ∈ rs, (Expr.evalRow es r).toOption.isSome) ↔
      ∀ r ∈ rs', (Expr.evalRow es' r).toOption.isSome :=
    ⟨fun hall r hr => hes' r hr ▸ hall r ((h.mem_iff r).mpr hr),
      fun hall r hr => (hes r hr).symm ▸ hall r ((h.mem_iff r).mp hr)⟩
  split_ifs with hall hall' hall'
  · rw [Option.rel_some_some]
    convert h.filterMap (fun r => (Expr.evalRow es r).toOption) using 1
    exact List.filterMap_congr fun r hr => (hes' r hr).symm
  · exact absurd (hc.mp hall) hall'
  · exact absurd (hc.mpr hall') hall
  · exact .none

end EquivLevel

namespace Query

variable {S : DbSchema} {n m k : ℕ}

/-- Queries `q₁` and `q₂` are equivalent at level `ℓ`: on every instance conforming to the
schema, both fail, or both succeed with results related at `ℓ`. -/
def Equiv (ℓ : EquivLevel) (q₁ q₂ : Query S n) : Prop :=
  ∀ D : Database S, D.Conforms → Option.Rel ℓ.Rel (q₁.eval D).toOption (q₂.eval D).toOption

theorem equiv_ordered_iff {q₁ q₂ : Query S n} :
    Equiv .ordered q₁ q₂ ↔ ∀ D : Database S, D.Conforms →
      (q₁.eval D).toOption = (q₂.eval D).toOption := by
  simp only [Equiv]
  exact forall₂_congr fun _ _ => Option.rel_eq_iff

/-- Queries with the same evaluation on every conforming instance are equivalent at every level. -/
theorem Equiv.of_eval_eq {ℓ : EquivLevel} {q₁ q₂ : Query S n}
    (h : ∀ D : Database S, D.Conforms → q₁.eval D = q₂.eval D) : Equiv ℓ q₁ q₂ := fun D hD =>
  h D hD ▸ Option.rel_refl (EquivLevel.Rel.refl ℓ) _

namespace Equiv

variable {ℓ ℓ' : EquivLevel}

@[refl] theorem refl (q : Query S n) : Equiv ℓ q q :=
  fun _ _ => Option.rel_refl (EquivLevel.Rel.refl ℓ) _

@[symm] theorem symm {q₁ q₂ : Query S n} (h : Equiv ℓ q₁ q₂) : Equiv ℓ q₂ q₁ :=
  fun D hD => Option.Rel.symm (r := ℓ.Rel) (fun _ _ h => h.symm) (h D hD)

theorem trans {q₁ q₂ q₃ : Query S n} (h₁₂ : Equiv ℓ q₁ q₂) (h₂₃ : Equiv ℓ q₂ q₃) :
    Equiv ℓ q₁ q₃ :=
  fun D hD => Option.Rel.trans (r := ℓ.Rel) (fun _ _ _ h h' => h.trans h') (h₁₂ D hD) (h₂₃ D hD)

instance : Trans (Equiv (S := S) (n := n) ℓ) (Equiv ℓ) (Equiv ℓ) := ⟨trans⟩

theorem equivalence (ℓ : EquivLevel) : _root_.Equivalence (Equiv (S := S) (n := n) ℓ) :=
  ⟨refl, symm, trans⟩

/-- Equivalence at a finer level implies equivalence at every coarser one:
ordered ⇒ bag ⇒ set. -/
theorem mono (hℓ : ℓ ≤ ℓ') {q₁ q₂ : Query S n} (h : Equiv ℓ q₁ q₂) : Equiv ℓ' q₁ q₂ :=
  fun D hD => (h D hD).mono fun _ _ => EquivLevel.Rel.mono hℓ

/-- Ordered equivalence implies equivalence at every level. -/
theorem of_ordered {q₁ q₂ : Query S n} (h : Equiv .ordered q₁ q₂) : Equiv ℓ q₁ q₂ :=
  h.mono (EquivLevel.ordered_le ℓ)

/-! ### Congruence in the query arguments -/

theorem select (p : Expr n) {q q' : Query S n} (h : Equiv ℓ q q') :
    Equiv ℓ (select p q) (select p q') := fun D hD => by
  simp only [eval_select, Except.toOption_bind]
  exact (h D hD).bind fun _ _ hrel => hrel.filterRows fun _ _ => rfl

theorem project (es : Fin k → Expr n) {q q' : Query S n} (h : Equiv ℓ q q') :
    Equiv ℓ (project es q) (project es q') := fun D hD => by
  simp only [eval_project, Except.toOption_bind]
  exact (h D hD).bind fun _ _ hrel => hrel.mapM_evalRow fun _ _ => rfl

theorem join (θ : Expr (n + m)) {q₁ q₁' : Query S n} {q₂ q₂' : Query S m} (h₁ : Equiv ℓ q₁ q₁')
    (h₂ : Equiv ℓ q₂ q₂') : Equiv ℓ (join θ q₁ q₂) (join θ q₁' q₂') := fun D hD => by
  simp only [eval_join, Except.toOption_bind]
  exact (h₁ D hD).bind fun _ _ hrel₁ => (h₂ D hD).bind fun _ _ hrel₂ =>
    (hrel₁.rowProduct hrel₂).filterRows fun _ _ => rfl

theorem unionAll {q₁ q₁' q₂ q₂' : Query S n} (h₁ : Equiv ℓ q₁ q₁') (h₂ : Equiv ℓ q₂ q₂') :
    Equiv ℓ (unionAll q₁ q₂) (unionAll q₁' q₂') := fun D hD => by
  simp only [eval_unionAll, Except.toOption_bind]
  exact (h₁ D hD).bind fun _ _ hrel₁ => (h₂ D hD).bind fun _ _ hrel₂ =>
    .some (hrel₁.append hrel₂)

theorem distinct {q q' : Query S n} (h : Equiv ℓ q q') : Equiv ℓ (distinct q) (distinct q') :=
  fun D hD => by
    simp only [eval_distinct, Except.toOption_bind]
    exact (h D hD).bind fun _ _ hrel => .some hrel.dedup

/-- `DISTINCT` observes only the set of rows of its input: set-equivalent inputs give
bag-equivalent results. -/
theorem distinct_of_set {q q' : Query S n} (h : Equiv .set q q') :
    Equiv .bag (Query.distinct q) (Query.distinct q') := fun D hD => by
  simp only [eval_distinct, Except.toOption_bind]
  exact (h D hD).bind fun _ _ hrel => .some hrel.perm_dedup

/-! ### Congruence in the expression arguments -/

/-- Replacing a `WHERE` predicate by an equivalent one in the typing context of the input gives an
equivalent query. -/
theorem select_expr {q : Query S n} {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ)
    {p p' : Expr n} (hp : p.Equiv Γ p') : Equiv ℓ (Query.select p q) (Query.select p' q) :=
  fun D hD => by
    simp only [eval_select]
    rcases h : q.eval D with e | rs
    · exact .none
    · exact (EquivLevel.Rel.refl ℓ rs).filterRows fun r hr =>
        hp.evalTruth (conforms_of_eval_eq_ok hD hq h r hr)

/-- Replacing the outer predicate of `WHERE` over `WHERE c` by an equivalent one in the typing
context of the inner input gives an equivalent query, whatever the type of `c`: the rows that `c`
keeps are rows of the input, so they conform to that context. `Query.Equiv.select_expr` would need
`WHERE c` itself to be well-typed. -/
theorem select_select_expr {q : Query S n} {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ)
    {p p' : Expr n} (hp : p.Equiv Γ p') (c : Expr n) :
    Equiv ℓ (Query.select p (Query.select c q)) (Query.select p' (Query.select c q)) :=
  fun D hD => by
    simp only [eval_select]
    rcases h : q.eval D with e | rs
    · exact .none
    rw [Except.ok_bind]
    rcases hc : c.filterRows rs with e | rs'
    · exact .none
    exact (EquivLevel.Rel.refl ℓ rs').filterRows fun r hr =>
      hp.evalTruth (conforms_of_eval_eq_ok hD hq h r (Expr.mem_of_filterRows_eq_ok hc hr))

/-- Replacing the expressions of a `SELECT` list by equivalent ones in the typing context of the
input gives an equivalent query. -/
theorem project_expr {q : Query S n} {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ)
    {es es' : Fin k → Expr n} (hes : ∀ i, (es i).Equiv Γ (es' i)) :
    Equiv ℓ (Query.project es q) (Query.project es' q) := fun D hD => by
  simp only [eval_project]
  rcases h : q.eval D with e | rs
  · exact .none
  · exact (EquivLevel.Rel.refl ℓ rs).mapM_evalRow fun r hr =>
      Expr.toOption_evalRow_congr fun i => hes i r (conforms_of_eval_eq_ok hD hq h r hr)

/-- Replacing a join predicate by an equivalent one in the typing context of the joined rows gives
an equivalent query. -/
theorem join_expr {q₁ : Query S n} {q₂ : Query S m} {Γ : Fin n → SqlType} {Δ : Fin m → SqlType}
    (h₁ : q₁.typeOf = some Γ) (h₂ : q₂.typeOf = some Δ) {θ θ' : Expr (n + m)}
    (hθ : θ.Equiv (Fin.append Γ Δ) θ') : Equiv ℓ (Query.join θ q₁ q₂) (Query.join θ' q₁ q₂) :=
  fun D hD => by
    simp only [eval_join]
    rcases hrs : q₁.eval D with e | rs
    · exact .none
    rcases hss : q₂.eval D with e | ss
    · exact .none
    exact (EquivLevel.Rel.refl ℓ _).filterRows fun t ht => hθ.evalTruth
      (Row.conforms_of_mem_product (conforms_of_eval_eq_ok hD h₁ hrs)
        (conforms_of_eval_eq_ok hD h₂ hss) ht)

end Equiv

/-- Equivalence at the level `ℓ`, as a setoid. -/
def equivSetoid (ℓ : EquivLevel) : Setoid (Query S n) := ⟨Equiv ℓ, Equiv.equivalence ℓ⟩

end Query

end Cslib.SQL
