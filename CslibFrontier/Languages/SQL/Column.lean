/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.SQL.Value
public import Mathlib.Data.List.Nodup

/-!
# Column metadata and name resolution

Expressions refer to columns by position, so names never affect evaluation. Names are metadata: a
`Column` records an optional qualifier (the table name or alias), a name and a declared type, and
the columns of an `n`-column row are `Fin n → Column`. Resolving a reference `[q.]name` against
them (`resolveColumn`) gives the unique matching position, or `unknownColumn` when no column
matches, or `ambiguousColumn` when several do. An unqualified reference matches every column of
that name; a qualified one only columns with that qualifier. Names are compared exactly: a parser
normalizes case before resolution.

These facts are what a translator from surface SQL to positional expressions needs to prove its
output well-scoped: a resolved position matches the reference (`resolveColumn_eq_ok_iff`), and the
two errors say precisely that nothing or more than one column matches.

It adapts and redesigns the column lookup of `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell,
where rows carried their names and lookup took the first case-insensitive match; here ambiguity is
an error and names are separate from rows.

## Main definitions

* `Cslib.SQL.Column`: a column's qualifier, name and declared type.
* `Cslib.SQL.Column.Matches`: a column answers to a reference `[q.]name`.
* `Cslib.SQL.resolveColumn`: name resolution, returning a position or a `ResolveError`.

## Main results

* `Cslib.SQL.resolveColumn_eq_ok_iff`: resolution returns exactly the unique matching position.
* `Cslib.SQL.resolveColumn_eq_unknownColumn_iff`,
  `Cslib.SQL.resolveColumn_eq_ambiguousColumn_iff`: when resolution fails, and why.
-/

@[expose] public section

namespace Cslib.SQL

/-- A column of a table or of a query result. -/
structure Column where
  /-- The table name or alias that qualifies the column, if any. -/
  qualifier : Option String
  /-- The column name. -/
  name : String
  /-- The declared type: every cell of the column is `NULL` or a value of this type. -/
  type : SqlType
  deriving DecidableEq, Repr

/-- Why a column reference does not resolve. -/
inductive ResolveError where
  /-- No column matches the reference. -/
  | unknownColumn
  /-- Several columns match the reference. -/
  | ambiguousColumn
  deriving DecidableEq, Repr

namespace Column

/-- The column answers to the reference `[q.]name`: it has that name and, when the reference is
qualified, that qualifier. -/
def Matches (c : Column) (q : Option String) (name : String) : Prop :=
  c.name = name ∧ ∀ q' ∈ q, c.qualifier = some q'

instance (c : Column) (q : Option String) (name : String) : Decidable (c.Matches q name) :=
  inferInstanceAs (Decidable (c.name = name ∧ ∀ q' ∈ q, c.qualifier = some q'))

@[simp] theorem matches_none {c : Column} {name : String} :
    c.Matches none name ↔ c.name = name := by
  simp [Matches]

@[simp] theorem matches_some {c : Column} {q name : String} :
    c.Matches (some q) name ↔ c.name = name ∧ c.qualifier = some q := by
  simp [Matches]

end Column

/-- Resolve the reference `[q.]name` against the columns `cols`: the position of the only matching
column, `unknownColumn` if none matches, `ambiguousColumn` if several do. -/
def resolveColumn {n : ℕ} (cols : Fin n → Column) (q : Option String) (name : String) :
    Except ResolveError (Fin n) :=
  match (List.finRange n).filter fun i => decide ((cols i).Matches q name) with
  | [] => .error .unknownColumn
  | [i] => .ok i
  | _ :: _ :: _ => .error .ambiguousColumn

section Resolve

variable {n : ℕ} {cols : Fin n → Column} {q : Option String} {name : String}

/-- A position is listed exactly when its column matches the reference. -/
private theorem mem_matching (i : Fin n) :
    i ∈ (List.finRange n).filter (fun j => decide ((cols j).Matches q name)) ↔
      (cols i).Matches q name := by
  simp

private theorem nodup_matching :
    ((List.finRange n).filter fun j => decide ((cols j).Matches q name)).Nodup :=
  (List.nodup_finRange n).filter _

/-- The three outcomes of resolution: no column matches, exactly one does, or two different ones
do. -/
private theorem resolveColumn_cases :
    (resolveColumn cols q name = .error .unknownColumn ∧ ∀ i, ¬(cols i).Matches q name) ∨
    (∃ i, resolveColumn cols q name = .ok i ∧ (cols i).Matches q name ∧
      ∀ j, (cols j).Matches q name → j = i) ∨
    (resolveColumn cols q name = .error .ambiguousColumn ∧
      ∃ i j, i ≠ j ∧ (cols i).Matches q name ∧ (cols j).Matches q name) := by
  have hmem := @mem_matching n cols q name
  have hnd := @nodup_matching n cols q name
  unfold resolveColumn
  generalize (List.finRange n).filter (fun j => decide ((cols j).Matches q name)) = l at hmem hnd ⊢
  match l with
  | [] => exact .inl ⟨rfl, fun i hi => by simpa using (hmem i).mpr hi⟩
  | [k] =>
    simp only [List.mem_singleton] at hmem
    exact .inr (.inl ⟨k, rfl, (hmem k).mp rfl, fun j hj => (hmem j).mpr hj⟩)
  | k :: k' :: l =>
    have hk : k ≠ k' := fun h => by simp [h] at hnd
    exact .inr (.inr ⟨rfl, k, k', hk, (hmem k).mp (by simp), (hmem k').mp (by simp)⟩)

/-- Resolution returns `i` exactly when column `i` is the only one matching the reference. -/
theorem resolveColumn_eq_ok_iff {i : Fin n} :
    resolveColumn cols q name = .ok i ↔
      (cols i).Matches q name ∧ ∀ j, (cols j).Matches q name → j = i := by
  rcases resolveColumn_cases (cols := cols) (q := q) (name := name) with
    ⟨h, hnone⟩ | ⟨k, h, hk, huniq⟩ | ⟨h, k, k', hkk', hk, hk'⟩ <;> rw [h]
  · simpa using fun hi => absurd hi (hnone i)
  · simp only [Except.ok.injEq]
    exact ⟨fun hki => hki ▸ ⟨hk, huniq⟩, fun ⟨hi, _⟩ => (huniq i hi).symm⟩
  · simp only [reduceCtorEq, false_iff, not_and, not_forall]
    intro _
    by_cases hki : k = i
    · exact ⟨k', hk', fun h => hkk' (hki.trans h.symm)⟩
    · exact ⟨k, hk, hki⟩

/-- A resolved reference names its column: the column has the requested name, and the requested
qualifier when there is one. -/
theorem Column.Matches.of_resolveColumn_eq_ok {i : Fin n}
    (h : resolveColumn cols q name = .ok i) : (cols i).Matches q name :=
  (resolveColumn_eq_ok_iff.mp h).1

/-- Resolution fails with `unknownColumn` exactly when no column matches. -/
theorem resolveColumn_eq_unknownColumn_iff :
    resolveColumn cols q name = .error .unknownColumn ↔ ∀ i, ¬(cols i).Matches q name := by
  rcases resolveColumn_cases (cols := cols) (q := q) (name := name) with
    ⟨h, hnone⟩ | ⟨k, h, hk, -⟩ | ⟨h, k, -, -, hk, -⟩ <;> rw [h]
  · simpa using hnone
  · simpa using ⟨k, hk⟩
  · simpa using ⟨k, hk⟩

/-- Resolution fails with `ambiguousColumn` exactly when two different columns match. -/
theorem resolveColumn_eq_ambiguousColumn_iff :
    resolveColumn cols q name = .error .ambiguousColumn ↔
      ∃ i j, i ≠ j ∧ (cols i).Matches q name ∧ (cols j).Matches q name := by
  rcases resolveColumn_cases (cols := cols) (q := q) (name := name) with
    ⟨h, hnone⟩ | ⟨k, h, -, huniq⟩ | ⟨h, hamb⟩ <;> rw [h]
  · simpa using fun i _ _ hi => absurd hi (hnone i)
  · simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro i j hij hi hj
    exact hij ((huniq i hi).trans (huniq j hj).symm)
  · simpa using hamb

end Resolve

end Cslib.SQL
