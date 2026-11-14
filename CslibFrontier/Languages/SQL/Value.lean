/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Int.Notation

/-!
# SQL values and `NULL`

This module fixes the values a cell of a SQL table can hold. A `Value` is a non-null value of one
of the three column types `SqlType.int`, `SqlType.text` and `SqlType.bool`; integers are
unbounded and text is a Lean `String`. A cell holds a `Datum`, which is `Option Value`: `none` is
SQL's `NULL`, which belongs to every type (`Datum.HasType`).

It adapts and redesigns material from `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell. There,
`NULL` was a value constructor carrying an optional type, and `none : Option Value` meant an
evaluation error. Here a value is never `NULL`, `NULL` is the `none` of a datum, errors are a
separate type (`Cslib.SQL.EvalError`), and decimals are not part of the fragment.

## Main definitions

* `Cslib.SQL.SqlType`: the column types `int`, `text` and `bool`.
* `Cslib.SQL.Value`: a non-null value, with its type `Cslib.SQL.Value.type`.
* `Cslib.SQL.Datum`: the content of a cell, `Option Value`, where `none` is `NULL`.
* `Cslib.SQL.Datum.HasType`: a datum is `NULL` or a value of the given type.
-/

@[expose] public section

namespace Cslib.SQL

/-- The column types of the SQL fragment. -/
inductive SqlType where
  /-- Unbounded integers. -/
  | int
  /-- Character strings, compared by code points. -/
  | text
  /-- Booleans. -/
  | bool
  deriving DecidableEq, Repr, Inhabited

/-- A non-null SQL value. `NULL` is not a value: it is the `none` of a `Datum`. -/
inductive Value where
  /-- An integer. -/
  | int (z : ℤ)
  /-- A character string. -/
  | text (s : String)
  /-- A boolean. -/
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace Value

/-- The type of a value. -/
def type : Value → SqlType
  | int _ => .int
  | text _ => .text
  | bool _ => .bool

@[simp] theorem type_int (z : ℤ) : (int z).type = .int := rfl

@[simp] theorem type_text (s : String) : (text s).type = .text := rfl

@[simp] theorem type_bool (b : Bool) : (bool b).type = .bool := rfl

/-- An integer value is an integer literal. -/
theorem type_eq_int_iff {v : Value} : v.type = .int ↔ ∃ z, v = int z := by
  cases v <;> simp [type]

/-- A text value is a text literal. -/
theorem type_eq_text_iff {v : Value} : v.type = .text ↔ ∃ s, v = text s := by
  cases v <;> simp [type]

/-- A boolean value is a boolean literal. -/
theorem type_eq_bool_iff {v : Value} : v.type = .bool ↔ ∃ b, v = bool b := by
  cases v <;> simp [type]

end Value

/-- The content of a cell: a value, or `none` for SQL's `NULL`.

It is an `abbrev` so that `Option`'s constructors, instances (`DecidableEq`, `Repr`) and lemmas
apply to datums directly. The type does not encode errors: evaluation returns
`Except EvalError Datum`, so a `NULL` result and a failure stay distinct. -/
abbrev Datum := Option Value

namespace Datum

/-- `d.HasType τ`: the datum is `NULL` or a value of type `τ`. `NULL` has every type. -/
def HasType : Datum → SqlType → Prop
  | none, _ => True
  | some v, τ => v.type = τ

instance decidableHasType : ∀ (d : Datum) (τ : SqlType), Decidable (d.HasType τ)
  | none, _ => isTrue trivial
  | some v, τ => inferInstanceAs (Decidable (v.type = τ))

@[simp] theorem hasType_none (τ : SqlType) : HasType none τ := trivial

@[simp] theorem hasType_some {v : Value} {τ : SqlType} : HasType (some v) τ ↔ v.type = τ :=
  Iff.rfl

/-- A non-null datum has only its own type. -/
theorem HasType.unique {d : Datum} {τ τ' : SqlType} (hτ : d.HasType τ) (hτ' : d.HasType τ')
    (hd : d ≠ none) : τ = τ' := by
  cases d with
  | none => exact absurd rfl hd
  | some v => exact hτ.symm.trans hτ'

end Datum

end Cslib.SQL
