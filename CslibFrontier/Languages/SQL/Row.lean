/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.SQL.Value
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic

/-!
# SQL rows and their types

A row of an `n`-column table is `Row n := Fin n → Datum`: columns are referenced by position,
so a reference to a missing column cannot be written. Rows are written `![d₀, d₁, …]`, and their
equality is decidable through Mathlib's instance for functions on a `Fintype`, which the kernel
evaluates: `decide` compares concrete rows, also rows computed by reindexing.

The type information that expressions are checked against is a typing context
`Γ : Fin n → SqlType`, and a row conforms to it when every cell is `NULL` or a value of its
column's type (`Row.Conforms`).

The row of a join is `Fin.append` of the two input rows, so the left columns are `Fin.castAdd` and
the right columns `Fin.natAdd`; a joined row conforms to the appended context exactly when both
inputs conform (`Row.conforms_append_iff`).

It adapts and redesigns the rows of `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell, which were
lists of name–value pairs whose schema came from the data; here positions are fixed by the type and
names are separate metadata (`Cslib.SQL.Column`).

## Main definitions

* `Cslib.SQL.Row`: a row of `n` datums.
* `Cslib.SQL.Row.Conforms`: a row has the types of a typing context.

## Main results

* `Cslib.SQL.Row.conforms_append_iff`: a joined row conforms exactly when both sides do.
-/

@[expose] public section

namespace Cslib.SQL

/-- A row of an `n`-column table, by position. It is an `abbrev`, so rows are functions: `![…]`,
`Fin.append` and `Fin.cons` build them, and they inherit decidable equality. -/
abbrev Row (n : ℕ) := Fin n → Datum

namespace Row

variable {n m : ℕ}

/-- The row conforms to the typing context `Γ`: every cell is `NULL` or a value of its column's
type. -/
def Conforms (Γ : Fin n → SqlType) (r : Row n) : Prop := ∀ i, (r i).HasType (Γ i)

instance (Γ : Fin n → SqlType) (r : Row n) : Decidable (r.Conforms Γ) :=
  inferInstanceAs (Decidable (∀ i, (r i).HasType (Γ i)))

/-- The all-`NULL` row conforms to every typing context. -/
theorem conforms_null (Γ : Fin n → SqlType) : Conforms Γ (fun _ => none) := fun _ => trivial

/-- A row conforms after reindexing when it conforms before. -/
theorem Conforms.comp {Γ : Fin n → SqlType} {r : Row n} (h : r.Conforms Γ) (ρ : Fin m → Fin n) :
    Conforms (Γ ∘ ρ) (r ∘ ρ) := fun i => h (ρ i)

/-- A joined row conforms to the joined typing context exactly when both sides conform. -/
theorem conforms_append_iff {Γ : Fin n → SqlType} {Δ : Fin m → SqlType} {r : Row n}
    {s : Row m} : Conforms (Fin.append Γ Δ) (Fin.append r s) ↔ r.Conforms Γ ∧ s.Conforms Δ := by
  simp only [Conforms, Fin.forall_fin_add, Fin.append_left, Fin.append_right]

end Row

end Cslib.SQL
