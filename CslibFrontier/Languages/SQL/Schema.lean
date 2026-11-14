/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.SQL.Column
public import CslibFrontier.Languages.SQL.Row

/-!
# Database schemas and instances

A database schema (`DbSchema`) names the tables and gives each table its arity and its column
declarations, independently of any data: an empty table still has columns and types. The typing
context of a table (`DbSchema.ctx`) is the list of its declared column types.

A database instance (`Database S`) gives each table of `S` its rows. The rows form a bag, which
is represented by a list: duplicates matter, and the list order is a property of this
representation only, since SQL promises no order without `ORDER BY`. An instance conforms to its
schema (`Database.Conforms`) when every cell of every table is `NULL` or a value of its column's
declared type.

It adapts and redesigns the databases of `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell,
which mapped table names to lists of name–value rows, so that a table's columns and types came
from its data and an empty table had none; here the schema is separate data that every instance
of it conforms to.

## Main definitions

* `Cslib.SQL.DbSchema`: table names, arities and column declarations.
* `Cslib.SQL.DbSchema.ctx`: the typing context of a table.
* `Cslib.SQL.Database`: an instance of a schema, a bag of rows for each table.
* `Cslib.SQL.Database.Conforms`: every table's rows conform to its declared types.
-/

@[expose] public section

namespace Cslib.SQL

/-- A database schema: the table names, and for each table its number of columns and their
declarations. It does not depend on data, so an empty table has columns too. -/
structure DbSchema where
  /-- The table names. -/
  Table : Type
  /-- The number of columns of each table. -/
  arity : Table → ℕ
  /-- The column declarations of each table: names, qualifiers and declared types. -/
  columns : (t : Table) → Fin (arity t) → Column

namespace DbSchema

/-- The typing context of a table: the declared types of its columns. -/
def ctx (S : DbSchema) (t : S.Table) : Fin (S.arity t) → SqlType := fun i => (S.columns t i).type

end DbSchema

/-- A database instance of the schema `S`: for each table, its rows. A table is a bag of rows,
represented by a list; the list order means nothing in SQL. -/
abbrev Database (S : DbSchema) := (t : S.Table) → List (Row (S.arity t))

namespace Database

variable {S : DbSchema}

/-- The instance conforms to its schema: every row of every table has the table's declared
types. -/
def Conforms (D : Database S) : Prop := ∀ t, ∀ r ∈ D t, r.Conforms (S.ctx t)

instance [Fintype S.Table] (D : Database S) : Decidable D.Conforms :=
  inferInstanceAs (Decidable (∀ t, ∀ r ∈ D t, r.Conforms (S.ctx t)))

/-- The instance with every table empty conforms to every schema. -/
theorem conforms_empty : Conforms (S := S) fun _ => [] := fun _ _ h => absurd h List.not_mem_nil

end Database

end Cslib.SQL
