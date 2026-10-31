/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Combinatorics.Matroid.Basic

/-!
# IndepQuery: Independence-Oracle Queries for Matroid Algorithms

`IndepQuery α` is the query signature for independence-oracle matroid algorithms in CSLib's
`FreeM` query-complexity framework (`Cslib.Algorithms.Lean.Query.FreeM`). A single query
`IndepQuery.indep S` tests whether a finite candidate subset `S : Finset α` is independent,
returning `Bool`.

Decoupling the computable query syntax `FreeM (IndepQuery α)` from the propositional predicate
`IndepQuery.ImplementsMatroid oracle M` allows algorithms to execute computably against concrete
Boolean independence checkers while proving mathematical optimality against arbitrary (possibly
noncomputable) `Mathlib.Combinatorics.Matroid` instances.

## Main definitions

* `Cslib.Query.IndepQuery`: query signature with constructor `indep (S : Finset α)`.
* `Cslib.Query.IndepQuery.ask`: lift an independence query into `FreeM (IndepQuery α) Bool`.
* `Cslib.Query.IndepQuery.oracleOf`: build an `IndepQuery` oracle from `Finset α → Bool`.
* `Cslib.Query.IndepQuery.ImplementsMatroid`: states that `oracle` answers `indep S` with `true`
  if and only if `M.Indep (S : Set α)`.
* `Cslib.Query.IndepQuery.matroidOracle`: classical oracle canonically implementing any
  `M : Matroid α`.
-/

public section

open scoped Cardinal

namespace Cslib.Query

/-- Independence-oracle query: asks whether the finite subset `S : Finset α` is independent,
returning a `Bool`. -/
inductive IndepQuery (α : Type) : Type → Type where
  | indep (S : Finset α) : IndepQuery α Bool

/-- Lift `IndepQuery.indep S` into `FreeM (IndepQuery α) Bool`. -/
abbrev IndepQuery.ask {α : Type} (S : Finset α) : FreeM (IndepQuery α) Bool :=
  FreeM.lift (.indep S)

@[simp] theorem IndepQuery.eval_ask {α : Type}
    (oracle : {ι : Type} → IndepQuery α ι → ι) (S : Finset α) :
    (IndepQuery.ask S).eval oracle = oracle (.indep S) := rfl

/-- Build an `IndepQuery α` oracle from a Boolean predicate on finite sets `Finset α → Bool`. -/
@[expose] def IndepQuery.oracleOf {α : Type} (f : Finset α → Bool) :
    {ι : Type} → IndepQuery α ι → ι
  | _, .indep S => f S

@[simp] theorem IndepQuery.oracleOf_indep {α : Type} (f : Finset α → Bool) (S : Finset α) :
    IndepQuery.oracleOf f (.indep S) = f S := rfl

/-- `ImplementsMatroid oracle M` states that `oracle` faithfully decides finite-set independence in
`M : Matroid α`. -/
@[expose] def IndepQuery.ImplementsMatroid {α : Type}
    (oracle : {ι : Type} → IndepQuery α ι → ι) (M : Matroid α) : Prop :=
  ∀ S : Finset α, oracle (.indep S) = true ↔ M.Indep (S : Set α)

/-- Classical independence oracle associated with an arbitrary `M : Matroid α`. -/
noncomputable def IndepQuery.matroidOracle {α : Type} (M : Matroid α) :
    {ι : Type} → IndepQuery α ι → ι :=
  letI := Classical.propDecidable
  IndepQuery.oracleOf fun S => decide (M.Indep (S : Set α))

theorem IndepQuery.implementsMatroid_matroidOracle {α : Type} (M : Matroid α) :
    IndepQuery.ImplementsMatroid (IndepQuery.matroidOracle M) M := by
  intro S
  classical
  simp [IndepQuery.matroidOracle]

/-- Every `IndepQuery α ι` has response type `ι = Bool`, of cardinality `2`. -/
theorem IndepQuery.cardResponse_eq_two {α : Type} : ∀ {ι : Type}, IndepQuery α ι → #ι = 2
  | _, .indep _ => Cardinal.mk_bool

theorem IndepQuery.cardResponse_le_two {α : Type} {ι : Type} (op : IndepQuery α ι) : #ι ≤ 2 :=
  (IndepQuery.cardResponse_eq_two op).le

end Cslib.Query
