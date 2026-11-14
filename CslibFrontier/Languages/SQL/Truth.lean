/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Order.Hom.Basic

/-!
# SQL's three-valued logic

SQL predicates take three truth values, ordered `false < unknown < true`. With this order, SQL's
`AND` is the minimum `⊓`, `OR` is the maximum `⊔`, and `NOT` reverses the order while fixing
`unknown`: this is Kleene's strong three-valued logic [Kleene1952]. A `WHERE` or `ON` clause keeps a
row exactly when its predicate is `true` (`Truth.isTrue`).

The order is transported from `ℕ` along `Truth.rank`, so `Truth` is a `LinearOrder` and a
`BoundedOrder` with `⊥ = false` and `⊤ = true`, hence a distributive lattice, and Mathlib's lattice
lemmas (`inf_comm`, `sup_assoc`, `inf_sup_left`, …) apply to `AND` and `OR` unchanged. The minimum
and maximum are given by truth tables, so the kernel evaluates them by `decide`.

`NOT` is `Truth.not`, an order-reversing involution (`Truth.notOrderIso : Truth ≃o Truthᵒᵈ`). It is
not a lattice complement: `unknown ⊔ not unknown = unknown`, so excluded middle fails
(`Truth.unknown_sup_not_unknown`). For this reason `NOT` is not a `Compl` instance: Mathlib's
`compl` lemmas belong to Heyting and Boolean algebras, and the Heyting complement of this chain
sends `unknown` to `false`, which is not SQL's `NOT`. De Morgan's laws (`Truth.not_inf`,
`Truth.not_sup`) and Kleene's law `a ⊓ not a ≤ b ⊔ not b` (`Truth.inf_not_le_sup_not`) are proved
directly.

It adapts and redesigns the `Trilean` type of `sql_equiv` (revision `38030a6b`) by Evelyn
Mitchell, whose connectives were separate truth tables; here they are the lattice operations.

## Main definitions

* `Cslib.SQL.Truth`: the truth values `false`, `unknown` and `true`, with
  `false < unknown < true`.
* `Cslib.SQL.Truth.not`: Kleene negation.
* `Cslib.SQL.Truth.ofBool`, `Cslib.SQL.Truth.isTrue`: embedding of two-valued logic, and the test
  a `WHERE` clause applies.

## Main results

* `Cslib.SQL.Truth.not_not`, `Cslib.SQL.Truth.not_inf`, `Cslib.SQL.Truth.not_sup`: `NOT` is an
  involution satisfying De Morgan's laws.
* `Cslib.SQL.Truth.inf_not_le_sup_not`: Kleene's law.
* `Cslib.SQL.Truth.unknown_sup_not_unknown`: excluded middle fails.
* `Cslib.SQL.Truth.ofBool_and`, `Cslib.SQL.Truth.ofBool_or`, `Cslib.SQL.Truth.ofBool_not`: on
  known values the connectives are Boolean.
* `Cslib.SQL.Truth.isTrue_inf`, `Cslib.SQL.Truth.isTrue_sup`: a conjunction holds when both
  conjuncts hold, a disjunction when one does.

## References

* [S. C. Kleene, *Introduction to Metamathematics*][Kleene1952]
-/

@[expose] public section

namespace Cslib.SQL

/-- SQL's truth values. `unknown` is the truth value of a comparison involving `NULL`. -/
inductive Truth where
  /-- Definitely false. -/
  | false
  /-- Unknown. -/
  | unknown
  /-- Definitely true. -/
  | true
  deriving DecidableEq, Repr, Inhabited

namespace Truth

/-- The position of a truth value in the chain `false < unknown < true`. -/
def rank : Truth → ℕ
  | false => 0
  | unknown => 1
  | true => 2

/-- Distinct truth values have distinct ranks. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Kleene conjunction, SQL's `AND`: the minimum in `false < unknown < true`. -/
instance : Min Truth where
  min
    | false, _ => false
    | _, false => false
    | unknown, _ => unknown
    | _, unknown => unknown
    | true, true => true

/-- Kleene disjunction, SQL's `OR`: the maximum in `false < unknown < true`. -/
instance : Max Truth where
  max
    | true, _ => true
    | _, true => true
    | unknown, _ => unknown
    | _, unknown => unknown
    | false, false => false

/-- The order `false < unknown < true`, transported along `rank`; its minimum and maximum are the
truth tables of `AND` and `OR`. -/
instance : LinearOrder Truth :=
  LinearOrder.lift rank rank_injective
    (fun a b => by cases a <;> cases b <;> rfl) (fun a b => by cases a <;> cases b <;> rfl)

instance : BoundedOrder Truth where
  top := true
  le_top a := by cases a <;> decide
  bot := false
  bot_le a := by cases a <;> decide

@[simp] theorem top_eq : (⊤ : Truth) = true := rfl

@[simp] theorem bot_eq : (⊥ : Truth) = false := rfl

theorem le_iff_rank_le {a b : Truth} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

@[simp] theorem sup_false (a : Truth) : a ⊔ false = a := sup_bot_eq a

@[simp] theorem false_sup (a : Truth) : false ⊔ a = a := bot_sup_eq a

@[simp] theorem sup_true (a : Truth) : a ⊔ true = true := sup_top_eq a

@[simp] theorem true_sup (a : Truth) : true ⊔ a = true := top_sup_eq a

@[simp] theorem inf_true (a : Truth) : a ⊓ true = a := inf_top_eq a

@[simp] theorem true_inf (a : Truth) : true ⊓ a = a := top_inf_eq a

@[simp] theorem inf_false (a : Truth) : a ⊓ false = false := inf_bot_eq a

@[simp] theorem false_inf (a : Truth) : false ⊓ a = false := bot_inf_eq a

/-- A disjunction is `true` exactly when a disjunct is. -/
theorem sup_eq_true_iff {a b : Truth} : a ⊔ b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

/-- A disjunction is `false` exactly when both disjuncts are. -/
theorem sup_eq_false_iff {a b : Truth} : a ⊔ b = false ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> decide

/-- A conjunction is `true` exactly when both conjuncts are. -/
theorem inf_eq_true_iff {a b : Truth} : a ⊓ b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

/-- A conjunction is `false` exactly when a conjunct is. -/
theorem inf_eq_false_iff {a b : Truth} : a ⊓ b = false ↔ a = false ∨ b = false := by
  cases a <;> cases b <;> decide

/-- Kleene negation, SQL's `NOT`: it exchanges `false` and `true` and fixes `unknown`. -/
def not : Truth → Truth
  | false => true
  | unknown => unknown
  | true => false

@[simp] theorem not_false : not false = true := rfl

@[simp] theorem not_unknown : not unknown = unknown := rfl

@[simp] theorem not_true : not true = false := rfl

/-- `NOT` is an involution. -/
@[simp] theorem not_not (a : Truth) : not (not a) = a := by
  cases a <;> rfl

theorem not_injective : Function.Injective not :=
  Function.LeftInverse.injective not_not

/-- `NOT` reverses the order. -/
@[simp] theorem not_le_not {a b : Truth} : not a ≤ not b ↔ b ≤ a := by
  cases a <;> cases b <;> decide

/-- `NOT` is an order isomorphism onto the order dual. -/
def notOrderIso : Truth ≃o Truthᵒᵈ where
  toFun a := OrderDual.toDual (not a)
  invFun a := not (OrderDual.ofDual a)
  left_inv := not_not
  right_inv := not_not
  map_rel_iff' := not_le_not

@[simp] theorem notOrderIso_apply (a : Truth) : notOrderIso a = OrderDual.toDual (not a) := rfl

theorem not_antitone : Antitone not := fun _ _ h => not_le_not.mpr h

/-- De Morgan: `NOT (a AND b) = NOT a OR NOT b`. -/
@[simp] theorem not_inf (a b : Truth) : not (a ⊓ b) = not a ⊔ not b := by
  cases a <;> cases b <;> rfl

/-- De Morgan: `NOT (a OR b) = NOT a AND NOT b`. -/
@[simp] theorem not_sup (a b : Truth) : not (a ⊔ b) = not a ⊓ not b := by
  cases a <;> cases b <;> rfl

/-- Kleene's law: a contradiction is below every excluded-middle instance. Together with
`not_not`, `not_inf` and `not_sup` it makes `Truth` a Kleene algebra in the lattice sense. -/
theorem inf_not_le_sup_not (a b : Truth) : a ⊓ not a ≤ b ⊔ not b := by
  cases a <;> cases b <;> decide

/-- Excluded middle fails: `unknown OR NOT unknown` is `unknown`, not `true`. -/
theorem unknown_sup_not_unknown : unknown ⊔ not unknown = unknown := rfl

/-- Non-contradiction fails: `unknown AND NOT unknown` is `unknown`, not `false`. -/
theorem unknown_inf_not_unknown : unknown ⊓ not unknown = unknown := rfl

/-- The truth value of a known Boolean. -/
def ofBool : Bool → Truth
  | .false => false
  | .true => true

@[simp] theorem ofBool_true : ofBool .true = true := rfl

@[simp] theorem ofBool_false : ofBool .false = false := rfl

@[simp] theorem ofBool_ne_unknown (b : Bool) : ofBool b ≠ unknown := by
  cases b <;> decide

theorem ofBool_injective : Function.Injective ofBool := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[simp] theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b :=
  ofBool_injective.eq_iff

/-- On known values, `AND` is Boolean conjunction. -/
@[simp] theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a ⊓ ofBool b := by
  cases a <;> cases b <;> rfl

/-- On known values, `OR` is Boolean disjunction. -/
@[simp] theorem ofBool_or (a b : Bool) : ofBool (a || b) = ofBool a ⊔ ofBool b := by
  cases a <;> cases b <;> rfl

/-- On known values, `NOT` is Boolean negation. -/
@[simp] theorem ofBool_not (a : Bool) : ofBool (!a) = not (ofBool a) := by
  cases a <;> rfl

/-- The test a `WHERE` or `ON` clause applies: only `true` keeps a row. -/
def isTrue : Truth → Bool
  | true => .true
  | _ => .false

@[simp] theorem isTrue_iff {a : Truth} : a.isTrue = .true ↔ a = true := by
  cases a <;> simp [isTrue]

@[simp] theorem isTrue_ofBool (b : Bool) : (ofBool b).isTrue = b := by
  cases b <;> rfl

/-- A conjunction holds exactly when both conjuncts hold. -/
@[simp] theorem isTrue_inf (a b : Truth) : (a ⊓ b).isTrue = (a.isTrue && b.isTrue) := by
  cases a <;> cases b <;> rfl

/-- A disjunction holds exactly when one disjunct holds. -/
@[simp] theorem isTrue_sup (a b : Truth) : (a ⊔ b).isTrue = (a.isTrue || b.isTrue) := by
  cases a <;> cases b <;> rfl

/-- `NOT a` is `true` exactly when `a` is `false`; so an `unknown` predicate and its negation both
drop the row in a `WHERE` clause. -/
@[simp] theorem not_eq_true_iff {a : Truth} : not a = true ↔ a = false := by
  cases a <;> decide

/-- `NOT a` is `false` exactly when `a` is `true`. -/
@[simp] theorem not_eq_false_iff {a : Truth} : not a = false ↔ a = true := by
  cases a <;> decide

end Truth

end Cslib.SQL
