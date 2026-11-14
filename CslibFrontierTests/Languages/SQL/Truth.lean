/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.SQL.Truth

/-! Checked examples of SQL's three-valued logic, through an ordinary import. -/

public section

namespace CslibFrontierTests.SQL.Truth

open Cslib.SQL

/-- The three truth values, in order. -/
abbrev truths : List Truth := [.false, .unknown, .true]

-- The `AND` table: row `a`, column `b`, entry `a AND b`.
example : truths.map (fun a => truths.map (a ⊓ ·)) =
    [[.false, .false, .false], [.false, .unknown, .unknown], [.false, .unknown, .true]] := by
  decide

-- The `OR` table.
example : truths.map (fun a => truths.map (a ⊔ ·)) =
    [[.false, .unknown, .true], [.unknown, .unknown, .true], [.true, .true, .true]] := by
  decide

-- The `NOT` table, and only `true` passes a `WHERE` clause.
example : truths.map Truth.not = [.true, .unknown, .false] := by decide
example : truths.map Truth.isTrue = [false, false, true] := by decide

-- `FALSE` dominates `AND` and `TRUE` dominates `OR`, even against `unknown`.
example : Truth.false ⊓ .unknown = .false ∧ Truth.true ⊔ .unknown = .true := by decide

-- Excluded middle and non-contradiction fail at `unknown`; both drop the row in a `WHERE`.
example : (Truth.unknown ⊔ Truth.unknown.not).isTrue = false := by decide
example : Truth.unknown ⊓ Truth.unknown.not ≠ .false := by decide

-- Mathlib's lattice lemmas apply to `AND` and `OR` unchanged.
example (a b c : Truth) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := inf_sup_left a b c
example (a b : Truth) : a ⊓ (a ⊔ b) = a := inf_sup_self
example (a b : Truth) : a ⊓ b ≤ a ⊔ b := inf_le_sup

-- De Morgan and involution, by `simp`.
example (a b c : Truth) : (a ⊓ (b ⊔ c)).not.not = a ⊓ (b ⊔ c) := by simp
example (a b : Truth) : (a ⊔ b.not).not = a.not ⊓ b := by simp

-- `NOT` reverses the order, and it is an order isomorphism onto the dual.
example (a b : Truth) (h : a ≤ b) : b.not ≤ a.not := Truth.not_antitone h
example : Truth.notOrderIso .unknown = OrderDual.toDual .unknown := rfl

-- On known values the connectives are Boolean.
example (a b : Bool) : (Truth.ofBool a ⊓ Truth.ofBool b).isTrue = (a && b) := by simp
example (a b : Bool) : Truth.ofBool (a || !b) = Truth.ofBool a ⊔ (Truth.ofBool b).not := by simp

end CslibFrontierTests.SQL.Truth
