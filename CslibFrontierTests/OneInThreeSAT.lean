/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Signed

/-! Clients of Exactly One 3SAT's NP-completeness, Arora–Barak 2007, Exercise 2 §16. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Complexity Cslib.Logic.PL

/-- `x₀ ⊕ ¬x₁` with `¬x₀`: negated literals are allowed. The assignment `x₀ = x₁ = false` makes
exactly one literal true in each clause. -/
example : [[(0, true), (1, false)], [(0, false)]] ∈ OneInThreeSAT :=
  ⟨by decide, fun _ => false, by decide⟩

/-- The same formula is outside the positive special case. -/
example : [[(0, true), (1, false)], [(0, false)]] ∉ PositiveOneInThreeSAT := fun h =>
  absurd ((PositiveOneInThreeSAT.syntaxCheck_iff _).mp
    ((PositiveOneInThreeSAT.mem_iff_syntaxCheck _).mp h).1).2 (by decide)

/-- `x₀` and `¬x₀` in one clause always have exactly one true literal. -/
example : [[(0, true), (0, false), (1, true)], [(1, false)]] ∈ OneInThreeSAT :=
  ⟨by decide, fun _ => false, by decide⟩

/-- Repeated occurrences count: `x₀ ∨ x₀` never has exactly one true occurrence. -/
example : [[(0, true), (0, true)]] ∉ OneInThreeSAT := by
  rintro ⟨-, σ, hσ⟩
  cases h : σ 0 <;> simp [CNF.evalOne, Clause.evalOne, h] at hσ

/-- A clause of width four is rejected, although it has an exact-one model. -/
example : [[(0, true), (1, true), (2, true), (3, true)]] ∉ OneInThreeSAT :=
  fun h => absurd (h.1 _ List.mem_cons_self) (by decide)

/-- The exercise's endpoint and its two halves. -/
example : NPComplete encCNF OneInThreeSAT := OneInThreeSAT_npComplete
example : OneInThreeSAT ∈ NP encCNF := OneInThreeSAT.mem_NP
example : PolyTimeReducible encCNF encCNF PositiveOneInThreeSAT OneInThreeSAT :=
  polyTimeReducible_PositiveOneInThreeSAT_OneInThreeSAT
