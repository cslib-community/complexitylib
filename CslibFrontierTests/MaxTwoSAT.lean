/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.MaxTwoSAT

/-!
# MAX 2-SAT: tests

The gadget table of Garey, Johnson and Stockmeyer on all of its cases that matter; membership in
`MaxTwoSAT` of an unsatisfiable 2-CNF formula with a small target and its failure for a larger
target or a wide clause; the reduction on concrete formulas, including a satisfiable and an
unsatisfiable exact 3-CNF formula, the empty formula, and the fixed no-instance for a clause of
another width; and the headline results.
-/

namespace ComplexityTests.MaxTwoSAT

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Headline results -/

example : MaxTwoSAT ∈ NP (encPair encCNF encNat) ∧
    NPHard (encPair encCNF encNat) MaxTwoSAT ∧
    PolyTimeReducible encCNF (encPair encCNF encNat) ThreeSAT MaxTwoSAT ∧
    PolyTimeReducible encCNF (encPair encCNF encNat) ExactThreeSAT MaxTwoSAT :=
  ⟨MaxTwoSAT_npComplete.1, MaxTwoSAT_npComplete.2, polyTimeReducible_ThreeSAT_MaxTwoSAT,
    polyTimeReducible_ExactThreeSAT_MaxTwoSAT⟩

/-! ### The gadget table -/

-- One, two or three true literals: the majority value of `w` reaches seven.
example : MaxTwoSAT.gadgetScore true false false false = 7 := by decide
example : MaxTwoSAT.gadgetScore true true false true = 7 := by decide
example : MaxTwoSAT.gadgetScore true true true true = 7 := by decide
-- With two true literals both values of `w` reach seven; with one, `w = true` gives six.
example : MaxTwoSAT.gadgetScore true true false false = 7 := by decide
example : MaxTwoSAT.gadgetScore true false false true = 6 := by decide
-- With three true literals `w = false` gives six: the three negated pairs fail.
example : MaxTwoSAT.gadgetScore true true true false = 6 := by decide
-- No true literal: six with `w = false` and four with `w = true`.
example : MaxTwoSAT.gadgetScore false false false false = 6 := by decide
example : MaxTwoSAT.gadgetScore false false false true = 4 := by decide

-- The table is read off the ten clauses, for a concrete clause `x₀ ∨ ¬x₁ ∨ x₂` and `w = 3`.
-- Making only `x₁` true falsifies the clause: six with `w` false, four with `w` true.
example : (MaxTwoSAT.gadget (0, true) (1, false) (2, true) 3).length = 10 := by decide
example : (MaxTwoSAT.gadget (0, true) (1, false) (2, true) 3).countP
    (Clause.eval fun v => v == 1) = 6 := by decide
example : (MaxTwoSAT.gadget (0, true) (1, false) (2, true) 3).countP
    (Clause.eval fun v => v == 1 || v == 3) = 4 := by decide
-- Making only `x₀` true satisfies `x₀` and `¬x₁`: seven with `w` false.
example : (MaxTwoSAT.gadget (0, true) (1, false) (2, true) 3).countP
    (Clause.eval fun v => v == 0) = 7 := by decide

/-! ### Membership in `MaxTwoSAT` -/

/-- The unsatisfiable 2-CNF formula `x₀ ∧ ¬x₀`. -/
private def contra : CNF ℕ := [[(0, true)], [(0, false)]]

-- One of its two clauses can be satisfied, but not both.
example : (contra, 1) ∈ MaxTwoSAT :=
  mem_MaxTwoSAT_iff.2 ⟨by decide, fun _ => true, by decide⟩

example : (contra, 2) ∉ MaxTwoSAT := by
  rintro ⟨-, σ, hσ⟩
  cases h : σ 0 <;> simp [contra, h] at hσ

-- A clause of three literals is not allowed, even with target `0`.
example : ([[(0, true), (1, true), (2, true)]], 0) ∉ MaxTwoSAT := fun h => by
  have := h.1 _ List.mem_cons_self
  simp at this

-- The verifier on the first-occurrence certificate `[true]`.
example : MaxTwoSAT.verifier ((contra, 1), [true]) = true := by decide
example : MaxTwoSAT.verifier ((contra, 2), [true]) = false := by decide

/-! ### The reduction -/

/-- The satisfiable exact 3-CNF formula `(x₀ ∨ x₁ ∨ x₂) ∧ (¬x₀ ∨ ¬x₁ ∨ x₂)`. -/
private def sat3 : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, false), (1, false), (2, true)]]

/-- The unsatisfiable exact 3-CNF formula `(x₀ ∨ x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀ ∨ ¬x₀)`, with repeated
literals. -/
private def unsat3 : CNF ℕ :=
  [[(0, true), (0, true), (0, true)], [(0, false), (0, false), (0, false)]]

-- Two gadgets, twenty clauses, target fourteen.
example : (toMaxTwoSAT sat3).1.length = 20 := by decide
example : (toMaxTwoSAT sat3).2 = 14 := by decide

-- The source variables are doubled and the fresh variables are `1` and `3`.
example : (toMaxTwoSAT sat3).1.take 4 = [[(0, true)], [(2, true)], [(4, true)], [(1, true)]] := by
  decide

example : toMaxTwoSAT sat3 ∈ MaxTwoSAT :=
  (mem_MaxTwoSAT_toMaxTwoSAT_iff _).2 ⟨by decide, fun v => v == 2, by decide⟩

example : toMaxTwoSAT unsat3 ∉ MaxTwoSAT := by
  rw [mem_MaxTwoSAT_toMaxTwoSAT_iff]
  rintro ⟨-, σ, hσ⟩
  cases h : σ 0 <;> simp [unsat3, CNF.eval, h] at hσ

-- The empty formula maps to the empty formula with target `0`.
example : toMaxTwoSAT [] = ([], 0) := by decide

-- A clause of two literals, an empty clause or a clause of four literals gives the fixed
-- no-instance; `ThreeSAT` pads short clauses first, through `toExactThreeSAT`.
example : toMaxTwoSAT [[(0, true), (1, true)]] = ([[]], 1) := by decide
example : toMaxTwoSAT [[]] = ([[]], 1) := by decide
example : toMaxTwoSAT [[(0, true), (1, true), (2, true), (3, true)]] = ([[]], 1) := by decide
example : ([[]], 1) ∉ MaxTwoSAT := by
  rintro ⟨-, σ, hσ⟩
  simp at hσ

end ComplexityTests.MaxTwoSAT
