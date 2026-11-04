/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Tseitin

/-!
# Tseitin formulas of De Morgan circuits

The gate list below computes `x₀ ∧ ¬x₁` on two inputs, with the negation at wire `2` and the
conjunction at wire `3`. Its Tseitin formula with the output fixed is satisfiable, and fixing the
first input to `false` makes it unsatisfiable, both through `satisfiable_tseitinSatCNF_iff`.
-/

namespace ComplexityTests.CircuitTseitin

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL

/-- `x₀ ∧ ¬x₁`: the negation at wire `2`, the conjunction at wire `3`. -/
private def gates : List (Op × List ℕ) := [(.not, [1]), (.and, [0, 2])]

private theorem isCodeFrom_gates : Program.IsCodeFrom signature 2 0 gates := by decide

-- One unit clause for the output, one for each fixed input, three clauses per gate.
example : tseitinSatCNF [false] 2 gates 3 =
    [[(3, true), (3, true), (3, true)], [(0, false), (0, false), (0, false)],
      [(2, true), (1, true), (1, true)], [(2, false), (1, false), (1, false)],
      [(2, true), (1, true), (1, true)],
      [(3, false), (0, true), (0, true)], [(3, false), (2, true), (2, true)],
      [(3, true), (0, false), (2, false)]] := rfl

example : (tseitinSatCNF [false] 2 gates 3).length = 8 := by
  rw [length_tseitinSatCNF]; rfl

-- With the output fixed to `true`, the formula is satisfiable: the input `[true, false]`.
example : (tseitinSatCNF [] 2 gates 3).Satisfiable :=
  (satisfiable_tseitinSatCNF_iff isCodeFrom_gates (by simp) (by decide)).2
    ⟨[true, false], rfl, List.nil_prefix, by decide⟩

-- Fixing the first input to `false` leaves no satisfying input, so no satisfying assignment.
example : ¬ (tseitinSatCNF [false] 2 gates 3).Satisfiable := by
  rw [satisfiable_tseitinSatCNF_iff isCodeFrom_gates (by simp) (by decide)]
  rintro ⟨y, hy, ⟨r, rfl⟩, hout⟩
  rcases r with _ | ⟨b, _ | ⟨_, _⟩⟩ <;> simp at hy
  cases b <;> revert hout <;> decide

-- The assignment that evaluates the gates on `[true, false]` satisfies the Tseitin formula.
example : (tseitinCNF 2 gates).eval (fun w => [true, false, true, true].getD w false) = true := by
  decide

-- An assignment that is not consistent with the negation gate does not.
example :
    (tseitinCNF 2 gates).eval (fun w => [true, false, false, false].getD w false) = false := by
  decide

end ComplexityTests.CircuitTseitin
