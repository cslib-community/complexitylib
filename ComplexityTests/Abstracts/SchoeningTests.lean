/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.SchoeningAbstract

/-!
# Regression tests for `SchoeningAbstract`

Concrete checks on the abstract's standard-basis arithmetic (truncated subtraction, and division
and remainder by zero, which do not fault) and on its formula encoding, and a non-vacuous
instantiation of `SchoeningAbstract.schoening3SAT` on a satisfiable 3-CNF with three variables at
word size `16`.
-/

namespace ComplexityTests.Abstracts.SchoeningTests

open ComplexityAbstracts.SchoeningAbstract

-- Truncated subtraction, and division and remainder by zero.
example : AluOp.eval .sub 2 5 = 0 := rfl
example : AluOp.eval .div 7 0 = 0 := rfl
example : AluOp.eval .mod 7 0 = 7 := rfl

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁ ∨ x₂)`: satisfiable, with clauses of at most three literals. -/
def φ : Formula 3 := [[(0, true), (1, true)], [(0, false), (1, true), (2, true)]]

-- The encoding: `n = 3`, then each clause as its length followed by the literal codes `2 v + b`.
example : encode φ = [3, 2, 1, 3, 3, 0, 3, 5] := rfl

theorem φ_satisfiable : Satisfiable φ := ⟨fun _ => true, by decide⟩

/-- With confidence `c = 1`, the input `3 :: 1 :: encode φ` has length `10`, `16`-bit words meet the
word-size condition, and the program fails with probability at most `e ^ (-1)`. -/
example : ∃ p : Program 24, ∃ T, HaltsWithin 16 p (init (3 :: 1 :: encode φ)) T ∧
    failure 16 p T (init (3 :: 1 :: encode φ)) ≤ Real.exp (-1) := by
  obtain ⟨p, hp⟩ := schoening3SAT
  obtain ⟨hhalt, -, -, -, hfail⟩ := hp 3 1 16 φ (by decide)
  exact ⟨p, _, hhalt, by simpa using hfail φ_satisfiable (by decide)⟩

end ComplexityTests.Abstracts.SchoeningTests
