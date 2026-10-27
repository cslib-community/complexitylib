/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.ExactTests

/-! Tests for exact parity tests of sparse CNF formulas. -/

namespace ComplexityTests.ExactTests

open Finset Cslib.BitString Cslib.Logic.PL

/-- The formula `x₀ ∧ x₁` on two variables. -/
def andFormula : CNF (Fin 2) := [[(0, true)], [(1, true)]]

/-- Its initial tests: at most six rows, and every passing assignment that falsifies the formula
violates at least one clause, so its violation vector is nonzero. -/
example : ∃ A₀ : List (Fin andFormula.length → Bool), A₀.length ≤ 6 ∧
    ∀ σ, PassesTests andFormula.violations A₀ σ → andFormula.eval σ = false →
      0 < weight (andFormula.violations σ) := by
  obtain ⟨A₀, hlen, -, hinit⟩ := andFormula.exists_initialTests (B := 1) (by decide) le_rfl
    (by decide)
  refine ⟨A₀, by simpa using hlen, fun σ hσ hf => ?_⟩
  have := hinit σ hσ hf
  rcases Nat.eq_zero_or_pos (weight (andFormula.violations σ)) with h | h
  · rw [h, mul_zero] at this
    exact absurd this (by decide)
  · exact h

end ComplexityTests.ExactTests
