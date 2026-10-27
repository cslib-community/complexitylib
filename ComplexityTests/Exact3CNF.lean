/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.ThreeCNF
import Complexity.Logics.Propositional.CNF.ThreeCNF.Exact
import Complexity.Logics.Propositional.CNF.ThreeOccurrence

/-!
# Tests for the count-preserving split into width three
-/

namespace ComplexityTests.Exact3CNF

open Cslib.Logic.PL

/-- A clause of width five becomes two OR gates, `z₀ ↔ x₀ ∨ x₁` and `z₁ ↔ z₀ ∨ ¬x₂`, followed by
the clause `z₁ ∨ x₃ ∨ x₄`. -/
example :
    Clause.orSplit3 (fun j => Sum.inr (0, j)) 0
        ([(Sum.inl 0, true), (Sum.inl 1, true), (Sum.inl 2, false), (Sum.inl 3, true),
          (Sum.inl 4, true)] : Clause (ℕ ⊕ (ℕ × ℕ))) =
      [[(Sum.inl 0, false), (Sum.inr (0, 0), true)], [(Sum.inl 1, false), (Sum.inr (0, 0), true)],
        [(Sum.inl 0, true), (Sum.inl 1, true), (Sum.inr (0, 0), false)],
        [(Sum.inr (0, 0), false), (Sum.inr (0, 1), true)],
        [(Sum.inl 2, true), (Sum.inr (0, 1), true)],
        [(Sum.inr (0, 0), true), (Sum.inl 2, false), (Sum.inr (0, 1), false)],
        [(Sum.inr (0, 1), true), (Sum.inl 3, true), (Sum.inl 4, true)]] := rfl

/-- Clauses of width at most three, including the empty clause, are kept. -/
example : Clause.orSplit3 (fun j => Sum.inr (0, j)) 0
    ([(Sum.inl 0, true), (Sum.inl 1, false)] : Clause (ℕ ⊕ (ℕ × ℕ))) =
      [[(Sum.inl 0, true), (Sum.inl 1, false)]] := rfl

example : Clause.orSplit3 (fun j => Sum.inr (0, j)) 0 ([] : Clause (ℕ ⊕ (ℕ × ℕ))) = [[]] := rfl

/-- One clause of width four has fifteen models. -/
theorem modelCount_width_four :
    CNF.modelCount ([[(0, true), (1, true), (2, true), (3, true)]] : CNF ℕ) = 15 := by decide

/-- Splitting it into OR gates keeps the fifteen models. -/
example :
    CNF.modelCount (CNF.toExact3CNF ([[(0, true), (1, true), (2, true), (3, true)]] : CNF ℕ)) =
      15 := by decide

/-- The satisfiability-preserving split `CNF.to3CNF` leaves its auxiliary variable free when both
halves of the clause hold, so it has `24 ≠ 15` models. -/
example :
    CNF.modelCount (CNF.to3CNF ([[(0, true), (1, true), (2, true), (3, true)]] : CNF ℕ)) =
      24 := by decide

/-- A formula with an empty clause stays unsatisfiable. -/
example : CNF.modelCount (CNF.toExact3CNF ([[], [(0, true)]] : CNF ℕ)) = 0 := by
  rw [CNF.modelCount_toExact3CNF]
  decide

/-- **Counting through width three and three occurrences.** Splitting into OR gates and then
splitting occurrences gives a formula of width at most three, with at most three occurrences of
every variable, and the same number of models. -/
example (φ : CNF ℕ) :
    (φ.toExact3CNF.toThreeOccurrence).modelCount = φ.modelCount ∧
      ∀ c ∈ φ.toExact3CNF.toThreeOccurrence, c.length ≤ 3 :=
  ⟨by rw [CNF.modelCount_toThreeOccurrence, CNF.modelCount_toExact3CNF],
    CNF.width_toThreeOccurrence (by decide) fun _ hc => CNF.length_le_three_of_mem_toExact3CNF hc⟩

/-- The split has at most seven times as many literal occurrences. -/
example (φ : CNF ℕ) : φ.toExact3CNF.vars.length ≤ 7 * φ.vars.length :=
  CNF.length_vars_toExact3CNF_le φ

end ComplexityTests.Exact3CNF
