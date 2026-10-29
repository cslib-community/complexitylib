/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.ParityTests
import Mathlib.Tactic.FinCases

/-! Tests for greedy parity tests. -/

namespace ComplexityTests.ParityTests

open Finset Cslib.BitString Cslib.Logic.PL

/-! ### Rows and parities of test lists -/

/-- Repeated indices cancel: `((0, 1), (2, 1), (0, 1))` has row `(0, 0, 1)`. -/
example : testRow (m := 3) ![(0, true), (2, true), (0, true)] = ![false, false, true] := by
  decide

/-- The parity of a list is the inner product of its row with the string. -/
example : testParity (m := 3) ![(0, true), (2, true), (0, true)] ![true, true, true] = true := by
  decide

/-! ### Counting rejecting lists -/

/-- One list `((0, 1))` of length one rejects `(1, 0)`, matching `2 · 1 = 2 ^ 1 (2 ^ 1 − 1 ^ 1)`. -/
example : #{γ : Fin 1 → Fin 2 × Bool | testParity γ ![true, false] = true} = 1 := by
  decide

example : 2 * #{γ : Fin 1 → Fin 2 × Bool | testParity γ ![true, false] = true} =
    2 ^ 1 * (2 ^ 1 - 1 ^ 1) := by
  rw [two_mul_card_testParity_eq_true]
  decide

/-- A quarter of the lists of length two reject a string of length four with two ones. -/
example : (2 * 4) ^ 2 ≤
    4 * #{γ : Fin 2 → Fin 4 × Bool | testParity γ ![true, true, false, false] = true} :=
  pow_le_four_mul_card_testParity_eq_true _ (by decide) (by decide)

/-- The support hypothesis is needed: lists of length one reject a single one in four positions
only once in eight. -/
example : 4 * #{γ : Fin 1 → Fin 4 × Bool | testParity γ ![true, false, false, false] = true} <
    (2 * 4) ^ 1 := by
  decide

/-! ### Violation vectors -/

/-- The formula `x₀ ∧ x₁`, as two unit clauses. -/
def andFormula : CNF (Fin 2) := [[(0, true)], [(1, true)]]

example : andFormula.violations ![true, false] ⟨0, by decide⟩ = false ∧
    andFormula.violations ![true, false] ⟨1, by decide⟩ = true := by
  decide

example : andFormula.violations ![true, true] = 0 ∧ andFormula.eval ![true, true] = true :=
  ⟨by decide, (CNF.violations_eq_zero_iff _ _).mp (by decide)⟩

/-- With no rows, all four assignments pass: one satisfying and three bad. -/
example : numPassing andFormula.violations [] = 1 + 3 := by
  rw [numPassing_eq]
  decide

/-! ### A complete greedy run -/

/-- The formula `x₀` on one variable. Its nonsatisfying assignment violates its single clause, so
the support hypothesis holds without initial rows. -/
def unitFormula : CNF (Fin 1) := [[(0, true)]]

/-- The list `((0, 1))`, whose row rejects the nonsatisfying assignment. -/
def unitList : Fin 1 → Fin unitFormula.length × Bool := fun _ => (⟨0, by decide⟩, true)

/-- The greedy rows: `i` copies of the row of `unitList`. -/
def unitRows (i : ℕ) : List (Fin unitFormula.length → Bool) :=
  List.replicate i (testRow unitList)

theorem accepts_unitRows (i : ℕ) (σ : Fin 1 → Bool) :
    PassesTests unitFormula.violations (unitRows i ++ [testRow unitList]) σ ↔
      testRow unitList ⬝ᵥ unitFormula.violations σ = false := by
  simp only [PassesTests, unitRows, List.mem_append, List.mem_replicate, List.mem_singleton]
  constructor
  · exact fun h => h _ (Or.inr rfl)
  · rintro h r (⟨-, rfl⟩ | rfl) <;> exact h

theorem numPassing_unitRows (i : ℕ) :
    numPassing unitFormula.violations (unitRows i ++ [testRow unitList]) = 1 := by
  simp only [numPassing, accepts_unitRows]
  decide

/-- The greedy procedure on `x₀`: three rounds leave exactly the one satisfying assignment, so the
hypotheses of `CNF.numPassing_greedy` are satisfiable. -/
example : numPassing unitFormula.violations (unitRows (3 * Fintype.card (Fin 1))) = 1 := by
  rw [CNF.numPassing_greedy unitFormula (P := 1) (by decide) le_rfl unitRows
    (fun σ _ h => by
      have : σ = ![false] := by funext i; fin_cases i; simpa [unitFormula, CNF.eval,
        Clause.eval, Literal.eval] using h
      subst this
      decide)
    (fun _ => unitList) (fun i => List.replicate_succ' ..)
    (fun i γ' => by
      rw [numPassing_unitRows, numPassing_eq]
      exact le_add_of_le_left (by decide))]
  decide

end ComplexityTests.ParityTests
