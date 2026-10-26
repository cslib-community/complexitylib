/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
import Complexity.Logics.Propositional.CNF.Compact

public section

open Cslib.Logic.PL

namespace ComplexityTests.CNFDeclaredCount

-- The ambient variable type and the declared set can both be empty.
theorem empty_declared_count : CNF.modelCountOn ([] : CNF Empty) ∅ = 1 := by decide

example : CNF.modelCountOn ([[]] : CNF Empty) ∅ = 0 := by decide

example : CNF.modelCountOn ([] : CNF (Fin 0)) Finset.univ = 1 := by decide

example (n : ℕ) : CNF.modelCountOn ([] : CNF (Fin n)) Finset.univ = 2 ^ n := by simp

-- An empty clause rejects every assignment even when there are unused declared variables.
example : CNF.modelCountOn ([[]] : CNF ℕ) (Finset.range 4) = 0 := by decide

-- A positive literal uses only one of the three declared variables.
example : CNF.modelCountOn ([[(0, true)]] : CNF ℕ) (Finset.range 3) = 4 := by decide

example : CNF.modelCountOn ([[(1, true)]] : CNF (Fin 3)) Finset.univ = 4 := by decide

-- The original occurring-variable count has not acquired the ambient factor.
example : CNF.modelCount ([[(0, true)]] : CNF ℕ) = 1 := by decide

example : CNF.modelCount ([] : CNF ℕ) = 1 := by decide

-- Removing a tautological clause must retain its declared-variable choices.
example :
    CNF.modelCountOn ([[(0, true), (0, false)]] : CNF ℕ) (Finset.range 3) =
      CNF.modelCountOn ([] : CNF ℕ) (Finset.range 3) := by decide

-- Containment is essential: an undeclared positive literal is false under the specified extension.
example :
    let φ : CNF ℕ := [[(0, true)]]
    ¬φ.vars.toFinset ⊆ (∅ : Finset ℕ) ∧
      φ.modelCountOn ∅ ≠ 2 ^ ((∅ : Finset ℕ).card - φ.numVars) * φ.modelCount := by decide

private def repeated : CNF ℕ :=
  [[(9, true), (9, true), (1000000000000, false)],
    [(9, true), (9, true), (1000000000000, false)]]

-- Dense renaming keeps literal order, repeats, and both original clauses.
example : repeated.relabel repeated.distinctVars.idxOf =
    [[(0, true), (0, true), (1, false)], [(0, true), (0, true), (1, false)]] := by decide

-- The old first-occurrence numbering deliberately still has a gap.
example : repeated.compact =
    [[(0, true), (0, true), (2, false)], [(0, true), (0, true), (2, false)]] := by decide

example : repeated.modelCount = 3 := by decide

example : (repeated.relabel repeated.distinctVars.idxOf).vars.toFinset = Finset.range 2 := by
  decide

example : (repeated.relabel repeated.distinctVars.idxOf).modelCountOn (Finset.range 2) = 3 := by
  decide

-- Empty input needs no impossible total map from ℕ to Fin 0.
example :
    CNF.modelCountOn (CNF.relabel (CNF.distinctVars ([] : CNF ℕ)).idxOf []) (Finset.range 0) =
      1 := by decide

universe u

-- The transport preserves the raw width contract, rather than deduplicating literals.
example {V : Type u} [DecidableEq V] (φ : CNF V) :
    (φ.relabel φ.distinctVars.idxOf).map List.length = φ.map List.length := by
  simp [CNF.relabel, Clause.relabel]

example {V : Type u} [DecidableEq V] (φ : CNF V) :
    (φ.relabel φ.distinctVars.idxOf).modelCountOn (Finset.range φ.numVars) = φ.modelCount :=
  φ.modelCountOn_dense_relabel

end ComplexityTests.CNFDeclaredCount
