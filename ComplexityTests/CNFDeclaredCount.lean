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

-- Other declared and occurring model counts across unit, tautological and undeclared variables.
example (n : ℕ) :
    CNF.modelCountOn ([[]] : CNF Empty) ∅ = 0 ∧
    CNF.modelCountOn ([] : CNF (Fin 0)) Finset.univ = 1 ∧
    CNF.modelCountOn ([] : CNF (Fin n)) Finset.univ = 2 ^ n ∧
    CNF.modelCountOn ([[]] : CNF ℕ) (Finset.range 4) = 0 ∧
    CNF.modelCountOn ([[(0, true)]] : CNF ℕ) (Finset.range 3) = 4 ∧
    CNF.modelCountOn ([[(1, true)]] : CNF (Fin 3)) Finset.univ = 4 ∧
    CNF.modelCount ([[(0, true)]] : CNF ℕ) = 1 ∧
    CNF.modelCount ([] : CNF ℕ) = 1 ∧
    CNF.modelCountOn ([[(0, true), (0, false)]] : CNF ℕ) (Finset.range 3) =
      CNF.modelCountOn ([] : CNF ℕ) (Finset.range 3) ∧
    (let φ : CNF ℕ := [[(0, true)]];
      ¬φ.vars.toFinset ⊆ (∅ : Finset ℕ) ∧
        φ.modelCountOn ∅ ≠ 2 ^ ((∅ : Finset ℕ).card - φ.numVars) * φ.modelCount) :=
  ⟨by decide, by decide, by simp, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide⟩

private def repeated : CNF ℕ :=
  [[(9, true), (9, true), (1000000000000, false)],
    [(9, true), (9, true), (1000000000000, false)]]

-- Dense renaming keeps literal order, repeats, and clause widths while contrasting with
-- first-occurrence `compact`.
example :
    repeated.relabel repeated.distinctVars.idxOf =
      [[(0, true), (0, true), (1, false)], [(0, true), (0, true), (1, false)]] ∧
    repeated.compact =
      [[(0, true), (0, true), (2, false)], [(0, true), (0, true), (2, false)]] ∧
    repeated.modelCount = 3 ∧
    (repeated.relabel repeated.distinctVars.idxOf).vars.toFinset = Finset.range 2 ∧
    (repeated.relabel repeated.distinctVars.idxOf).modelCountOn (Finset.range 2) = 3 ∧
    CNF.modelCountOn (CNF.relabel (CNF.distinctVars ([] : CNF ℕ)).idxOf []) (Finset.range 0) = 1 ∧
    (repeated.relabel repeated.distinctVars.idxOf).map List.length = repeated.map List.length := by
  decide

universe u

-- The transport preserves the raw width contract, rather than deduplicating literals.
example {V : Type u} [DecidableEq V] (φ : CNF V) :
    (φ.relabel φ.distinctVars.idxOf).map List.length = φ.map List.length := by
  simp [CNF.relabel, Clause.relabel]

end ComplexityTests.CNFDeclaredCount
