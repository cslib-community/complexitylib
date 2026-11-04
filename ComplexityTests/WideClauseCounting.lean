/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.WideClauseCounting
import Complexity.Computability.Complexity.Problems.SharpThreeSAT

/-! # Model counting for unbounded clause width: checked instances

A formula with a clause of width six, its count-preserving split into width three, and the
counter of `ContractionCounting.exists_modelCounter_unboundedWidth` evaluated on it. -/

namespace ComplexityTests.WideClauseCounting

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.ContractionCounting

/-- `(x₀ ∨ x₁ ∨ x₂ ∨ x₃ ∨ x₄ ∨ x₅) ∧ (¬x₀ ∨ x₆)`: a clause of width six, eight literal occurrences
and seven variables. -/
def φ₁ : CNF ℕ :=
  [[(0, true), (1, true), (2, true), (3, true), (4, true), (5, true)], [(0, false), (6, true)]]

/-- Of the `2 ^ 7` assignments, two falsify the wide clause (`x₀ = ⋯ = x₅ = false`) and `2 ^ 5`
falsify the second (`x₀ = true`, `x₆ = false`); no assignment falsifies both. -/
theorem modelCount_φ₁ : φ₁.modelCount = 94 := by decide

example : φ₁.vars.length = 8 ∧ φ₁.numVars = 7 := by decide

-- The split: width three, `6 + 6 · 3 + 2 = 26 ≤ 7 · 8` literal occurrences, the same count.
example : (toSharpThreeSAT φ₁).all (fun c => decide (c.length ≤ 3)) = true := by decide

example : (toSharpThreeSAT φ₁).vars.length = 26 := by decide

example : (toSharpThreeSAT φ₁).modelCount = 94 := by
  rw [modelCount_toSharpThreeSAT, modelCount_φ₁]

-- The counter for every width counts `φ₁`.
example : ∃ (count : CNF ℕ → ℕ) (A e b : ℕ), count φ₁ = 94 ∧
    Turing.MultiTapeTM.ComputableInO count encCNF Turing.MultiTapeTM.encNat
      (fun φ => 2 ^ (A * (φ.vars.length + 1) / Nat.sqrt (Nat.log 2 (φ.vars.length + 2))) *
        ((encCNF φ).length + 1) ^ e)
      (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_modelCounter_unboundedWidth
  exact ⟨count, A, e, b, (hcount φ₁).trans modelCount_φ₁, hc⟩

-- `φ₁` meets the linear-length hypothesis `N ≤ D n` with `D = 2`, although its widest clause has
-- six literals; formulas with many occurrences of few variables do not.
example : φ₁.vars.length ≤ 2 * φ₁.numVars := by decide

/-- `x₀ ∧ x₀ ∧ x₀`: three occurrences of one variable. -/
def φ₂ : CNF ℕ := [[(0, true)], [(0, true)], [(0, true)]]

example : ¬ φ₂.vars.length ≤ 2 * φ₂.numVars := by decide

end ComplexityTests.WideClauseCounting
