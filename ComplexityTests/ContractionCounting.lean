/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.ContractionCounting

/-! # Model counting by tensor contraction: checked instances

The clause network of a small formula with a repeated variable, its bipartition, admissibility
and contraction, and the fixed-density counter of Theorem 1.1. -/

namespace ComplexityTests.ContractionCounting

open Cslib.Logic.PL Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ClauseNetwork
  Cslib.Complexity Cslib.Complexity.ContractionCounting Cslib.Complexity.CountingSimulation

/-- `(x₀ ∨ ¬x₁) ∧ (x₁ ∨ x₀ ∨ x₁) ∧ ¬x₂`: three clauses, six occurrences, three variables. -/
def φ₀ : CNF ℕ := [[(0, true), (1, false)], [(1, true), (0, true), (1, true)], [(2, false)]]

-- The chains: the previous occurrence of each occurrence of `x₀, x₁, x₁, x₀, x₁, x₂`.
example : (List.range 6).map (prev (occurrences φ₀)) = [0, 1, 1, 0, 2, 5] := by decide

example : clausePorts (occurrences φ₀) 1 = [6, 9, 12] := by decide

example : qPorts (occurrences φ₀) 1 = [3, 4, 5, 8] := by decide

example : (clauseNetwork 3 φ₀).2.numEdges = 18 ∧ (clauseNetwork 3 φ₀).1 = 9 ∧
    (clauseNetwork 3 φ₀).2.vertices.length = 15 := by decide

example : (clauseNetwork 3 φ₀).2.IsRowsFirstBipartite (clauseNetwork 3 φ₀).1 :=
  isRowsFirstBipartite_clauseNetwork 3 φ₀

example : (clauseNetwork 3 φ₀).2.maxDegree = 4 := by decide

-- The guard accepts `φ₀`, so its network is admissible at its number of edges.
example : ExplicitAdmissible (3 + 4) 18 (clauseNetwork 3 φ₀) :=
  explicitAdmissible_clauseNetwork (φ := φ₀) (by decide)

example : (clauseNetwork 3 φ₀).2.contraction = φ₀.modelCount :=
  contraction_clauseNetwork (by decide)

-- The guard rejects the empty formula, a formula with an empty clause and a clause too wide.
example : guard 3 [] = false ∧ guard 3 [[(0, true)], []] = false ∧
    guard 1 [[(0, true), (1, true)]] = false := by decide

example : count 3 ([] : CNF ℕ) = 1 := count_eq (by simp)

example : count 3 ([[(0, true)], []] : CNF ℕ) = 0 := by
  rw [count_eq (by decide), ← CNF.modelCountOn_vars, CNF.modelCountOn_eq_zero_of_nil_mem (by simp)]

-- The counter for width three, and its fixed-density form.
example : ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
    (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → count φ = φ.modelCount) ∧
    Turing.MultiTapeTM.ComputableInO count encCNF Turing.MultiTapeTM.encNat
      (fun φ => 2 ^ (A * (φ.length + 1) / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
        ((encCNF φ).length + 1) ^ e)
      (fun φ => ((encCNF φ).length + 1) ^ b) :=
  exists_modelCounter 3

-- `φ₀` meets the density bound `m ≤ 1 · n` of the fixed-density statement.
example : φ₀.length ≤ 1 * φ₀.numVars := by decide

end ComplexityTests.ContractionCounting
