/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.Sparsification

/-!
# Tests: algorithmic sparsification

The list-level sparsification step on concrete formulas: a heavy heart and its two children, a
sparse formula, normalization; the sparsification search on satisfiable, unsatisfiable, branching
and wide formulas, against exhaustive search; and the non-vacuity of the hypotheses of the search
and of the headline theorems.
-/

namespace ComplexityTests.FineGrained.Sparsification

open Cslib.Complexity Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification

/-- The thresholds for width three and `α = 1`: `θ 1 = 6`, `θ 2 = 6 ^ 3`. -/
private abbrev θ : ℕ → ℕ := Cslib.Logic.PL.ClauseSet.Sparsification.threshold 3 1

example : θ 0 = 1 ∧ θ 1 = 6 ∧ θ 2 = 216 := by decide

/-- A flower: six clauses of size two through the literal `x₀`. -/
private def ψ₆ : CNF ℕ := (List.range 6).map fun i => [(0, true), (i + 1, true)]

/-! ### The list-level step -/

/-- The literal `x₀` is a heavy heart of `ψ₆`: it lies in `θ 1 = 6` clauses of size two. -/
example : isSparse θ 3 ψ₆ = false := by decide

example : choice θ 3 ψ₆ = (2, [(0, true)]) := by decide

/-- The heart child: the clause `x₀` absorbs the flower. -/
example : next θ 3 ψ₆ false = [[(0, true)]] := by decide

/-- The petal child: the petals absorb the flower. -/
example : next θ 3 ψ₆ true = (List.range 6).map fun i => [(i + 1, true)] := by decide

example : isSparse θ 3 (next θ 3 ψ₆ true) = true := by decide

/-- Five clauses through `x₀` are not enough. -/
example : isSparse θ 3 (ψ₆.drop 1) = true := by decide

/-- Normalization removes repeated literals and clauses and the clauses containing others. -/
example : normalize ([[(0, true), (0, true)], [(0, true)], [(1, false), (0, true)]] : CNF ℕ) =
    [[(0, true)]] := by decide

example : normalize ([[(1, false), (0, true)], [(0, true), (1, false)]] : CNF ℕ) =
    [[(1, false), (0, true)]] := by decide

/-! ### The search -/

example : Sparsify.search 3 1 3 1 BruteForce.search
    [[(0, true), (1, false)], [(1, true)], [(0, false), (2, true)]] = true := by decide

example : Sparsify.search 3 1 3 1 BruteForce.search [[(0, true)], [(0, false)]] = false := by
  decide

/-- The formula with no clauses is satisfiable, and the empty clause is not. -/
example : Sparsify.search 3 1 3 1 BruteForce.search [] = true := by decide

example : Sparsify.search 3 1 3 1 BruteForce.search [[]] = false := by decide

/-- A search through both children of a heavy heart. -/
example : Sparsify.search 3 1 3 7 BruteForce.search ψ₆ = true := by decide

/-- Wider formulas start from the formula without clauses; `k`-SAT rejects them separately. -/
example : Sparsify.root 1 ψ₆ = [] := by decide

example : Sparsify.root 2 ψ₆ = ψ₆ := by decide

/-! ### Non-vacuity -/

/-- The bound on the leaves holds for width one. -/
theorem leafBound_one : Sparsify.LeafBound 1 1 1 := fun N => by simpa using Nat.one_le_two_pow

/-- The search decides `1`-SAT, with exhaustive search at the leaves. -/
example (φ : CNF ℕ) (hφ : ∀ c ∈ φ, c.length ≤ 1) :
    Sparsify.search 1 1 1 1 BruteForce.search φ = true ↔ φ.Satisfiable :=
  Sparsify.search_eq_true_iff le_rfl le_rfl le_rfl leafBound_one
    (fun ψ _ => (BruteForce.search_eq_true_iff ψ).trans mem_SAT) hφ

/-- A decider for 3SAT in the number of clauses: exhaustive search, as `n ≤ 3 m`. -/
example : DecidableInExpTime (KSAT 3) encCNF List.length (3 * 1) :=
  (KSAT_decidableInExpTime_one 3).length_of_numVars zero_le_one

/-- The two directions together: back from clauses to variables. -/
example : ∃ c : ℕ, DecidableInExpTime (KSAT 3) encCNF CNF.numVars (1 + c * (3 * 1)) := by
  obtain ⟨c, hc⟩ := exists_decidableInExpTime_numVars_of_length 3 one_pos
  exact ⟨c, hc _ (by norm_num) ((KSAT_decidableInExpTime_one 3).length_of_numVars zero_le_one)⟩

example (h : ¬DecidableInSubexpTime ThreeSAT encCNF List.length) : 0 < satExponent 3 :=
  ETH_iff_satExponent_pos.mp (ETH_iff_not_decidableInSubexpTime_length.mpr h)

end ComplexityTests.FineGrained.Sparsification
