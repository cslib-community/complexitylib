/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.DFS.SCC
public import CslibFrontier.Algorithms.Lean.TwoSAT
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.HornSAT

/-!
# Strongly connected components, linear-time 2-SAT, and polynomial-time 2-SAT/HornSAT tests

Kernel-checked examples (zero `native_decide`) exercising:
1. Kosaraju's strongly connected components (`Cslib.Algorithms.Lean.DFS.sccs`, `sccsM`,
   `indexComponents`, `IsSCCCondensation`) on DAGs, cycles, and multi-component graphs with exact
   `3 * (|V| + |E|)` tick counts;
2. Aspvall–Plass–Tarjan linear-time 2-SAT in `TimeM` (`Cslib.Algorithms.Lean.TwoSAT`);
3. Native multi-tape Turing-machine polynomial-time `TwoSAT` decision and witness construction
   (`Cslib.Complexity.TwoSAT.solve`, `TwoSAT.assignment`, `TwoSAT.mem_P`), including sparse binary
   variable names;
4. HornSAT least-model minimality (`HornSAT.isLeast_assignment`) and non-uniqueness
   (`HornSAT.exists_multiple_models`).
-/

public section

namespace CslibFrontierTests.SCCAndTwoSAT

open Cslib.Algorithms.Lean.DFS
open Cslib.Logic.PL
open Cslib.Complexity

/-! ### 1. Kosaraju strongly connected components -/

/-- Diamond DAG `0 → 1, 0 → 2, 1 → 3, 2 → 3`: four singleton SCCs and `3 * (4 + 4) = 24` ticks. -/
def diamond : Fin 4 → List (Fin 4)
  | 0 => [1, 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => []

example : sccs diamond (List.finRange 4) = [[0], [2], [1], [3]] := by decide +kernel

example : (sccsM diamond (List.finRange 4)).time = 24 := by decide +kernel

/-- Triangle `0 → 1 → 2 → 0`: one SCC of size `3` and `3 * (3 + 3) = 18` ticks. -/
def triangle : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0]

example : (sccs triangle (List.finRange 3)).length = 1 := by decide +kernel

example : (sccsM triangle (List.finRange 3)).time = 18 := by decide +kernel

example :
    let idx := indexComponents (sccs triangle (List.finRange 3))
    idx 0 = 0 ∧ idx 1 = 0 ∧ idx 2 = 0 := by decide +kernel

/-- Two 2-cycles joined by a bridge `0 ↔ 1 → 2 ↔ 3`: `4` vertices, `5` edges, `27` ticks. -/
def twoCycles : Fin 4 → List (Fin 4)
  | 0 => [1]
  | 1 => [0, 2]
  | 2 => [3]
  | 3 => [2]

example : (sccs twoCycles (List.finRange 4)).length = 2 := by decide +kernel

example : (sccsM twoCycles (List.finRange 4)).time = 27 := by decide +kernel

example :
    let comps := sccs twoCycles (List.finRange 4)
    let idx := indexComponents comps
    idx 0 = 0 ∧ idx 1 = 0 ∧ idx 2 = 1 ∧ idx 3 = 1 ∧ (indexComponentsM comps).time = 6 := by
  decide +kernel

example : IsSCCCondensation twoCycles (sccs twoCycles (List.finRange 4)) :=
  isSCCCondensation_sccs List.mem_finRange

/-! ### 2. Linear-time `TimeM` 2-SAT solver -/

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ x₂)` forces `x₂ = true`. -/
def satFin : CNF (Fin 3) :=
  [[(0, true), (1, true)], [(0, false), (2, true)], [(1, false), (2, true)]]

example :
    ((Cslib.Algorithms.Lean.TwoSAT.solveFin 3 satFin).any fun σ =>
      satFin.eval σ && σ 2) = true := by decide +kernel

example :
    (Cslib.Algorithms.Lean.TwoSAT.solveFinM 3 satFin).time ≤ 12 * 3 + 8 * satFin.length + 1 :=
  Cslib.Algorithms.Lean.TwoSAT.time_solveFinM_le 3 satFin

/-- Symmetry-breaking `x₀ ↔ ¬x₁`: two incomparable literal SCCs. -/
def xorTwo : CNF ℕ :=
  [[(0, true), (1, true)], [(0, false), (1, false)]]

example :
    ((Cslib.Algorithms.Lean.TwoSAT.solveNat xorTwo).any fun σ =>
      xorTwo.eval σ && (σ 0 == !σ 1)) = true := by decide +kernel

/-- Unsatisfiable four-clause 2-CNF `(x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)`. -/
def unsatTwo : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)],
   [(0, false), (1, true)], [(0, false), (1, false)]]

example : Cslib.Algorithms.Lean.TwoSAT.solveNat unsatTwo = none := by decide +kernel

example : (Cslib.Algorithms.Lean.TwoSAT.solveNat ([] : CNF ℕ)).isSome = true := by decide +kernel

example : Cslib.Algorithms.Lean.TwoSAT.solveNat ([[]] : CNF ℕ) = none := by decide +kernel

example :
    Cslib.Algorithms.Lean.TwoSAT.solveNat ([[(0, true), (1, true), (2, true)]] : CNF ℕ) = none := by
  decide +kernel

/-! ### 3. Multi-tape polynomial-time `TwoSAT` decision and witness construction -/

example : TwoSAT ∈ P encCNF := TwoSAT.mem_P

example : TwoSAT.solve ([] : CNF ℕ) = true := by decide

example : TwoSAT.solve ([[]] : CNF ℕ) = false := by decide

example : TwoSAT.solve ([[(0, true), (1, true), (2, true)]] : CNF ℕ) = false := by decide

example : TwoSAT.solve xorTwo = true ∧ xorTwo.eval (TwoSAT.assignment xorTwo) = true := by decide

example : TwoSAT.solve unsatTwo = false := by decide

/-- Sparse binary variable names (`2 ^ 100` and `7`) require only occurrence-bounded passes. -/
def sparseSat : CNF ℕ :=
  [[(2 ^ 100, true), (7, false)], [(2 ^ 100, false)]]

example :
    TwoSAT.solve sparseSat = true ∧
      sparseSat.eval (TwoSAT.assignment sparseSat) = true ∧
      TwoSAT.assignment sparseSat (2 ^ 100) = false ∧
      TwoSAT.assignment sparseSat 7 = false := by decide

/-! ### 4. HornSAT least model and non-uniqueness -/

theorem horn_implication_least :
    let φ : CNF ℕ := [[(0, false), (1, true)]]
    IsLeast {σ : ℕ → Bool | φ.eval σ = true} (HornSAT.assignment φ) := by
  intro φ
  have hsat : φ ∈ HornSAT := (HornSAT.solve_eq_true_iff φ).mp (by decide)
  exact HornSAT.isLeast_assignment hsat.1 hsat.2

example :
    ∃ (φ : CNF ℕ) (σ : ℕ → Bool),
      φ ∈ HornSAT ∧ φ.eval σ = true ∧ ∃ v ∈ φ.vars, σ v ≠ HornSAT.assignment φ v :=
  HornSAT.exists_multiple_models

end CslibFrontierTests.SCCAndTwoSAT
