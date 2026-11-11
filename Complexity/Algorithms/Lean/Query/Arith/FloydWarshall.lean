/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.FreeM.Tabulate
public import Complexity.Algorithms.ShortestPaths.FloydWarshall
public import Cslib.Algorithms.Lean.Query.Arith.Defs
import Mathlib.Tactic.Ring

/-!
# Floyd–Warshall as an arithmetic query program

`Cslib.Query.floydWarshall n W` runs Floyd–Warshall on an `n`-vertex weight matrix in the
arithmetic query model `FreeM (ArithQuery S)`: it starts from `withOneDiag W` and, for the pivots
`k = 0, …, n - 1`, replaces every entry `D i j` by `D i j + D i k * D k j` with one multiplication
query and one addition query. Over `MinTropical R` these are an addition of weights and a
comparison. The program is generic in `S` with only `[One S]`, so it touches weights only
through queries; its control flow does not depend on the answers.

## Main definitions

* `Cslib.Query.fwRound`: one Floyd–Warshall round as a query program.
* `Cslib.Query.floydWarshall`: Floyd–Warshall as a query program.

## Main results

* `Cslib.Query.cost_floydWarshall`: exactly `n ^ 3` additions and `n ^ 3` multiplications under
  every oracle.
* `Cslib.Query.isShortestDistances_floydWarshall`: under an oracle answering additions and
  multiplications honestly over `MinTropical R`, Floyd–Warshall returns the shortest-distance
  matrix of every weight matrix without negative cycles.

## References

* [Floyd, *Algorithm 97: Shortest path*][Floyd1962].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 25.2.
-/

public section

open Cslib.Algorithms.ShortestPaths

namespace Cslib.Query

variable {S : Type}

/-- One Floyd–Warshall round with pivot `k`, as a program: for every pair `(i, j)` one
multiplication `D i k * D k j` (an addition of weights) and one addition (a comparison). -/
@[expose] def fwRound {n : ℕ} (D : Matrix (Fin n) (Fin n) S) (k : Fin n) :
    FreeM (ArithQuery S) (Matrix (Fin n) (Fin n) S) :=
  FreeM.tabulateMatrix n fun i j => do
    let t ← ArithQuery.doMul (D i k) (D k j)
    ArithQuery.doAdd (D i j) t

/-- **Floyd–Warshall** in the arithmetic query model: start from `withOneDiag W` and run the
rounds for the pivots `0, 1, …, n - 1`. -/
@[expose] def floydWarshall [One S] (n : ℕ) (W : Matrix (Fin n) (Fin n) S) :
    FreeM (ArithQuery S) (Matrix (Fin n) (Fin n) S) :=
  (List.finRange n).foldlM fwRound (withOneDiag W)

theorem cost_fwRound (oracle : {ι : Type} → ArithQuery S ι → ι) (cAdd cMul : ℕ) {n : ℕ}
    (D : Matrix (Fin n) (Fin n) S) (k : Fin n) :
    (fwRound D k).cost oracle (ArithQuery.weight cAdd cMul) = n ^ 2 * (cAdd + cMul) := by
  simp only [fwRound, FreeM.cost_tabulateMatrix, FreeM.cost_bind, FreeM.cost_lift,
    ArithQuery.weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- Floyd–Warshall makes exactly `n ^ 3` multiplications and `n ^ 3` additions, under every
oracle. -/
theorem cost_floydWarshall [One S] (oracle : {ι : Type} → ArithQuery S ι → ι) (cAdd cMul n : ℕ)
    (W : Matrix (Fin n) (Fin n) S) :
    (floydWarshall n W).cost oracle (ArithQuery.weight cAdd cMul) = n ^ 3 * (cAdd + cMul) := by
  rw [floydWarshall, FreeM.cost_foldlM oracle _ fwRound _ (cost_fwRound oracle cAdd cMul),
    List.length_finRange, smul_eq_mul]
  ring

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R]

theorem eval_fwRound (oracle : {ι : Type} → ArithQuery (MinTropical R) ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b) (hmul : ∀ a b, oracle (.mul a b) = a * b) {n : ℕ}
    (D : Matrix (Fin n) (Fin n) (MinTropical R)) (k : Fin n) :
    (fwRound D k).eval oracle = fwStep D k := by
  rw [fwRound, FreeM.eval_tabulateMatrix]
  ext i j
  simp only [Matrix.of_apply, FreeM.eval_bind, FreeM.eval_lift, hmul, hadd, fwStep]

/-- **Correctness of Floyd–Warshall.** Under an oracle that answers additions and
multiplications honestly, Floyd–Warshall returns the shortest-distance matrix of every weight
matrix without negative cycles. -/
theorem isShortestDistances_floydWarshall
    (oracle : {ι : Type} → ArithQuery (MinTropical R) ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b) (hmul : ∀ a b, oracle (.mul a b) = a * b) {n : ℕ}
    {W : Matrix (Fin n) (Fin n) (MinTropical R)} (hW : NoNegCycle W) :
    IsShortestDistances W ((floydWarshall n W).eval oracle) := by
  rw [floydWarshall, FreeM.eval_foldlM oracle fwRound fwStep (eval_fwRound oracle hadd hmul)]
  exact isShortestDistances_foldl_fwStep hW List.mem_finRange

end Cslib.Query
