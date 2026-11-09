/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.ShortestPaths.MinPlus
import CslibFrontier.Algorithms.ShortestPaths.Power
import Mathlib.Data.Fin.VecNotation

/-!
# All-pairs shortest paths and the (min,+) product

Kernel-checked runs of Floyd–Warshall, repeated squaring with schoolbook (min,+) products and the
(min,+) product through APSP on the tripartite graph, over `MinTropical (WithTop ℤ)` with a
negative edge and with the honest oracle; their exact query counts; negative-cycle detection on a
graph with and without a negative cycle; and the general theorems instantiated, which shows that
their hypotheses are satisfiable.
-/

namespace CslibFrontierTests.ShortestPaths

open MinTropical Cslib.Query Cslib.Algorithms.ShortestPaths

/-- Weights in `ℤ ∪ {∞}`, with `0 = ∞` (no edge) and `1 = 0`. -/
abbrev T := MinTropical (WithTop ℤ)

/-- The honest oracle: an addition query is a minimum, a multiplication query adds weights. -/
def oracle : {ι : Type} → ArithQuery T ι → ι
  | _, .add a b => a + b
  | _, .sub a _ => a
  | _, .mul a b => a * b

theorem oracle_add (a b : T) : oracle (.add a b) = a + b := rfl
theorem oracle_mul (a b : T) : oracle (.mul a b) = a * b := rfl

/-- The finite weight `x`. -/
def w (x : ℤ) : T := trop (x : WithTop ℤ)

instance : DecidableEq (Matrix (Fin 3) (Fin 3) T) :=
  inferInstanceAs (DecidableEq (Fin 3 → Fin 3 → T))

/-- Edges `0 → 1` (weight `4`), `0 → 2` (`5`), `1 → 2` (`-2`) and `2 → 1` (`3`); the only cycle
`1 → 2 → 1` has weight `1`. -/
def W₃ : Matrix (Fin 3) (Fin 3) T := Matrix.of ![![0, w 4, w 5], ![0, 0, w (-2)], ![0, w 3, 0]]

/-- Its shortest distances: `0 → 2` goes through `1` with weight `2`. -/
def D₃ : Matrix (Fin 3) (Fin 3) T :=
  Matrix.of ![![w 0, w 4, w 2], ![0, w 0, w (-2)], ![0, w 3, w 0]]

/-- Changing `2 → 1` to weight `1` makes `1 → 2 → 1` a negative cycle. -/
def Wneg : Matrix (Fin 3) (Fin 3) T := Matrix.of ![![0, w 4, w 5], ![0, 0, w (-2)], ![0, w 1, 0]]

/-! ### Negative-cycle detection -/

example : NoNegCycle W₃ := by decide +kernel
example : ¬ NoNegCycle Wneg := by decide +kernel

/-! ### Runs and query counts -/

example : (floydWarshall 3 W₃).eval oracle = D₃ := by decide +kernel
example : (floydWarshall 3 W₃).countQueries oracle = 54 := by decide +kernel

example : (apspBySquaring (schoolbookMatMul 3) W₃).eval oracle = D₃ := by decide +kernel
/-- One squaring (`⌈log₂ 2⌉ = 1`) of `27` multiplications and `18` additions. -/
example : (apspBySquaring (schoolbookMatMul 3) W₃).countQueries oracle = 45 := by decide +kernel

example : (schoolbookMatMul 3 W₃ W₃).eval oracle = W₃ * W₃ := by decide +kernel
/-- The (min,+) product through Floyd–Warshall on the `9`-vertex tripartite graph. -/
example : (minPlusViaAPSP (floydWarshall (3 * 3)) W₃ Wneg).eval oracle = W₃ * Wneg := by
  decide +kernel

/-! ### The general theorems, instantiated -/

example : IsShortestDistances W₃ D₃ := by
  have h := isShortestDistances_floydWarshall oracle oracle_add oracle_mul
    (show NoNegCycle W₃ by decide +kernel)
  rwa [show (floydWarshall 3 W₃).eval oracle = D₃ by decide +kernel] at h

example : IsShortestDistances W₃ ((1 + W₃) ^ 2) :=
  isShortestDistances_one_add_pow (by decide +kernel) (by simp)

example (n : ℕ) (W : Matrix (Fin n) (Fin n) T) (hW : NoNegCycle W) :
    IsShortestDistances W ((apspBySquaring (schoolbookMatMul n) W).eval oracle) :=
  isShortestDistances_apspBySquaring_schoolbook oracle oracle_add oracle_mul hW

example (n : ℕ) (A B : Matrix (Fin n) (Fin n) T) :
    (minPlusViaAPSP (floydWarshall (3 * n)) A B).eval oracle = A * B :=
  eval_minPlusViaAPSP_floydWarshall oracle oracle_add oracle_mul A B

example (n : ℕ) (A B : Matrix (Fin n) (Fin n) T) :
    (minPlusViaAPSP (floydWarshall (3 * n)) A B).cost oracle (ArithQuery.weight 1 1) =
      54 * n ^ 3 := by
  rw [cost_minPlusViaAPSP_floydWarshall]
  ring

example (W : Matrix (Fin 9) (Fin 9) T) :
    (apspBySquaring (schoolbookMatMul 9) W).cost oracle (ArithQuery.weight 1 1) = 3 * 1377 := by
  rw [cost_apspBySquaring_schoolbook]
  decide

end CslibFrontierTests.ShortestPaths
