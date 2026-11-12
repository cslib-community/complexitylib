/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.TSP.HamiltonianCount
import Mathlib.Data.Fin.VecNotation

/-!
# Worked inclusion–exclusion Hamiltonian-path counting examples

These kernel-checked examples (using `decide +kernel`, never `native_decide`) exercise
`Cslib.Algorithms.Lean.TSP.countHamPathsM` and `decideHamPathM`:

1. A directed path `0 → 1 → 2` on `Fin 3` with a unique Hamiltonian path, and the observed tick
   count `176 ≤ 2 ^ 3 * 3 ^ 3`.
2. A directed branching graph `0 → 1, 0 → 2` on `Fin 3` with no Hamiltonian path (`count = 0`).
3. Complete loopless directed graphs on `Fin 3` (`3! = 6` Hamiltonian paths) and `Fin 4`
   (`4! = 24` Hamiltonian paths, in `848 ≤ 2 ^ 4 * 4 ^ 3` ticks).
4. A 4-vertex diamond digraph (`0 → 1, 0 → 2, 1 ↔ 2, 1 → 3, 2 → 3`) with exactly `2` Hamiltonian
   paths.
5. Edge cases on `0` and `1` vertices.
-/

namespace CslibFrontierTests.HamiltonianCount

open Cslib.Algorithms.Lean.TSP

/-! ### 1. A directed path on three vertices -/

/-- The directed path `0 → 1 → 2` on `Fin 3`. -/
def path3 : Fin 3 → Fin 3 → Bool :=
  ![![false, true, false], ![false, false, true], ![false, false, false]]

example : (countHamPathsM path3).ret = 1 := by decide +kernel
example : (hamPaths path3).card = 1 := by
  rw [card_hamPaths_eq_toNat_ret_countHamPathsM]
  decide +kernel
example : (decideHamPathM path3).ret = true := by decide +kernel
example : (hamPaths path3).Nonempty := (ret_decideHamPathM_eq_true_iff path3).1 (by decide +kernel)
example : (countHamPathsM path3).time = 176 := by decide +kernel
example : (countHamPathsM path3).time ≤ 2 ^ 3 * 3 ^ 3 :=
  time_countHamPathsM_le_of_two_le path3 (by omega)

/-! ### 2. A digraph on three vertices without a Hamiltonian path -/

/-- Out-branching `0 → 1` and `0 → 2` with no arcs between `1` and `2`. -/
def noHam3 : Fin 3 → Fin 3 → Bool :=
  ![![false, true, true], ![false, false, false], ![false, false, false]]

example : (countHamPathsM noHam3).ret = 0 := by decide +kernel
example : (decideHamPathM noHam3).ret = false := by decide +kernel
example : ¬ (hamPaths noHam3).Nonempty := fun h => by
  have := (ret_decideHamPathM_eq_true_iff noHam3).2 h
  revert this
  decide +kernel

/-! ### 3. Complete loopless directed graphs `K₃` and `K₄` -/

/-- Complete loopless directed graph on `Fin n`: an arc between every pair of distinct vertices. -/
def completeDigraph (n : ℕ) (u v : Fin n) : Bool := u != v

example : (countHamPathsM (completeDigraph 3)).ret = 6 := by decide +kernel
example : (hamPaths (completeDigraph 3)).card = 6 := by
  rw [card_hamPaths_eq_toNat_ret_countHamPathsM]
  decide +kernel

example : (countHamPathsM (completeDigraph 4)).ret = 24 := by decide +kernel
example : (hamPaths (completeDigraph 4)).card = 24 := by
  rw [card_hamPaths_eq_toNat_ret_countHamPathsM]
  decide +kernel
example : (countHamPathsM (completeDigraph 4)).time = 848 := by decide +kernel
example : (countHamPathsM (completeDigraph 4)).time ≤ 2 ^ 4 * 4 ^ 3 :=
  time_countHamPathsM_le_of_two_le (completeDigraph 4) (by omega)

/-! ### 4. A 4-vertex diamond digraph with two Hamiltonian paths -/

/-- `0` reaches `1` and `2`, `1` and `2` have arcs both ways, and both reach `3`: the two
Hamiltonian paths are `0 → 1 → 2 → 3` and `0 → 2 → 1 → 3`. -/
def diamond4 : Fin 4 → Fin 4 → Bool :=
  ![![false, true, true, false],
    ![false, false, true, true],
    ![false, true, false, true],
    ![false, false, false, false]]

example : (countHamPathsM diamond4).ret = 2 := by decide +kernel
example : (hamPaths diamond4).card = 2 := by
  rw [card_hamPaths_eq_toNat_ret_countHamPathsM]
  decide +kernel
example : (decideHamPathM diamond4).ret = true := by decide +kernel

/-! ### 5. Edge cases (`n = 0` and `n = 1`) -/

example : (countHamPathsM (n := 0) fun _ _ => false).ret = 1 := by decide +kernel
example : (countHamPathsM (n := 1) fun _ _ => false).ret = 1 := by decide +kernel
example : (countHamPathsM (n := 1) fun _ _ => true).ret = 1 := by decide +kernel

end CslibFrontierTests.HamiltonianCount
