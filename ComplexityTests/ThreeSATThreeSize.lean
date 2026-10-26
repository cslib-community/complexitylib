/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
import Complexity.Computability.Complexity.Problems.ThreeSATThree.Size

open Cslib.Logic.PL Cslib.Complexity

-- An empty formula and an empty clause take the width-valid branch, including the unit offset.
example : (toThreeSATThree []).numVars + (toThreeSATThree []).length +
    (toThreeSATThree []).vars.length + 1 = 1 := by decide

example : (toThreeSATThree [[]]).numVars + (toThreeSATThree [[]]).length +
    (toThreeSATThree [[]]).vars.length + 1 = 2 := by decide

private def hugeUnit : CNF ℕ := [[(2 ^ 128, true)]]

-- Binary label magnitude does not increase the number of distinct variables or incidences.
example : (toThreeSATThree hugeUnit).numVars = 1 := by decide +kernel
example : (toThreeSATThree hugeUnit).numVars + (toThreeSATThree hugeUnit).length +
    (toThreeSATThree hugeUnit).vars.length + 1 = 7 := by decide +kernel
example : (toThreeSATThree hugeUnit).vars.count
    (ThreeSATThree.numberCopy (2 ^ 128, 0, 0)) = 3 := by decide +kernel

private def invalidWidth : CNF ℕ :=
  [[(2 ^ 128, true), (0, false), (2 ^ 128, true), (1, false)]]

-- The total bound also covers a width-invalid formula with repeated, huge binary labels.
example : toThreeSATThree invalidWidth = [[]] := by decide +kernel
example : (toThreeSATThree invalidWidth).numVars + (toThreeSATThree invalidWidth).length +
    (toThreeSATThree invalidWidth).vars.length + 1 = 2 := by decide +kernel
example : (toThreeSATThree invalidWidth).numVars + (toThreeSATThree invalidWidth).length +
    (toThreeSATThree invalidWidth).vars.length + 1 ≤
      7 * (invalidWidth.length + invalidWidth.vars.length + 1) := size_toThreeSATThree_le _

-- Total structural bounds do not require satisfiability or source width hypotheses.
example (φ : CNF ℕ) : ∀ c ∈ toThreeSATThree φ, c.length ≤ 3 := width_toThreeSATThree φ
example (φ : CNF ℕ) (v : ℕ) : (toThreeSATThree φ).vars.count v ≤ 3 :=
  count_vars_toThreeSATThree_le φ v
