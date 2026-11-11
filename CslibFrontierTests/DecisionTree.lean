/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.DecisionTree.AffineScore
import Mathlib.Tactic.FinCases

/-! Tests for structural decision-tree paths and affine leaf scores. -/

namespace CslibFrontierTests.DecisionTree

open Cslib Cslib.DecisionTree

private def sampleTree : DecisionTree (Fin 2) Bool :=
  .node 0 (.leaf false) (.node 1 (.leaf false) (.leaf true))

example : sampleTree.paths = [[false], [true, false], [true, true]] := rfl

example : sampleTree.paths.length = sampleTree.leafCount :=
  sampleTree.length_paths

example (x : Fin 2 → Bool) : sampleTree.path x ∈ sampleTree.paths :=
  sampleTree.path_mem_paths x

example : sampleTree.paths.Nodup :=
  sampleTree.nodup_paths

example : (sampleTree.mapQueries id).paths = sampleTree.paths :=
  sampleTree.paths_mapQueries id

example (B : ℝ) (d : ℕ) (p : List Bool) :
    leafScore B d 0 sampleTree p = 0 :=
  leafScore_zero B d sampleTree p

example (B c : ℝ) (d : ℕ) (q₁ q₂ : Fin 2 → ℝ) (p : List Bool) :
    leafScore B d (c • q₁ + q₂) sampleTree p =
      c * leafScore B d q₁ sampleTree p + leafScore B d q₂ sampleTree p := by
  rw [leafScore_add, leafScore_smul]

example (B : ℝ) (d : ℕ) (q : Fin 2 → ℝ) (p : List Bool) :
    leafScore B d q (sampleTree.mapQueries id) p = leafScore B d q sampleTree p :=
  leafScore_mapQueries id B d q sampleTree p

private def sampleMargins : Fin 2 → ℝ
  | 0 => 2
  | 1 => -1

private theorem sampleMargins_min (i : Fin 2) : 1 ≤ |sampleMargins i| := by
  fin_cases i <;> norm_num [sampleMargins]

private theorem sampleMargins_max (i : Fin 2) : |sampleMargins i| ≤ 2 := by
  fin_cases i <;> norm_num [sampleMargins]

example (p : List Bool) :
    2 * |leafScore 5 2 sampleMargins sampleTree p| ≤ (5 : ℝ) ^ 2 - 1 := by
  simpa only [show (2 : ℝ) * 2 + 1 = 5 by ring] using
    two_mul_abs_leafScore_le sampleTree p (by decide) (by norm_num) sampleMargins_max

example :
    leafScore 5 2 sampleMargins sampleTree [false] + 1 ≤
      leafScore 5 2 sampleMargins sampleTree
        (sampleTree.path (fun i => decide (0 ≤ sampleMargins i))) := by
  have hpath : sampleTree.path (fun i => decide (0 ≤ sampleMargins i)) = [true, false] := by
    simp [sampleTree, DecisionTree.path, sampleMargins]
  simpa only [show (2 : ℝ) * 2 + 1 = 5 by ring] using
    leafScore_add_one_le_leafScore_path_decide sampleTree (d := 2) (M := 2)
      (by decide) (by norm_num) sampleMargins_min sampleMargins_max
      (by simp [sampleTree]) (by rw [hpath]; decide)

end CslibFrontierTests.DecisionTree
