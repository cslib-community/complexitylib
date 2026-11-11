/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module -- shake: keep-all
-- upstream: local-only (test file)

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import CslibFrontier.Algorithms.Lean.GomoryHu.Real
public import CslibFrontier.Algorithms.Lean.GomoryHu.Oracles

public section

namespace CslibFrontierTests.GomoryHuRealAndOracles

open Cslib.Algorithms.Lean.GomoryHu
open Cslib.Algorithms.Lean.MaxFlow

def W5 : Fin 5 → Fin 5 → ℕ
  | 0, 1 => 5
  | 1, 0 => 5
  | 0, 2 => 10
  | 2, 0 => 10
  | 1, 2 => 1
  | 2, 1 => 1
  | 1, 3 => 8
  | 3, 1 => 8
  | 2, 4 => 2
  | 4, 2 => 2
  | 3, 4 => 7
  | 4, 3 => 7
  | _, _ => 0

example : (pushRelabelGomoryHu W5 0).parent.toList = [0, 0, 0, 1, 3] := by decide
example : (pushRelabelGomoryHu W5 0).weight.toList = [0, 8, 13, 10, 9] := by decide

example : (dinitzGomoryHu W5 0).parent.toList = [0, 0, 0, 1, 3] := by decide
example : (dinitzGomoryHu W5 0).weight.toList = [0, 8, 13, 10, 9] := by decide

noncomputable def WReal : Fin 2 → Fin 2 → ℝ
  | 0, 1 => Real.sqrt 2
  | 1, 0 => Real.sqrt 2
  | _, _ => 0

theorem exists_real_tree : ∃ T, IsGomoryHuTree (Cslib.WeightedCut.realCutWeight WReal) T :=
  exists_isGomoryHuTree_realCutWeight (by intro u v; fin_cases u <;> fin_cases v <;> rfl)
    (by intro u v; fin_cases u <;> fin_cases v <;> simp [WReal] )

end CslibFrontierTests.GomoryHuRealAndOracles
