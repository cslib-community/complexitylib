/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module -- shake: keep-all
-- upstream: local-only (test file)

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
public import CslibFrontier.Algorithms.Lean.GomoryHu.Real
public import CslibFrontier.Algorithms.Lean.GomoryHu.Oracles
public import CslibFrontier.Algorithms.Lean.MaxFlow.RealFlow

public section

namespace CslibFrontierTests.GomoryHuRealAndOracles

open Cslib.Algorithms.Lean.GomoryHu
open Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut

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

theorem isMultigraph_W5 : IsMultigraph W5 := by
  unfold IsMultigraph
  decide

-- The certified weights are minimum cut values `λ(u, parent u)`.
example : minCutBetween W5 3 1 = 10 := by
  have h := vget_dinitzGomoryHu_weight isMultigraph_W5 0 (u := 3) (by decide)
  rw [show vget (dinitzGomoryHu W5 0).weight 3 = 10 by decide,
    show vget (dinitzGomoryHu W5 0).parent 3 = 1 by decide] at h
  exact h.symm

example : minCutBetween W5 4 3 = 9 := by
  have h := vget_pushRelabelGomoryHu_weight isMultigraph_W5 0 (u := 4) (by decide)
  rw [show vget (pushRelabelGomoryHu W5 0).weight 4 = 9 by decide,
    show vget (pushRelabelGomoryHu W5 0).parent 4 = 3 by decide] at h
  exact h.symm

noncomputable def WReal : Fin 2 → Fin 2 → ℝ
  | 0, 1 => Real.sqrt 2
  | 1, 0 => Real.sqrt 2
  | _, _ => 0

theorem exists_real_tree : ∃ T, IsGomoryHuTree (Cslib.WeightedCut.cutWeight WReal) T :=
  exists_isGomoryHuTree_cutWeight_of_symm (by intro u v; fin_cases u <;> fin_cases v <;> rfl)
    (by intro u v; fin_cases u <;> fin_cases v <;> simp [WReal])

theorem WReal_nonneg (u v : Fin 2) : 0 ≤ WReal u v := by
  fin_cases u <;> fin_cases v <;> simp [WReal]

/-- The only cut separating `0` from `1` is `{0}`, of weight `√2`. -/
theorem minRealCutBetween_WReal : minRealCutBetween WReal 0 1 = Real.sqrt 2 := by
  have hcut : ∀ X : Finset (Fin 2), 0 ∈ X → 1 ∉ X → cutWeight WReal X = Real.sqrt 2 := by
    intro X h0 h1
    have hX : X = {0} := by
      ext x
      fin_cases x <;> simp [h0, h1]
    subst hX
    simp [cutWeight, WReal, Fin.sum_univ_two]
  obtain ⟨X, h0, h1, hX⟩ := exists_cutWeight_eq_minRealCutBetween WReal (s := 0) (t := 1)
    (by decide)
  rw [← hX, hcut X h0 h1]

/-- Max-flow min-cut with an irrational capacity: the maximum flow value is `√2`. -/
example : IsMaxRealFlow WReal 0 1 (Real.sqrt 2) :=
  minRealCutBetween_WReal ▸ isMaxRealFlow_minRealCutBetween WReal_nonneg (by decide)

end CslibFrontierTests.GomoryHuRealAndOracles
