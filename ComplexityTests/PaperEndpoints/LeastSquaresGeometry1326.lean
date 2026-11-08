/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import Complexity.Statistics.LeastSquares.FractionalGeometry
public import Complexity.Statistics.LeastSquares.FixedEffects.MatrixBridge
public import ComplexityTests.PaperEndpoints.FixedEffectsResources1326
import all ComplexityTests.PaperEndpoints.FixedEffectsResources1326
import Mathlib.Tactic

/-! Nonvacuous real optimizer, vanished-dummy and executed matrix-audit clients. -/

open Cslib.LeastSquares
open Matrix

namespace LeastSquaresGeometry1326

private def x : Fin 3 → ℝ := ![-1, 0, 1]
private def y : Fin 3 → ℝ := ![1, 0, 2]
private noncomputable def w : Fin 3 → ℝ := ![1, 1, 1/4]

private theorem optimum : Simple.MassOptimal x y w := by
  constructor
  · constructor
    · intro i; fin_cases i <;> norm_num [w]
    · norm_num [Simple.mass, Simple.xNumerator, Simple.crossNumerator, x, y, w, Fin.sum_univ_succ]
  · intro u hu
    have hb := hu.1
    have h0 := hb 0
    have h1 := hb 1
    have h2 := hb 2
    have hn := hu.2.2.2
    norm_num [Simple.crossNumerator, Simple.mass, x, y, Fin.sum_univ_succ] at hn
    norm_num [Simple.mass, w, Fin.sum_univ_succ]
    by_contra h
    have hs : 0 < u 0 + u 1 := by linarith [h2.2]
    have hc : 0 < 2 * u 2 - (u 0 + u 1) / 4 := by linarith [h0.2, h1.2]
    have hp := mul_pos hs hc
    nlinarith [sq_nonneg (u 0 - u 1)]

example : Simple.crossNumerator x y (fun _ => 1) > 0 := by
  norm_num [Simple.crossNumerator, Simple.mass, x, y, Fin.sum_univ_succ]

-- A global optimum with a genuinely fractional coordinate has a self-centred threshold.
example : ∃ τ, Simple.centeredScore x y w 2 = τ ∧
    (∀ i, 0 < w i → Simple.centeredScore x y w i ≤ τ) := by
  obtain ⟨_, τ, hsup, _, hfrac, _⟩ := optimum.self_centered x y w (by
    norm_num [Simple.crossNumerator, Simple.mass, x, y, Fin.sum_univ_succ])
  exact ⟨τ, hfrac 2 (by norm_num [w]), hsup⟩

private def panel : List FixedEffects.Choice :=
  [⟨1, []⟩, ⟨0, [(0, 1), (1, 0)]⟩]

-- A vanished group contributes no dummy column; the surviving group has negative slope.
example : Fintype.card (FixedEffects.Active panel) = 1 := by decide +kernel

example : (FixedEffects.MatrixModel.gram (FixedEffects.realX panel)).PosDef := by
  rw [FixedEffects.real_gram_posDef_iff]
  norm_num [FixedEffects.denominator, FixedEffects.variance, FixedEffects.mean,
    Cslib.FiniteMinPlus.total, panel]

example : ((FixedEffects.MatrixModel.gram (FixedEffects.realX panel))⁻¹ *ᵥ
    FixedEffects.MatrixModel.response (FixedEffects.realX panel)
      (FixedEffects.realY panel)) none = -1 := by
  rw [FixedEffects.real_inverse_slope panel (by
    norm_num [FixedEffects.denominator, FixedEffects.variance, FixedEffects.mean,
      Cslib.FiniteMinPlus.total, panel])]
  norm_num [FixedEffects.slope, FixedEffects.numerator, FixedEffects.denominator,
    FixedEffects.cross, FixedEffects.variance, FixedEffects.mean, Cslib.FiniteMinPlus.total, panel]

/-- The executed first crossing computes the real matrix optimum and its bound. -/
public theorem computed_matrix_optimum :
    ∃ r, (FixedEffects.Resources.run FixedEffectsResources1326.groups).ret = some r ∧
    FixedEffects.MatrixFeasible FixedEffectsResources1326.groups r.hit.entry.plan ∧
    FixedEffects.refittedIntegralStability FixedEffectsResources1326.groups = r.hit.index ∧
    (FixedEffects.Resources.run FixedEffectsResources1326.groups).time ≤
      300 * (3 * 2 ^ 3 +
        3 * FixedEffects.refittedIntegralStability FixedEffectsResources1326.groups) := by
  let groups := FixedEffectsResources1326.groups
  obtain ⟨r, hr⟩ := FixedEffects.Resources.run_exists groups
  have hp : r.hit.entry.plan = FixedEffectsResources1326.plan := by
    have hh := FixedEffectsResources1326.computed.1
    rw [hr] at hh
    exact Option.some.inj hh
  have hs := FixedEffects.Resources.run_matrix_optimal groups 3 r hr
    (by simp [groups, FixedEffectsResources1326.groups])
    (by simp [groups, FixedEffectsResources1326.groups])
    (by norm_num [groups, FixedEffectsResources1326.groups, FixedEffects.Resources.fullPlan,
      FixedEffects.numerator, Cslib.FiniteMinPlus.total, FixedEffects.cross, FixedEffects.mean])
    ⟨r.hit.entry.plan, (FixedEffects.Resources.run_spec groups r hr).1,
      (FixedEffects.Resources.run_spec groups r hr).2.1, rfl, by
      rw [hp]
      norm_num [FixedEffectsResources1326.plan, FixedEffects.denominator,
        Cslib.FiniteMinPlus.total, FixedEffects.variance, FixedEffects.mean]⟩
  exact ⟨r, hr, hs.1, hs.2.1, by simpa [groups, FixedEffectsResources1326.groups,
    FixedEffects.sampleSize, Cslib.FiniteMinPlus.total] using hs.2.2⟩

end LeastSquaresGeometry1326
