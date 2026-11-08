/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Backbone
public import Complexity.Statistics.LeastSquares.SharpGap
public import Complexity.Statistics.LeastSquares.RangeAudit
import Mathlib.Tactic.FinCases

/-! Checked clients for the generic backbone, actual simple regression and two audit gaps. -/

open Cslib.LeastSquares Matrix

namespace Submission1326

/-- Three nonzero scalar design rows are in general position in dimension one. -/
public theorem scalar_general_position :
    GeneralPosition (fun _ : Fin 3 => fun _ : Fin 1 => (1 : ℝ)) := by
  intro s hs
  have hs' : s.card = 1 := hs
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs'
  change LinearIndepOn ℝ (fun _ : Fin 3 => fun _ : Fin 1 => (1 : ℝ))
    (↑({i} : Finset (Fin 3)))
  rw [Finset.coe_singleton, linearIndepOn_singleton_iff]
  intro h
  have := congrFun h 0
  norm_num at this

/-- A nonvacuous sparse GP client: mass `5/2`, one fractional coordinate, and no
separately supplied positive definite backbone. The output includes nonsingularity. -/
public theorem sparse_scalar_rounding :
    ∃ u : Fin 3 → ℝ, (∀ i ∈ Finset.univ, u i = 0 ∨ u i = 1) ∧
      (∀ i, i ∉ Finset.univ → u i = (![1, 1, 1/2] : Fin 3 → ℝ) i) ∧
      (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ weightedEstimate 0 0 Finset.univ
        (fun _ _ => 1) (![1, -1, -1] : Fin 3 → ℝ) u ≤
      (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ weightedEstimate 0 0 Finset.univ
        (fun _ _ => 1) (![1, -1, -1] : Fin 3 → ℝ) ![1, 1, 1/2] ∧
      (∑ i, (![1, 1, 1/2] : Fin 3 → ℝ) i) - (∑ i, u i) < 1 ∧
      (weightedGram 0 Finset.univ (fun _ : Fin 3 => fun _ : Fin 1 => (1 : ℝ)) u).PosDef := by
  have h := exists_round_sparse _ scalar_general_position Finset.univ
    (![1, -1, -1] : Fin 3 → ℝ) ![1, 1, 1/2] (fun _ => 1) (by decide)
    (by intro i hi; fin_cases i <;> norm_num)
    (by
      have hJ : Finset.univ.filter (fun i : Fin 3 =>
          0 < (![1, 1, 1/2] : Fin 3 → ℝ) i ∧ (![1, 1, 1/2] : Fin 3 → ℝ) i < 1) = {2} := by
        ext i
        fin_cases i <;> norm_num
      rw [hJ]
      decide) (by norm_num [Fin.sum_univ_succ])
  simpa only [Fintype.card_fin, Nat.cast_one] using h

/-- The two-regressor (intercept plus slope) formula returns a genuine nonzero slope. -/
public theorem simple_regression :
    Simple.slope (![0, 1, 2] : Fin 3 → ℚ) ![1, 3, 5] (fun _ => 1) = 2 ∧
    Simple.intercept (![0, 1, 2] : Fin 3 → ℚ) ![1, 3, 5] (fun _ => 1) = 1 := by
  decide +kernel

/-- A constant regressor is singular and must not be accepted just because division by
zero assigns a value to the slope expression. -/
public theorem singular_regressor :
    Simple.xNumerator (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 1) = 0 := by
  decide +kernel

/-- The strict fractional gap concerns actual real weights, and the integral endpoint
quantifies over all retained subsets. -/
public theorem sharpness : SharpGap.fractionalStability < 98/100 ∧
    IsLeast {k : ℕ | ∃ s : Finset (Fin 10),
      SharpGap.Feasible (Simple.realVector (Simple.keep s)) ∧ k = 10 - s.card} 2 := by
  exact SharpGap.sharp_gap.2

/-- The twelve-point endpoint applies to actual real OLS, not just rational scatter signs. -/
public theorem real_audit :
    IsLeast {k : ℕ | ∃ s : Finset (Fin 12),
      (0 < Simple.xNumerator (Simple.realVector (fun i => (RangeAudit.point i).1))
        (Simple.realVector (Simple.keep s)) ∧
      Simple.slope (Simple.realVector (fun i => (RangeAudit.point i).1))
        (Simple.realVector (fun i => (RangeAudit.point i).2))
        (Simple.realVector (Simple.keep s)) ≤ 0) ∧ k = 12 - s.card} 2 := by
  simpa only [← RangeAudit.feasible_iff_real] using RangeAudit.range_audit_gap.1

end Submission1326
