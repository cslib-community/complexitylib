/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Strategic.SwapRegretDynamics
import CslibFrontierTests.GameTheory.Strategic

/-!
# Tests for swap regret dynamics

Concrete instantiation of `blumMansour_isApproxCorrelatedEquilibrium` on matching pennies
(`CslibFrontierTests.GameTheory.Strategic.pennies`), discharging all game-cost and horizon
conditions unconditionally for every `T ≥ 2`.
-/

namespace CslibFrontierTests.GameTheory.SwapRegretDynamics

open Finset Real Function Cslib.MachineLearning.OnlineLearning.Experts
open Cslib.GameTheory
open Cslib.GameTheory.CostGame
open CslibFrontierTests.GameTheory.Strategic

/-- Matching pennies has costs bounded in absolute value by `1`, and `2 * log 2 ≤ T` for every
`T ≥ 2`, so the coupled Blum–Mansour dynamics converge unconditionally on `pennies` with slack
`2 √(2 log 2 / T)`. -/
theorem blumMansour_pennies {T : ℕ} (hT : 2 ≤ T) :
    pennies.IsApproxCorrelatedEquilibrium
      (fun _ => 2 * √(2 * log 2 / T))
      (timeAverage
        (fun t => productDist (blumMansourDynamics_nonneg pennies T t)
          (sum_blumMansourDynamics pennies T t))
        T (by omega)) := by
  have hn : ∀ _i : Fin 2, 2 ≤ Fintype.card Bool := fun _ => by decide
  have hT_bound : ∀ _i : Fin 2, (Fintype.card Bool : ℝ) * log (Fintype.card Bool) ≤ T := by
    intro _
    have hlog : Real.log 2 ≤ 1 :=
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq (by norm_num)
    have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
    norm_num
    nlinarith
  have hc : ∀ (i : Fin 2) (s : Fin 2 → Bool), |pennies.cost i s| ≤ 1 := by
    intro i s
    dsimp [pennies]
    split_ifs <;> norm_num
  have h_eq :
      (fun _i : Fin 2 => 2 * √((Fintype.card Bool : ℝ) * log (Fintype.card Bool) / T)) =
        fun _ => 2 * √(2 * log 2 / T) := by
    ext _
    norm_num
  rw [← h_eq]
  exact blumMansour_isApproxCorrelatedEquilibrium pennies (by omega) hn hT_bound hc

/-- Concrete check of `blumMansour_pennies` at `T = 4` together with the online learner identity
at round `0`. -/
theorem blumMansour_pennies_four_and_learner (i : Fin 2) :
    pennies.IsApproxCorrelatedEquilibrium
      (fun _ => 2 * √(2 * log 2 / 4))
      (timeAverage
        (fun t => productDist (blumMansourDynamics_nonneg pennies 4 t)
          (sum_blumMansourDynamics pennies 4 t))
        4 (by omega)) ∧
    blumMansourDynamics pennies 4 0 i =
      blumMansourProb √(2 * log 2 / 4)
        (fun s c => pennies.deviationCost (blumMansourDynamics pennies 4 s) i c) 0 := by
  refine ⟨by simpa using blumMansour_pennies (T := 4) (by omega), ?_⟩
  simpa using blumMansourDynamics_eq_blumMansourProb pennies 4 0 i

end CslibFrontierTests.GameTheory.SwapRegretDynamics
