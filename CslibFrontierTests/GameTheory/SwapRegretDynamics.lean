/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Strategic.SwapRegretDynamics
import CslibFrontierTests.GameTheory.Strategic

/-!
# Tests for swap regret dynamics
-/

namespace CslibFrontierTests.GameTheory.SwapRegretDynamics

open Finset Real Function Cslib.MachineLearning.OnlineLearning.Experts
open Cslib.GameTheory
open Cslib.GameTheory.CostGame
open CslibFrontierTests.GameTheory.Strategic

theorem blumMansour_pennies
    {T : ℕ} (hT : 0 < T)
    (hT_bound : ∀ _ : Fin 2, (2 : ℝ) * log 2 ≤ T)
    (h_cost : ∀ t < T, ∀ i a, |pennies.deviationCost (blumMansourDynamics pennies T t) i a| ≤ 1) :
    pennies.IsApproxCorrelatedEquilibrium
      (fun _ => 2 * √(2 * log 2 / T))
      (timeAverage (fun t => productDist (blumMansourDynamics_nonneg pennies T t)
        (sum_blumMansourDynamics pennies T t)) T hT) := by
  have hn : ∀ (i : Fin 2), 2 ≤ Fintype.card Bool := fun _ => by rfl
  have hT_bound' : ∀ (_ : Fin 2), (Fintype.card Bool : ℝ) * log (Fintype.card Bool) ≤ ↑T := by
    intro i
    have : (Fintype.card Bool : ℝ) = 2 := by norm_num
    rw [this]
    exact hT_bound i
  have h_eq : (fun (i : Fin 2) => 2 * √((Fintype.card Bool : ℝ) * log (Fintype.card Bool) / ↑T)) =
      fun _ => 2 * √(2 * log 2 / ↑T) := by
    ext i
    have : (Fintype.card Bool : ℝ) = 2 := by norm_num
    rw [this]
  rw [← h_eq]
  exact blumMansour_isApproxCorrelatedEquilibrium pennies hT hn hT_bound' h_cost

end CslibFrontierTests.GameTheory.SwapRegretDynamics
