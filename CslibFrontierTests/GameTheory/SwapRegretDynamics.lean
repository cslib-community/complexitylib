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
    {p : ℕ → Fin 2 → Bool → ℝ} {T : ℕ} (hT : 0 < T)
    (h_nonneg : ∀ t i c, 0 ≤ p t i c) (h_sum : ∀ t i, ∑ c, p t i c = 1)
    (hT_bound : ∀ _ : Fin 2, (2 : ℝ) * log 2 ≤ T)
    (h_cost : ∀ t < T, ∀ i a, |pennies.deviationCost (p t) i a| ≤ 1)
    (h_p : ∀ t i a, p t i a = blumMansourProb √(2 * log 2 / T)
      (fun s c => pennies.deviationCost (p s) i c) t a) :
    pennies.IsApproxCorrelatedEquilibrium
      (fun _ => 2 * √(2 * log 2 / T))
      (timeAverage (fun t => productDist (h_nonneg t) (h_sum t)) T hT) := by
  have hn : ∀ (i : Fin 2), 2 ≤ Fintype.card Bool := fun _ => by rfl
  have hT_bound' : ∀ (_ : Fin 2), (Fintype.card Bool : ℝ) * log (Fintype.card Bool) ≤ ↑T := by
    intro i
    have : (Fintype.card Bool : ℝ) = 2 := by norm_num
    rw [this]
    exact hT_bound i
  have h_p' : ∀ (t : ℕ) (i : Fin 2) (a : Bool),
    p t i a = blumMansourProb √((Fintype.card Bool : ℝ) * log (Fintype.card Bool) / ↑T)
      (fun s c => pennies.deviationCost (p s) i c) t a := by
    intro t i a
    have : (Fintype.card Bool : ℝ) = 2 := by norm_num
    rw [this]
    exact h_p t i a
  have h_eq : (fun (i : Fin 2) => 2 * √((Fintype.card Bool : ℝ) * log (Fintype.card Bool) / ↑T)) =
      fun _ => 2 * √(2 * log 2 / ↑T) := by
    ext i
    have : (Fintype.card Bool : ℝ) = 2 := by norm_num
    rw [this]
  rw [← h_eq]
  exact blumMansour_isApproxCorrelatedEquilibrium pennies hT h_nonneg h_sum hn hT_bound' h_cost h_p'

end CslibFrontierTests.GameTheory.SwapRegretDynamics
