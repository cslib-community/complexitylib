/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.AdaptivePolicy.Covariance
import CslibFrontier.Probability.AdaptivePolicy.Nonidentifiability
import CslibFrontier.Probability.AdaptivePolicy.SignReversal
import Mathlib.Tactic

/-! Actual controlled trajectories and boundary clients for the general covariance identity. -/
noncomputable section
open Finset Cslib.Probability.AdaptivePolicy
namespace CslibFrontierTests.AdaptivePolicyCovariance

/-- The two-state endogenous experiment from Proposition 3.8. -/
def investment (m : ℝ) : FiniteMDP Bool Bool where
  initial _ := 1 / 2
  initial_nonneg _ := by norm_num
  initial_sum := by norm_num [Fintype.sum_bool]
  transition _ s a s' := if s' = (s && a) then 1 else 0
  transition_nonneg _ _ _ _ := by split <;> norm_num
  transition_sum _ s a := by simp
  cost t s a := if t = 0 then SignReversal.firstCost s a else SignReversal.terminalCost m s a

/-- Invest precisely in the favorable initial state; the terminal action is irrelevant. -/
def investPolicy : MarkovPolicy Bool Bool where
  prob t s a := if a = (if t = 0 then s else false) then 1 else 0
  nonneg _ _ _ := ite_nonneg (by norm_num) (by norm_num)
  sum_prob _ _ := by simp

/-- This client evaluates the actual controlled process independently of the identity. -/
theorem investment_values (m : ℝ) :
    (investment m).totalCost investPolicy 2 = 1 - m / 2 ∧
    (investment m).totalCost ((investment m).openLoop investPolicy) 2 = 3 / 4 - m / 4 := by
  constructor <;>
    simp [FiniteMDP.totalCost, FiniteMDP.stateLaw, FiniteMDP.openLoop, investment,
      investPolicy, sum_range_succ, SignReversal.firstCost, SignReversal.terminalCost] <;> ring

/-- The general theorem recovers the true negative gap, rather than the positive myopic audit. -/
example (m : ℝ) :
    (∑ t ∈ range 2, (investment m).traceCovariance investPolicy t
      ((investment m).actionValue ((investment m).openLoop investPolicy) 2 t)) =
        (1 - m) / 4 := by
  rw [← FiniteMDP.covariance_characterization]
  rw [(investment_values m).1, (investment_values m).2]
  ring

example (M : FiniteMDP Bool Bool) (π : MarkovPolicy Bool Bool) :
    M.totalCost π 0 = 0 ∧
    (∑ t ∈ range 0, M.traceCovariance π t (M.actionValue (M.openLoop π) 0 t)) = 0 := by
  simp [FiniteMDP.totalCost]

/-- The comparison is between genuine trajectory values under two different policies. -/
example (m : ℝ) :
    (investment m).totalCost investPolicy 2 -
        (investment m).totalCost ((investment m).openLoop investPolicy) 2 =
      ∑ t ∈ range 2,
        ((∑ s, ∑ a, ((investment m).stateLaw investPolicy t s * investPolicy.prob t s a) *
          (investment m).actionValue ((investment m).openLoop investPolicy) 2 t s a) -
        ∑ s, ∑ a, ((investment m).stateLaw investPolicy t s *
          (∑ x, (investment m).stateLaw investPolicy t x * investPolicy.prob t x a)) *
            (investment m).actionValue ((investment m).openLoop investPolicy) 2 t s a) :=
  (investment m).joint_product_characterization investPolicy 2

/-- A nonconstant deterministic logger cannot identify even binary cost tables,
regardless of the number of i.i.d. logged rounds. -/
example : ∃ loss₀ loss₁ : Bool → Bool → Bool,
    (∀ T z, (investment 2).sampleLaw investPolicy loss₀ T z =
      (investment 2).sampleLaw investPolicy loss₁ T z) ∧
    (investment 2).contextualGap investPolicy loss₁ -
      (investment 2).contextualGap investPolicy loss₀ = -1 / 4 ∧
    (investment 2).contextualGap investPolicy loss₁ ≠
      (investment 2).contextualGap investPolicy loss₀ := by
  have h := (investment 2).finite_nonidentifiability investPolicy {false} true
    (by simp [investPolicy])
    (by norm_num [investment, investPolicy, Fintype.sum_bool])
    (by norm_num [investment])
  norm_num [investment, investPolicy, Fintype.sum_bool] at h ⊢
  exact h

end CslibFrontierTests.AdaptivePolicyCovariance
