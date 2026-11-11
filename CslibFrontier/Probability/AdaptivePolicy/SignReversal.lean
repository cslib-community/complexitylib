/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# A two-state sign reversal for myopic audits

[Aldridge2027], Proposition 3.8 (PDF p. 4). States and actions are both `Bool`.
The initial state is uniform; the adaptive first action equals the state, whereas its
open-loop marginal is an independent uniform action. The second action is immaterial.
The transition retains only `s && a`, a sufficient statistic for the terminal cost;
this realizes the claimed two-state model without storing the paper's redundant pair.
The experiment below sums the actual first and terminal costs, rather than assuming a
value-function identity. This module does not formalize the general audit theorem.

## Main results

* `sign_reversal`: the exact positive myopic covariance and negative actual cost gap.
* `terminal_covariance`: the terminal myopic term is zero for every second-step policy.
-/

public section
noncomputable section
namespace Cslib.Probability.AdaptivePolicy.SignReversal

/-- Expectation under a uniform Boolean seed. -/
def mean (f : Bool → ℝ) : ℝ := (f false + f true) / 2

/-- The investment cost is zero for waiting and `1 + s` for investment. -/
def firstCost (s a : Bool) : ℝ := if a then 1 + (if s then 1 else 0) else 0

/-- The second state is the indicator of an initially successful investment. -/
def transition (s a : Bool) : Bool := s && a

/-- The second action has no effect on the terminal reward. -/
def terminalCost (m : ℝ) (s _a : Bool) : ℝ := if s then -m else 0

/-- Actual two-step cost along a trajectory. -/
def cost (m : ℝ) (s a b : Bool) : ℝ :=
  firstCost s a + terminalCost m (transition s a) b

/-- Any deterministic second-step policy may be used. -/
def policyValue (m : ℝ) (b : Bool → Bool) : ℝ :=
  mean fun s => cost m s s (b (transition s s))

/-- The open-loop first action is sampled independently with the policy's marginal. -/
def openLoopValue (m : ℝ) (b : Bool) : ℝ :=
  mean fun s => mean fun a => cost m s a b

/-- The adaptive first action has uniform marginal, justifying the open-loop experiment. -/
theorem action_marginal (a : Bool) :
    mean (fun s => if s = a then 1 else 0) = 1 / 2 := by
  cases a <;> norm_num [mean]

/-- Trace covariance of the first cost vector and the one-hot adaptive action. -/
def myopicCovariance : ℝ :=
  ∑ a : Bool, (mean (fun s => firstCost s a * (if s = a then 1 else 0)) -
    mean (fun s => firstCost s a) * mean (fun s => if s = a then 1 else 0))

/-- Terminal action-independent costs have zero trace covariance for every second policy. -/
theorem terminal_covariance (m : ℝ) (b : Bool → Bool) :
    (∑ a : Bool,
      (mean (fun s => terminalCost m (transition s s) a *
        (if b (transition s s) = a then 1 else 0)) -
      mean (fun s => terminalCost m (transition s s) a) *
        mean (fun s => if b (transition s s) = a then 1 else 0))) = 0 := by
  cases h₀ : b false <;> cases h₁ : b true <;>
    simp [mean, terminalCost, transition, h₀, h₁] <;> ring

/-- The exact finite-experiment identities in Proposition 3.8. -/
theorem sign_reversal (m : ℝ) (hm : 1 < m) (b : Bool → Bool) (b' : Bool) :
    myopicCovariance = 1 / 4 ∧ 0 < myopicCovariance ∧
    policyValue m b - openLoopValue m b' = (1 - m) / 4 ∧
    policyValue m b - openLoopValue m b' < 0 := by
  have hcov : myopicCovariance = 1 / 4 := by
    norm_num [myopicCovariance, mean, firstCost, Fintype.sum_bool]
  have hgap : policyValue m b - openLoopValue m b' = (1 - m) / 4 := by
    simp only [policyValue, openLoopValue, mean, cost, firstCost, terminalCost, transition,
      Bool.and_false, Bool.and_true, Bool.false_eq_true,
      ↓reduceIte]
    ring
  refine ⟨hcov, by rw [hcov]; norm_num, hgap, ?_⟩
  rw [hgap]
  linarith

end Cslib.Probability.AdaptivePolicy.SignReversal
