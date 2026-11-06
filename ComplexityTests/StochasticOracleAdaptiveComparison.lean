/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptiveComparison
import Mathlib.Tactic

/-! A response law whose success probability increases after its first success. -/

public section
noncomputable section
open Cslib.Optimization.OneConstraint Cslib.Probability.StochasticOracle
namespace StochasticOracleAdaptiveComparisonTests

/-- The entire history determines which conditional response law is used. -/
@[expose] def law (h : List Bool) : Distribution Bool ℝ :=
  if true ∈ h then pair true false (3 / 4) (by norm_num) (by norm_num)
  else pair true false (1 / 4) (by norm_num) (by norm_num)

private theorem envelope (h : List Bool) :
    (law h).mean (fun x => if x then 1 else 0) ≤ (3 / 4 : ℝ) := by
  unfold law
  split_ifs <;> norm_num [pair_mean]

/-- Comparison bounds the actual history-dependent two-turn success event. -/
theorem correlated_tail :
    progressExpectation law (fun _ x => x) (fun k => if 2 ≤ k then 1 else 0) 2 [] 0 ≤
      (9 / 16 : ℝ) := by
  have hf : Monotone (fun k : ℕ => if 2 ≤ k then (1 : ℝ) else 0) := by
    intro a b hab
    dsimp only
    split_ifs <;> norm_num; omega
  have h := progressExpectation_le law (fun _ x => x) (3 / 4) (by norm_num)
    (by norm_num) envelope _ hf 2 [] 0
  norm_num [bernoulliExpectation] at h
  exact h

/-- The actual probability differs from the product of the initial success
probability with itself: actual responses are positively correlated. -/
theorem actual_tail :
    progressExpectation law (fun _ x => x) (fun k => if 2 ≤ k then 1 else 0) 2 [] 0 =
      (3 / 16 : ℝ) := by
  norm_num [progressExpectation, law, pair_mean]

/-- The lower envelope is also instantiated at every possible history. -/
theorem lower_tail :
    (1 / 16 : ℝ) ≤
      progressExpectation law (fun _ x => x) (fun k => if 2 ≤ k then 1 else 0) 2 [] 0 := by
  have hf : Monotone (fun k : ℕ => if 2 ≤ k then (1 : ℝ) else 0) := by
    intro a b hab
    dsimp only
    split_ifs <;> norm_num; omega
  have h := le_progressExpectation law (fun _ x => x) (1 / 4) (by norm_num)
    (by norm_num) (by intro h; unfold law; split_ifs <;> norm_num [pair_mean]) _ hf 2 [] 0
  norm_num [bernoulliExpectation] at h
  exact h

end StochasticOracleAdaptiveComparisonTests
