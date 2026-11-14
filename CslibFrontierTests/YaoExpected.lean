/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.QueryComplexity.YaoExpected

/-! # Expected-cost Yao on empty coordinates and infinite output types -/

set_option linter.privateModule false

open Cslib Convexity Cslib.QueryComplexity

-- No coordinate is queried, while outputs inhabit the infinite type ℕ.
example : zeroErrorComplexity (fun _ : Empty → Bool => (7 : ℕ)) = 0 := by
  refine le_antisymm (zeroErrorComplexity_le
    (RandomizedDecisionTree.computes_single (t := DecisionTree.leaf 7) (fun _ => rfl)
      le_rfl) ?_) zeroErrorComplexity_nonneg
  intro x
  simp

example (ν : StdSimplex ℝ (Empty → Bool)) :
    distributionalExpectedComplexity ν (fun _ => (7 : ℕ)) = 0 := by
  refine le_antisymm (distributionalExpectedComplexity_le
    (t := DecisionTree.leaf 7) (fun _ => rfl) (by simp)) ?_
  exact le_distributionalExpectedComplexity fun t _ => t.distributionalCost_nonneg ν

private def bitValue (x : Unit → Bool) : ℕ := if x () then 37 else 12
private def bitTree : DecisionTree Unit ℕ := .node () (.leaf 12) (.leaf 37)

private theorem bitTree_computes : bitTree.Computes bitValue := by
  intro x
  cases h : x () <;> simp [bitTree, bitValue, DecisionTree.eval_node, h]

private theorem bitValue_complexity : zeroErrorComplexity bitValue = 1 := by
  refine le_antisymm (zeroErrorComplexity_le
    (RandomizedDecisionTree.computes_single bitTree_computes le_rfl) ?_) ?_
  · intro x
    rw [RandomizedDecisionTree.expectedCost_single]
    simp [bitTree, DecisionTree.cost, DecisionTree.weightedCost_node]
  · apply one_le_zeroErrorComplexity
    exact ⟨fun _ => false, fun _ => true, by decide⟩

-- Obtain an optimal algorithm and a hard distribution at the concrete value 1.
example : ∃ (μ : RandomizedDecisionTree Unit ℕ) (ν : StdSimplex ℝ (Unit → Bool)),
    μ.Computes 0 bitValue ∧ (∀ x, μ.expectedCost x ≤ 1) ∧
      ∀ t : DecisionTree Unit ℕ, t.Computes bitValue → 1 ≤ t.distributionalCost ν := by
  simpa only [bitValue_complexity] using exists_optimal_expectedCost bitValue

example : (⨆ ν : StdSimplex ℝ (Unit → Bool),
    distributionalExpectedComplexity ν bitValue) = 1 :=
  (zeroErrorComplexity_eq_iSup_distributionalExpectedComplexity bitValue).symm.trans
    bitValue_complexity

-- Each distribution has an attained deterministic optimum, even with an infinite output type.
example (ν : StdSimplex ℝ (Unit → Bool)) : ∃ t : DecisionTree Unit ℕ,
    t.Computes bitValue ∧ t.distributionalCost ν = distributionalExpectedComplexity ν bitValue :=
  exists_computes_distributionalCost_eq ν bitValue
