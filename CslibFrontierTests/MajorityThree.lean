/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.QueryComplexity.MajorityThree

/-! # Optimal majority algorithms, hard inputs and repeated queries -/

set_option linter.privateModule false

open Cslib Cslib.QueryComplexity Cslib.BitString

example : zeroErrorComplexity (majority 3) = 8 / 3 := zeroErrorComplexity_majority_three

example : MajorityThree.algorithm.expectedCost (fun _ => false) = 2 := by
  rw [MajorityThree.algorithm_expectedCost]
  norm_num

example : MajorityThree.algorithm.expectedCost ![false, false, true] = 8 / 3 := by
  rw [MajorityThree.algorithm_expectedCost]
  norm_num

example : MajorityThree.hardDistribution.weights (fun _ => true) = 0 := by
  rw [MajorityThree.weights_hardDistribution]
  simp

example : MajorityThree.hardDistribution.weights ![false, false, true] = 1 / 6 := by
  rw [MajorityThree.weights_hardDistribution]
  have hfalse : (![false, false, true] : BitString 3) ≠ (fun _ => false) := by decide
  have htrue : (![false, false, true] : BitString 3) ≠ (fun _ => true) := by decide
  simp [hfalse, htrue]

-- An unnecessary initial query is charged, while the all-tree lower bound still applies.
private def repeated : DecisionTree (Fin 3) Bool :=
  .node 0 (MajorityThree.queryOrder (Equiv.refl _)) (MajorityThree.queryOrder (Equiv.refl _))

private theorem repeated_computes : repeated.Computes (majority 3) := by
  intro x
  simp [repeated, DecisionTree.eval_node, MajorityThree.queryOrder_eval]

example : repeated.cost ![false, false, true] = 3 := rfl
example : repeated.cost ![false, true, false] = 4 := rfl

example : (8 : ℝ) / 3 ≤ repeated.distributionalCost MajorityThree.hardDistribution :=
  MajorityThree.hardDistribution_lower repeated repeated_computes
