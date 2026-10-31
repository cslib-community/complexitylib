/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PropertyTesting.LinearityLowerBound
import Complexity.Probability.PMF.Uniform
import ComplexityTests.BooleanAnalysisExamples

/-! Concrete sharpness and probability clients for the one-sided linearity query lower bound. -/

namespace ComplexityTests.PropertyTestingLinearityLowerBound

open Cslib Cslib.BitString Cslib.Probability BooleanAnalysisExamples
open scoped ENNReal

private def leftPoint : Fin 2 → Bool := ![true, false]
private def rightPoint : Fin 2 → Bool := ![false, true]

-- Check the BLR equation at the two coordinate vectors: exactly three queries suffice here.
private def checkTree : DecisionTree (Fin 2 → Bool) Bool :=
  DecisionTree.queryAll (fun f => decide ((f leftPoint ^^ f rightPoint) =
    f (leftPoint + rightPoint))) [leftPoint, rightPoint, leftPoint + rightPoint] fun _ => false

private theorem checkTree_complete : ∀ S : Finset (Fin 2), checkTree.eval (parityOn S) = true := by
  decide

private theorem checkTree_rejects : checkTree.eval and₂ = false := by decide

example : checkTree.depth = 3 := by decide

example : 3 ≤ (checkTree.queries and₂).card :=
  checkTree.three_le_card_queries_of_parity_complete checkTree_complete (by decide)
    (by rw [checkTree_rejects]; decide)

-- Conjunction satisfies the normalization and distance promise; this is a genuine no-instance.
example : and₂ 0 = false ∧ ∀ S : Finset (Fin 2), 1 ≤ hammingDist and₂ (parityOn S) := by decide

-- The interpolation statement covers a zero point and a repeated nonzero point.
example : ∃ S : Finset (Fin 2), parityOn S 0 = and₂ 0 ∧
    parityOn S leftPoint = and₂ leftPoint :=
  exists_parityOn_agrees_pair (by decide) 0 leftPoint

example : ∃ S : Finset (Fin 2), parityOn S leftPoint = and₂ leftPoint ∧
    parityOn S leftPoint = and₂ leftPoint :=
  exists_parityOn_agrees_pair (by decide) leftPoint leftPoint

private def chooseTree (b : Bool) : DecisionTree (Fin 2 → Bool) Bool :=
  if b then checkTree else .leaf true

private noncomputable def coinTester : PMF (DecisionTree (Fin 2 → Bool) Bool) :=
  (PMF.uniformOfFintype Bool).map chooseTree

private theorem coinTester_complete (S : Finset (Fin 2)) :
    coinTester.toOuterMeasure {t | t.eval (parityOn S) ≠ true} = 0 := by
  rw [coinTester, PMF.toOuterMeasure_map_apply]
  have hempty : chooseTree ⁻¹' {t | t.eval (parityOn S) ≠ true} = ∅ := by
    ext b
    cases b <;> simp [chooseTree, checkTree_complete]
  rw [hempty]
  simp

-- The tester makes zero or three queries with equal probability and rejects conjunction with
-- probability 1/2. The lower bound concerns a positive-mass three-query run, not expected depth.
private theorem coinTester_rejects :
    coinTester.toOuterMeasure {t | t.eval and₂ ≠ true} = 1 / 2 := by
  rw [coinTester, PMF.toOuterMeasure_map_apply]
  have hevent : chooseTree ⁻¹' {t | t.eval and₂ ≠ true} = {true} := by
    ext b
    cases b <;> simp [chooseTree, checkTree_rejects]
  rw [hevent, PMF.toOuterMeasure_uniformOfFintype]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

example : ∃ t ∈ coinTester.support, 3 ≤ t.depth :=
  exists_three_le_depth_of_parity_complete coinTester coinTester_complete (f := and₂) (by decide)
    (by rw [coinTester_rejects]; norm_num)

-- The existing finite-simplex model receives the same worst-case lower bound.
example : 3 ≤ RandomizedDecisionTree.depth (Convexity.StdSimplex.single checkTree :
    RandomizedDecisionTree (Fin 2 → Bool) Bool) := by
  apply RandomizedDecisionTree.three_le_depth_of_parity_complete (f := and₂)
  · intro S
    simp [RandomizedDecisionTree.errorProb, checkTree_complete]
  · decide
  · simp [RandomizedDecisionTree.errorProb, checkTree_rejects]

end ComplexityTests.PropertyTestingLinearityLowerBound
