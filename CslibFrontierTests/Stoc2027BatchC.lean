/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.AdaptivePolicy.SignReversal
import CslibFrontier.Algorithms.Lean.Submodular.OracleSavings
import CslibFrontier.Probability.PeerPrediction.Quadratic
import Mathlib.Tactic

/-! Nonvacuity and boundary clients for the three selected batch-C endpoints. -/

noncomputable section
open Finset Matrix
namespace CslibFrontierTests.Stoc2027BatchC

example : Cslib.Probability.AdaptivePolicy.SignReversal.myopicCovariance = 1 / 4 ∧
    0 < Cslib.Probability.AdaptivePolicy.SignReversal.myopicCovariance ∧
    Cslib.Probability.AdaptivePolicy.SignReversal.policyValue 2 (fun _ => false) -
      Cslib.Probability.AdaptivePolicy.SignReversal.openLoopValue 2 false = (1 - 2) / 4 ∧
    Cslib.Probability.AdaptivePolicy.SignReversal.policyValue 2 (fun _ => false) -
      Cslib.Probability.AdaptivePolicy.SignReversal.openLoopValue 2 false < 0 :=
  Cslib.Probability.AdaptivePolicy.SignReversal.sign_reversal 2 (by norm_num) _ _

open Cslib.Algorithms.Lean.Submodular.OracleSavings in
example : savings (fun _ : Bool => (1 : ℝ)) (fun _ => 1) {false} = 1 ∧
    savings (fun _ : Bool => (1 : ℝ)) (fun _ => 1) univ = 0 := by
  norm_num [savings, failureProbability, remainingCost, Fintype.sum_bool, Fintype.prod_bool,
    Finset.card_compl]

-- Adding an oracle can decrease savings: monotonicity is deliberately not required.
open Cslib.Algorithms.Lean.Submodular in
example : IsSubmodular (OracleSavings.savings (fun _ : Bool => (1 : ℝ)) (fun _ => 1)) :=
  OracleSavings.savings_isSubmodular (by intro i; norm_num) (by intro i; norm_num)
    (by intro i; norm_num)

open Cslib.Probability.PeerPrediction.Quadratic

private def correlated : Matrix Bool Bool ℝ := fun i j => if i = j then 1 / 2 else 0
private def independent : Matrix Bool Bool ℝ := fun _ _ => 1 / 4

private theorem correlated_joint : IsJoint correlated := by
  constructor
  · intro i j; unfold correlated; split <;> norm_num
  · norm_num [rowMarginal, correlated, Fintype.sum_bool]

private theorem independent_joint : IsJoint independent := by
  constructor
  · intro i j; norm_num [independent]
  · norm_num [rowMarginal, independent, Fintype.sum_bool]

example : qmi correlated = 1 / 4 := by
  norm_num [qmi, centered, rowMarginal, colMarginal, correlated, Fintype.sum_bool]

example : Independent independent := by
  intro i j
  norm_num [independent, rowMarginal, colMarginal, Fintype.sum_bool]

example : expectFour correlated payment = 1 / 4 := by
  rw [payment_unbiased correlated_joint]
  norm_num [qmi, centered, rowMarginal, colMarginal, correlated, Fintype.sum_bool]

example : expectFour independent payment = 0 := by
  rw [payment_unbiased independent_joint]
  norm_num [qmi, centered, rowMarginal, colMarginal, independent, Fintype.sum_bool]

-- Individual payments may be negative even though their expectation is nonnegative.
example : payment (false, false) (false, true) (true, false) (true, true) = -2 := by
  norm_num [payment]

private theorem uniform_noise : mixed (1 / 2) (1 : Matrix Bool Bool ℝ) (fun _ => 1 / 2) ∈
    colStochastic ℝ Bool := by
  exact mixed_stochastic (by norm_num) (by norm_num) (one_mem _)
    (by intro i; norm_num) (by norm_num [Fintype.sum_bool])

example : expectFour
    (mixed (1 / 2) (1 : Matrix Bool Bool ℝ) (fun _ => 1 / 2) * correlated) payment ≤
    expectFour correlated payment := by
  have h := truthful_alice correlated_joint (1 : Matrix Bool Bool ℝ) (one_mem _)
    (lam := 1 / 2) (by norm_num) (by norm_num) (D := 1) (one_mem _)
    (q := fun _ => 1 / 2) (by intro i; norm_num) (by norm_num [Fintype.sum_bool])
  simpa using h

example : qmi (mixed (1 / 2) (1 : Matrix Bool Bool ℝ) (fun _ => 1 / 2) * correlated) =
    1 / 16 := by
  norm_num [qmi, centered, rowMarginal, colMarginal, mixed, correlated,
    Matrix.mul_apply, Matrix.one_apply, Fintype.sum_bool]

example : expectFour
    ((mixed (1 / 2) (1 : Matrix Bool Bool ℝ) (fun _ => 1 / 2) * correlated) *
      (mixed 0 (1 : Matrix Bool Bool ℝ) (fun _ => 1 / 2))ᵀ) payment ≤
    expectFour (mixed (1 / 2) (1 : Matrix Bool Bool ℝ) (fun _ => 1 / 2) * correlated)
      payment :=
  truthful_bob correlated_joint _ uniform_noise (by norm_num) (by norm_num)
    (one_mem _) (by intro i; norm_num) (by norm_num [Fintype.sum_bool])

-- Unequal alphabets and a zero marginal: no hidden full-support or square-table assumption.
private def rectangular : Matrix Bool (Fin 3) ℝ :=
  fun _i j => if j = 0 then 1 / 2 else 0

example : IsJoint rectangular := by
  constructor
  · intro i j; unfold rectangular; split <;> norm_num
  · norm_num [rowMarginal, rectangular, Fintype.sum_bool, Fin.sum_univ_succ]

example : Independent rectangular := by
  intro i j
  fin_cases j <;> cases i <;>
    norm_num [rectangular, rowMarginal, colMarginal, Fintype.sum_bool, Fin.sum_univ_succ]


end CslibFrontierTests.Stoc2027BatchC
