/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.FiniteSampleInformation.Rigidity
import CslibFrontier.Probability.FiniteSampleInformation.QuadraticBridge
import CslibFrontier.Probability.FiniteSampleInformation.CopositiveDPIRecognition

/-!
# Clients of the finite-sample information theorems

These examples use actual probability tables and actual signed sample statistics.
Boundary witnesses include a dependent zero-row law and the zero-sample case.
-/

noncomputable section
open scoped BigOperators
open Cslib.FiniteSampleInformation
open GeneralAsymmetricC1

/-- A statistic estimating a single outcome's squared mass. -/
def collisionAt (v : Fin 2 → Bool) : ℝ := if v 0 = false ∧ v 1 = false then 1 else 0

example (p : Bool → ℝ) : Estimation.expectation p 2 collisionAt = p false ^ 2 := by
  simp [Estimation.expectation, collisionAt, pow_two]

-- A zero-sample statistic is constant, with no probability positivity assumption.
example (p : Bool → ℝ) : Estimation.expectation p 0 (fun _ => (-3 : ℝ)) = -3 := rfl

-- The converse actually supplies a statistic with the prescribed number of tasks.
example : ∃ g : (Fin 3 → Bool) → ℝ,
    ∀ p, Estimation.IsProbability p →
      Estimation.expectation p 3 g = p false ^ 2 - 2 * p true := by
  let P : MvPolynomial Bool ℝ := MvPolynomial.X false ^ 2 -
    MvPolynomial.C 2 * MvPolynomial.X true
  obtain ⟨g, hg⟩ := Estimation.polynomial_unbiased P 3 (by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_pow _ _).trans (by norm_num)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by norm_num))
  refine ⟨g, fun p hp => ?_⟩
  simpa [P] using hg p hp

-- A real rectangular law makes the exact degree-six bound nonvacuous.
example : Simplex (diagonalLaw (show 3 ≤ 4 by decide)) ∧
    0 < GramDependence.gramDet (diagonalLaw (show 3 ≤ 4 by decide)) :=
  ⟨diagonalLaw_simplex (by decide) _, diagonalLaw_gramDet_pos (by decide) _⟩

example : (GramDependence.gramDetPoly 3 4).totalDegree = 6 := by
  exact GramDependence.gramDetPoly_totalDegree (by decide)

-- A dependent distribution with a null row is forced to zero by smooth DPI.
example (F : Mat 3 2 → ℝ) (hC1 : ContDiff ℝ 1 F) (hDPI : DPI F) (hIZ : RKO F) :
    F (dependentZeroRowWitness (by decide : 3 ≤ 3) (by decide : 2 ≤ 2)) = 0 ∧
      ¬(Matrix.of (dependentZeroRowWitness (by decide : 3 ≤ 3)
        (by decide : 2 ≤ 2))).rank ≤ 1 := by
  refine ⟨?_, dependentZeroRowWitness_rank_not_le_one _ _⟩
  exact general_asymmetric_simplex_C1 (by decide) (by decide) F hC1 hDPI hIZ _
    (dependentZeroRowWitness_simplex _ _)

-- The sample lower bound rules out a real nontrivial five-task 3-by-3 mechanism.
example (M : Payment 3 3 5) (hT : TruthfulAlice M) (hIZ : IndependenceZeroPayment M) :
    ¬NontrivialPayment M := by
  intro hN
  have := square_payment_task_lower_bound (by decide : 2 ≤ 3) M hT hIZ hN
  omega

-- Eight tasks suffice at four symbols, with actual expected payment and both incentives.
example : ∃ M : Payment 4 4 8,
    DominantlyTruthful M ∧ expectedPayment M (diagonalLaw (le_refl 4)) = (1 / 4 : ℝ) ^ 8 := by
  obtain ⟨M, _, hDom, _, hM⟩ := exists_optimal_square_payment (by decide : 2 ≤ 4)
  refine ⟨M, hDom, ?_⟩
  rw [hM _ (diagonalLaw_simplex (by decide) _)]
  have heq : Matrix.of (diagonalLaw (le_refl 4)) =
      (1 / 4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    simp [diagonalLaw, Matrix.one_apply, eq_comm]
  rw [heq, Matrix.det_smul, Matrix.det_one]
  norm_num

-- The same binary Gram statistic is faithful with four tasks against a larger peer alphabet.
example : ∃ M : Payment 2 5 4, TruthfulAlice M ∧ FaithfulPayment M ∧
    expectedPayment M (diagonalLaw (show 2 ≤ 5 by decide)) ≠ 0 := by
  obtain ⟨M, hT, hF⟩ := exists_four_task_faithful_payment (by decide : 2 ≤ 5)
  refine ⟨M, hT, hF, ?_⟩
  intro hzero
  have hRank := (hF _ (diagonalLaw_simplex (by decide) _)).mp hzero
  have hFull := (GramDependence.gramDet_ne_zero_iff_rank_eq_height _).mp
    (diagonalLaw_gramDet_pos (by decide : 0 < 2) (by decide : 2 ≤ 5)).ne'
  omega

-- Two-sided faithfulness fails as soon as either alphabet has more than two states.
example : ¬∃ d, ∃ M : Payment 2 3 d,
    TruthfulAlice M ∧ TruthfulAlice (swapPayment M) ∧ FaithfulPayment M := by
  rw [exists_two_sided_faithful_payment_iff (by decide) (by decide)]
  decide

-- A four-task binary reward is faithful from both orientations.
example : ∃ M : Payment 2 2 4,
    TruthfulAlice M ∧ TruthfulAlice (swapPayment M) ∧ FaithfulPayment M ∧
      NontrivialPayment M := by
  obtain ⟨M, hA, hB, hF⟩ := exists_four_task_two_sided_faithful_payment
  exact ⟨M, hA, hB, hF, hF.nontrivial (by decide) (by decide)⟩

-- Dimension-changing hypotheses are consistent: the zero family satisfies them.
example : DimensionChangingDPI (fun _ _ _ => 0) := by
  intro k n m hk hn hm T hT U hU
  exact le_refl 0

-- Collapse applies to a concrete dependent wide law as well as to tall laws.
example (F : (n m : ℕ) → Mat n m → ℝ) (hDPI : DimensionChangingDPI F)
    (hC1 : ∀ n m, 2 ≤ n → 2 ≤ m → ContDiffOnSimplex (F n m))
    (hIZ : ∀ n m, 2 ≤ n → 2 ≤ m → RKO (F n m)) :
    F 2 3 (diagonalLaw (show 2 ≤ 3 by decide)) = 0 := by
  exact dimensionChanging_collapse hDPI hC1 hIZ (by decide) (by decide)
    (diagonalLaw_simplex (by decide) _)

end
