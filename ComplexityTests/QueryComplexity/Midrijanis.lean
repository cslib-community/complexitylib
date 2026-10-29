/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Midrijanis
import Complexity.Foundations.Data.Finset.Expect

/-!
The conjunction of two coordinates with a third, irrelevant coordinate has degree and block
sensitivity `2`. At the all-false input it has no sensitive coordinate but has a sensitive block
of size `2`, so the maximal-support lemma must produce blocks rather than single coordinates.
The new product bound gives `D ≤ 4`. For the same conjunction on `100` input coordinates, the
cubic degree corollary gives `D ≤ 16`, below both the input-length bound `100` and the former
sixth-power degree bound `512`. Constant functions exercise the zero-degree case.
-/

namespace ComplexityTests.QueryComplexity.Midrijanis

open Cslib Cslib.BitString Cslib.QueryComplexity Finset

/-- Two queried coordinates and one irrelevant coordinate. -/
private def andPair : BooleanFunction 3 := fun x => x 0 && x 1

private theorem degree_and_le_two {n : ℕ} (i j : Fin n) :
    degree (fun x : BitString n => x i && x j) ≤ 2 := by
  refine degree_le_iff_mem_lowDegree.2 ?_
  have hfun : (fun x : BitString n => bitVal ℝ (x i && x j)) =
      (fun x => bitVal ℝ (x i)) * (fun x => bitVal ℝ (x j)) := by
    funext x
    cases hi : x i <;> cases hj : x j <;> simp [hi, hj]
  rw [hfun]
  exact mul_mem_lowDegree (a := 1) (b := 1) (R := ℝ)
    (bitVal_mem_lowDegree (R := ℝ) i) (bitVal_mem_lowDegree (R := ℝ) j)

private theorem degree_andPair : degree andPair = 2 := by
  apply le_antisymm
  · exact degree_and_le_two 0 1
  · have hcoeff : fourierCoeff (fun x => bitVal ℝ (andPair x)) {0, 1} = 1 / 4 := by
      simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
      norm_num [chi, andPair, bitVal]
    have h := card_le_totalDegree_of_fourierCoeff_ne_zero (hcoeff.trans_ne (by norm_num))
    change #({0, 1} : Finset (Fin 3)) ≤ degree andPair at h
    simpa using h

/-- Sensitive block vs. singleton at the all-false input, simultaneous proper-subset sensitive
blocks, the native `deg · bs` product bound (`D ≤ 4`), the cubic bound with irrelevant inputs
(`D ≤ 16`), and the zero-degree constant case. -/
example (n : ℕ) (b : Bool) :
    (sensitivityAt andPair (fun _ => false) = 0 ∧
      blockSensitivityAt andPair (fun _ => false) = 1 ∧
      IsSensitiveBlock andPair (fun _ => false) {0, 1}) ∧
    (∃ S : Finset (Fin 3), #S = 2 ∧ ∀ x, ∃ B, B ⊆ S ∧ IsSensitiveBlock andPair x B) ∧
    DecisionTree.complexity andPair ≤ 4 ∧
    DecisionTree.complexity (fun x : BitString 100 => x 0 && x 1) ≤ 16 ∧
    DecisionTree.complexity (fun _ : BitString n => b) = 0 := by
  refine ⟨by decide,
    by simpa only [degree_andPair] using
      exists_card_eq_degree_forall_exists_isSensitiveBlock_subset andPair
        (by rw [degree_andPair]; decide),
    ?_,
    (DecisionTree.complexity_le_two_mul_degree_pow_three _).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (degree_and_le_two 0 1) 3)),
    ?_⟩
  · have h := DecisionTree.complexity_le_degree_mul_blockSensitivity andPair
    rwa [degree_andPair, show blockSensitivity andPair = 2 by decide] at h
  · have hdeg : degree (fun _ : BitString n => b) = 0 :=
      Nat.eq_zero_of_le_zero (degree_le_iff_mem_lowDegree.2 (const_mem_lowDegree 0 _))
    have h := DecisionTree.complexity_le_two_mul_degree_pow_three (fun _ : BitString n => b)
    exact Nat.eq_zero_of_le_zero (by simpa [hdeg] using h)

end ComplexityTests.QueryComplexity.Midrijanis
