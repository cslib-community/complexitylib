/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Parity
import Complexity.Computability.QueryComplexity.Huang
import Complexity.Computability.QueryComplexity.Relations

/-! Degree, Nisan's relations and Huang's sensitivity theorem on concrete functions: parity,
disjunction and conjunction of `n` bits, majority of three bits and the address function with one
address bit. Non-vacuity witnesses for the induced subgraph theorem. -/

namespace ComplexityTests.QueryComplexity.Measures

open Cslib Cslib.BitString Cslib.QueryComplexity Finset

/-! ### Disjunction, conjunction, parity, majority, and the address function -/

/-- The disjunction is sensitive to every bit at the all-false input. -/
private theorem sensitivityAt_or {n : ℕ} :
    sensitivityAt (threshold n 1) (fun _ => false) = n := by
  have h : sensitiveCoords (threshold n 1) (fun _ => false) = univ :=
    eq_univ_of_forall fun i => mem_sensitiveCoords.2 (by
      rw [IsSensitiveCoord, threshold_one_right, threshold_one_right]
      simp only [Bool.not_false, ne_eq, decide_eq_decide]
      exact fun h => absurd (h.1 ⟨i, by simp⟩) (by simp))
  rw [sensitivityAt, h, card_univ, Fintype.card_fin]

/-- The conjunction is sensitive to every bit at the all-true input. -/
private theorem sensitivityAt_and {n : ℕ} :
    sensitivityAt (threshold n n) (fun _ => true) = n := by
  have h : sensitiveCoords (threshold n n) (fun _ => true) = univ :=
    eq_univ_of_forall fun i => mem_sensitiveCoords.2 (by
      rw [IsSensitiveCoord, threshold_self, threshold_self]
      simp only [Bool.not_true, ne_eq, decide_eq_decide]
      exact fun h => absurd (h.2 (fun _ => trivial) i) (by simp))
  rw [sensitivityAt, h, card_univ, Fintype.card_fin]

/-- The address function with one address bit: bit `0` selects bit `1` or bit `2`. -/
private def address : BooleanFunction 3 := fun x => if x 0 then x 2 else x 1

/-- Read as signs, majority of three bits has Fourier coefficient `-1/2` on all three coordinates:
the sum defining it, computed over `ℤ`, is `-4`. -/
private theorem fourierCoeff_majority_three_univ :
    fourierCoeff (fun x : BitString 3 => signVal (majority 3 x)) univ = -1 / 2 := by
  have hint : ∑ x : BitString 3, (if majority 3 x then (-1 : ℤ) else 1) * chi ℤ univ x = -4 := by
    decide
  have hreal : ∑ x : BitString 3, signVal (majority 3 x) * chi ℝ univ x = -4 := by
    rw [← show ((-4 : ℤ) : ℝ) = -4 by norm_num, ← hint]
    push_cast [signVal, chi]
    rfl
  rw [fourierCoeff_eq_sum, hreal, Fintype.card_fin]
  norm_num

example {n : ℕ} :
    (degree (threshold n 1) = n ∧ sensitivity (threshold n 1) = n ∧
      DecisionTree.complexity (threshold n 1) = n) ∧
    (degree (threshold n n) = n ∧ sensitivity (threshold n n) = n ∧
      DecisionTree.complexity (threshold n n) = n) ∧
    (degree (parity n) = n ∧ sensitivity (parity n) = n) ∧
    (fun x : BitString 3 => bitVal ℝ (parity 3 x)) ∉ lowDegree ℝ (Fin 3) 2 ∧
    fourierCoeff (fun x : BitString 2 => signVal (parity 2 x)) univ ≠ 0 ∧
    (sensitivity (majority 3) = 2 ∧ blockSensitivity (majority 3) = 2 ∧
      certificateComplexity (majority 3) = 2 ∧ degree (majority 3) = 3) ∧
    (sensitivity address = 2 ∧ blockSensitivity address = 2 ∧
      certificateComplexity address = 2 ∧ blockSensitivityFor address false = 2 ∧
      certificateComplexityFor address true = 2 ∧
      certificateComplexity address ≤ 4 ∧ DecisionTree.complexity address ≤ 4) := by
  refine ⟨⟨degree_threshold_one_right,
      le_antisymm (sensitivity_le_card _) (sensitivityAt_or.symm.trans_le
        (sensitivityAt_le_sensitivity _ _)),
      DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card sensitivityAt_or⟩,
    ⟨degree_threshold_self,
      le_antisymm (sensitivity_le_card _) (sensitivityAt_and.symm.trans_le
        (sensitivityAt_le_sensitivity _ _)),
      DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card sensitivityAt_and⟩,
    ⟨degree_parity, sensitivity_parity⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    have := QueryComplexity.degree_le_iff_mem_lowDegree.2 h
    rw [degree_parity] at this
    omega
  · rw [parity, fourierCoeff_signVal_parityOn]
    simp
  · refine ⟨by decide, by decide, by decide, le_antisymm (degree_le_card _) ?_⟩
    have h := card_le_degree_of_fourierCoeff_ne_zero (f := majority 3) (S := univ) (by
      rw [fourierCoeff_majority_three_univ]
      norm_num)
    rwa [card_univ, Fintype.card_fin] at h
  · have h₁ := certificateComplexity_le_sensitivity_mul_blockSensitivity address
    have h₂ := DecisionTree.complexity_le_blockSensitivityFor_mul_certificateComplexityFor address
    rw [show sensitivity address = 2 by decide, show blockSensitivity address = 2 by decide] at h₁
    rw [show blockSensitivityFor address false = 2 by decide,
      show certificateComplexityFor address true = 2 by decide] at h₂
    exact ⟨by decide, by decide, by decide, by decide, by decide, h₁, h₂⟩

/-! ### The general bounds and the induced subgraph theorem -/

example {n : ℕ} (f : BooleanFunction n) {ι : Type*} [LinearOrder ι] [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (v : (ι → Bool) → ℝ) :
    (degree f ≤ DecisionTree.complexity f ∧ degree f ≤ sensitivity f ^ 2 ∧
      √(degree f : ℝ) ≤ sensitivity f) ∧
    (certificateComplexity f ≤ sensitivity f * blockSensitivity f ∧
      DecisionTree.complexity f ≤ certificateComplexity f * blockSensitivity f ∧
      DecisionTree.complexity f ≤ blockSensitivity f ^ 3) ∧
    totalDegree (fun x : BitString 2 =>
      bitVal ℝ ((DecisionTree.node (0 : Fin 2) (.leaf false) (.leaf true)).eval x)) ≤ 1 ∧
    2 ^ Fintype.card ι < 2 * #(univ : Finset (ι → Bool)) ∧
    (∃ x ∈ ({![false, false], ![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      2 ≤ #{i | Function.update x i (!x i) ∈
        ({![false, false], ![true, false], ![false, true]} : Finset (Fin 2 → Bool))}) ∧
    signedAdjacency S (signedAdjacency S v) = (#S : ℝ) • v := by
  refine ⟨⟨DecisionTree.degree_le_complexity f, degree_le_sensitivity_sq f,
      sqrt_degree_le_sensitivity f⟩,
    ⟨certificateComplexity_le_sensitivity_mul_blockSensitivity f,
      DecisionTree.complexity_le_certificateComplexity_mul_blockSensitivity f,
      DecisionTree.complexity_le_blockSensitivity_pow_three f⟩,
    DecisionTree.totalDegree_comp_eval_le _ _, ?_, ?_, signedAdjacency_signedAdjacency S v⟩
  · rw [card_univ, Fintype.card_fun, Fintype.card_bool]
    have := Nat.two_pow_pos (Fintype.card ι)
    omega
  · obtain ⟨x, hx, h⟩ := exists_mem_sqrt_card_le_card_update_mem
      (V := {![false, false], ![true, false], ![false, true]}) (by decide) (univ : Finset (Fin 2))
    refine ⟨x, hx, ?_⟩
    rw [card_univ, Fintype.card_fin] at h
    have h1 : (1 : ℝ) < √(2 : ℕ) := by
      rw [Real.lt_sqrt zero_le_one]
      norm_num
    exact_mod_cast h1.trans_le h

end ComplexityTests.QueryComplexity.Measures
