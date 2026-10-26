/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.Parity.Weight
import Complexity.Computability.DecisionTree.Symmetric
import Complexity.Computability.QueryComplexity.Monotone
import Complexity.Computability.QueryComplexity.SensitivityBounds
import Complexity.Computability.QueryComplexity.Threshold

/-! Sensitivity, block sensitivity, certificate and decision tree complexity of threshold,
majority, monotone and symmetric functions, one-sided bounds and polynomial bounds in sensitivity:
concrete values checked against the general formulas, and witnesses that the monotonicity and
symmetry hypotheses are satisfiable. -/

namespace ComplexityTests.QueryComplexity.Sensitivity

open Cslib Cslib.BitString Cslib.QueryComplexity Finset

/-! ### Threshold functions -/

/-- The sensitivity of `Th^4_2`, computed exhaustively, is `max(2, 4 + 1 - 2) = 3`, and so is its
certificate complexity by the general formula. -/
example : sensitivity (threshold 4 2) = 3 ∧ certificateComplexity (threshold 4 2) = 3 := by
  refine ⟨by decide, ?_⟩
  rw [certificateComplexity_threshold (by norm_num) (by norm_num)]
  rfl

example : sensitivity (threshold 4 2) = max 2 (4 + 1 - 2) :=
  sensitivity_threshold (by norm_num) (by norm_num)

example : sensitivity (majority 5) = 3 ∧ blockSensitivity (threshold 5 2) = 4 :=
  ⟨sensitivity_majority (by norm_num), blockSensitivity_threshold (by norm_num) (by norm_num)⟩

/-- One true bit certifies the disjunction, but its value `0` needs every bit. -/
example : certificateComplexityFor (threshold 3 1) true = 1 ∧
    certificateComplexityFor (threshold 3 1) false = 3 ∧
    certificateComplexity (threshold 3 1) = 3 :=
  ⟨certificateComplexityFor_threshold_one_right_true (by norm_num),
    certificateComplexityFor_threshold_one_right_false, certificateComplexity_threshold_one_right⟩

example : certificateComplexityFor (threshold 3 1) true = 1 := by decide

example {n : ℕ} : sensitivityAt (threshold n 1) (fun _ => false) = n ∧
    blockSensitivity (threshold n 1) = n :=
  ⟨sensitivityAt_threshold_one_right, blockSensitivity_threshold_one_right⟩

example {n : ℕ} : sensitivity (parity n) = n ∧ blockSensitivity (parity n) = n ∧
    certificateComplexity (parity n) = n :=
  ⟨sensitivity_parity, blockSensitivity_parity, certificateComplexity_parity⟩

/-! ### Evasiveness -/

example : DecisionTree.complexity (majority 4) = 4 ∧ DecisionTree.complexity (threshold 7 5) = 7 :=
  ⟨DecisionTree.complexity_majority (by norm_num),
    DecisionTree.complexity_threshold (by norm_num) (by norm_num)⟩

/-- Majority of four bits has sensitivity `3` yet is evasive. -/
example : sensitivity (majority 4) = 3 ∧ DecisionTree.complexity (majority 4) = 4 :=
  ⟨sensitivity_majority (by norm_num), DecisionTree.complexity_majority (by norm_num)⟩

/-- The symmetry hypothesis is satisfiable by a non-monotone function, parity. -/
example {n : ℕ} (hn : 1 ≤ n) : DecisionTree.complexity (parity n) = n :=
  DecisionTree.complexity_eq_card_of_isSymmetric isSymmetric_parity fun h => by
    have h0 : parity n (fun _ => false) = false := by
      rw [parity_eq_decide_weight]
      simp [weight]
    have h1 : parity n (Function.update (fun _ => false) ⟨0, hn⟩ true) = true := by
      rw [parity_eq_decide_weight, weight_update_true rfl, decide_eq_true_iff]
      simp [weight]
    exact Bool.false_ne_true (h0.symm.trans ((h _ _).trans h1))

/-! ### Monotone functions and one-sided measures -/

/-- The monotonicity hypothesis is satisfiable: majority is monotone, so `C = bs = s`. -/
example {n : ℕ} : certificateComplexity (majority n) = sensitivity (majority n) ∧
    blockSensitivity (majority n) = sensitivity (majority n) :=
  ⟨certificateComplexity_eq_sensitivity_of_monotone (monotone_threshold _),
    blockSensitivity_eq_sensitivity_of_monotone (monotone_threshold _)⟩

/-- A monotone function that is not symmetric: `x₀ ∧ (x₁ ∨ x₂)`. -/
abbrev andOr : BooleanFunction 3 := fun x => x 0 && (x 1 || x 2)

theorem monotone_andOr : Monotone andOr := fun x y hxy => by
  change (x 0 && (x 1 || x 2)) ≤ (y 0 && (y 1 || y 2))
  have h0 := hxy 0
  have h1 := hxy 1
  have h2 := hxy 2
  revert h0 h1 h2
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases y 0 <;> cases y 1 <;> cases y 2 <;> decide

example : ¬ andOr.IsSymmetric := fun h => by
  exact absurd (h ![true, true, false] ![false, true, true] (by decide)) (by decide)

/-- For `x₀ ∧ (x₁ ∨ x₂)`, `C = bs = s = 2`, the sensitivity computed exhaustively. -/
example : certificateComplexity andOr = 2 ∧ blockSensitivity andOr = 2 := by
  rw [certificateComplexity_eq_sensitivity_of_monotone monotone_andOr,
    blockSensitivity_eq_sensitivity_of_monotone monotone_andOr]
  exact ⟨by decide, by decide⟩

example : DecisionTree.complexity andOr ≤ 4 :=
  (DecisionTree.complexity_le_sensitivity_sq_of_monotone monotone_andOr).trans_eq
    (by rw [show sensitivity andOr = 2 by decide]; rfl)

/-- The one-sided sensitivity is computable. -/
example : sensitivityFor (threshold 3 1) false = 3 ∧ sensitivityFor (threshold 3 1) true = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

example {n : ℕ} (f : BooleanFunction n) :
    certificateComplexityFor f true ≤ sensitivityFor f false * blockSensitivityFor f true ∧
      DecisionTree.complexity f ≤ blockSensitivityFor f true * certificateComplexityFor f false ∧
      DecisionTree.complexity f ≤
        blockSensitivityFor f false * sensitivityFor f false * blockSensitivityFor f true ∧
      DecisionTree.complexity f ≤
        blockSensitivityFor f false * blockSensitivityFor f true * sensitivity f :=
  ⟨certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor f true,
    DecisionTree.complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor f false,
    DecisionTree.complexity_le_blockSensitivityFor_mul_sensitivityFor_mul_blockSensitivityFor
      f true,
    DecisionTree.complexity_le_blockSensitivityFor_mul_blockSensitivityFor_mul_sensitivity f⟩

example {n : ℕ} (f : BooleanFunction n) :
    certificateComplexity f ≤ 2 * sensitivity f ^ 5 ∧
      DecisionTree.complexity f ≤ sensitivity f * blockSensitivity f ^ 2 ∧
      DecisionTree.complexity f ≤ 2 * sensitivity f ^ 6 :=
  ⟨certificateComplexity_le_two_mul_sensitivity_pow_five f,
    DecisionTree.complexity_le_sensitivity_mul_blockSensitivity_sq f,
    DecisionTree.complexity_le_two_mul_sensitivity_pow_six f⟩

end ComplexityTests.QueryComplexity.Sensitivity
