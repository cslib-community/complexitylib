/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.PolynomialAtomCutoffs
import Complexity.Foundations.Probability.CorrectionAtom
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for polynomial atom cutoffs

Both switches vary in each interior example, producing exact value `1/4`. The broad witness
retains its strict entry/rank margin at its closed endpoints. Concrete existing atom and score
expressions use the new polynomial factors, and the witness's fourth-root variation forces
its Lipschitz constant to be positive.
-/

namespace ComplexityTests.PolynomialAtomCutoffs

open Cslib Finset Matrix

-- All three functions execute with rational inputs, including both transition regions.
/-- info: true -/
#guard_msgs in
#eval [polynomialPrepRow4 (8 : ℚ) 5 (3 / 250),
    polynomialAuxCutoff4 (8 : ℚ) (3 / 2) (3 / 25),
    polynomialWitnessCutoff4 (1000 : ℚ) 86 (53 / 2)] == [1 / 4, 1 / 4, 1 / 4]

private theorem witness_quarter : polynomialWitnessCutoff4 (1000 : ℚ) 86 (53 / 2) = 1 / 4 := by
  norm_num [polynomialWitnessCutoff4, polynomialSwitch4, polynomialTransition4,
    transitionPolynomial4]

-- Rational evaluation is exactly the real function used by the analytic theorems.
example : polynomialWitnessCutoff4 (1000 : ℝ) 86 (53 / 2) = 1 / 4 := by
  have h := polynomialWitnessCutoff4_ratCast 1000 86 (53 / 2)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, witness_quarter] at h
  exact h

example : polynomialPrepRow4 (8 : ℝ) (-4) (-1) = 0 ∧
    polynomialAuxCutoff4 (8 : ℝ) (-4) (-1) = 0 ∧
    polynomialWitnessCutoff4 (1000 : ℝ) (-4) (-1) = 0 := by
  exact ⟨polynomialPrepRow4_eq_zero_of_entry_le (by norm_num) (by norm_num),
    polynomialAuxCutoff4_eq_zero_of_entry_le (by norm_num) (by norm_num),
    polynomialWitnessCutoff4_eq_zero_of_entry_le (by norm_num) (by norm_num)⟩

-- The exact witness margin is 82 - 3*27 = 1; closure includes both boundary points.
example : (3 : ℝ) * 27 < 82 ∧ polynomialWitnessCutoff4 (1000 : ℝ) 82 0 = 0 ∧
    polynomialWitnessCutoff4 (1000 : ℝ) 90 27 = 0 ∧
    polynomialWitnessCutoff4 (1000 : ℝ) 90 26 = 1 := by
  exact ⟨by norm_num,
    polynomialWitnessCutoff4_eq_zero_of_entry_le (by norm_num) (by norm_num),
    polynomialWitnessCutoff4_eq_zero_of_rank_ge (by norm_num) (by norm_num),
    polynomialWitnessCutoff4_eq_one (by norm_num) (by norm_num) (by norm_num)⟩

private noncomputable def G : Matrix (Fin 2) (Fin 2) ℝ := !![0, 8; 0, 0]

private theorem first_row_rank : kthLargest 2 univ (fun y => G 0 y / 1) = 0 := by
  norm_num [kthLargest, G, Fin.univ_succ, filter_insert, filter_singleton]

-- This is an actual atom preparation and actual auxiliary score, not separate scalar formulas.
example : atomPrep (polynomialPrepCutoff4 8) (polynomialRowCutoff4 8) 2 1 G univ 0 1 = 1 ∧
    auxScore (polynomialAuxCutoff4 8) 2 1 G univ 0 1 = 1 := by
  constructor
  · rw [atomPrep, rowGate, first_row_rank]
    have hv : G 0 1 / 1 = 8 := by norm_num [G]
    rw [hv, polynomialPrepCutoff4_eq_one (by norm_num) (by norm_num),
      polynomialRowCutoff4_eq_one (by norm_num) (by norm_num), mul_one]
  · rw [auxScore, first_row_rank]
    have hv : G 0 1 / 1 = 8 := by norm_num [G]
    rw [hv]
    exact polynomialAuxCutoff4_eq_one (by norm_num) (by norm_num) (by norm_num)

-- The analytic constant cannot be zero: the fourth root changes from zero to one over width 8.
example : ∃ C : ℝ, 1 / 8 ≤ C ∧ ∀ v r v' r',
    |polynomialWitnessCutoff4 1000 v r ^ (4⁻¹ : ℝ) -
      polynomialWitnessCutoff4 1000 v' r' ^ (4⁻¹ : ℝ)| ≤ C * (|v - v'| + |r - r'|) := by
  obtain ⟨C, _, hC⟩ := exists_abs_polynomialWitnessCutoff4_root_sub_le 1000
  have h := hC 90 0 82 0
  rw [polynomialWitnessCutoff4_eq_one (by norm_num) (by norm_num) (by norm_num),
    polynomialWitnessCutoff4_eq_zero_of_entry_le (by norm_num) (by norm_num)] at h
  norm_num at h
  exact ⟨C, by linarith, hC⟩

end ComplexityTests.PolynomialAtomCutoffs
