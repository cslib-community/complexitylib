/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of actual compression event assembly)

public import Complexity.Foundations.Probability.PolynomialAtomCompression
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Actual compression assembly boundary case

An empty schedule and positive rank capacity have no first overflow. The actual zero row and
one nonzero true endpoint have fourth-root discrepancy exactly one. The assembled comparison
therefore gives a nontrivial final-prefix bound, with both prefix and selected-tail sums zero.
-/

public section

namespace ComplexityTests.PolynomialAtomCompression

open Finset Cslib Cslib.RowCompression

private noncomputable def truth : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 0]]

private theorem error_eq_one :
    |PolynomialAtomRow.preparation.stateRootError 1 univ 2 ⟨0, 0⟩ ⟨0, truth⟩ 0| = 1 := by
  have hzero : PolynomialAtomRow.preparation.eval 1 0
      (firstRank univ 2 0 (0 : Fin 2 → Fin 2 → ℝ)) = 0 :=
    polynomialPrepRow4_eq_zero_of_entry_le (by norm_num) (by norm_num)
  have hrank : firstRank univ 2 0 truth = 0 := by
    norm_num [firstRank, kthLargest, truth, Fin.univ_succ, filter_insert, filter_singleton]
  have hone : PolynomialAtomRow.preparation.eval 1 (truth 0 0)
      (firstRank univ 2 0 truth) = 1 := by
    rw [hrank]
    change polynomialPrepRow4 1 1 0 = 1
    rw [polynomialPrepRow4_of_rank_le (by norm_num) (by norm_num)]
    exact polynomialPrepCutoff4_eq_one (by norm_num) (by norm_num)
  unfold PolynomialAtomRow.stateRootError
  change |PolynomialAtomRow.preparation.eval 1 0
    (firstRank univ 2 0 (0 : Fin 2 → Fin 2 → ℝ)) ^ (4⁻¹ : ℝ) -
    PolynomialAtomRow.preparation.eval 1 (truth 0 0)
      (firstRank univ 2 0 truth) ^ (4⁻¹ : ℝ)| = 1
  rw [hzero, hone, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), Real.one_rpow]
  norm_num

/-- The assembled coefficient pays for the actual unit output discrepancy at zero horizon. -/
theorem unit_error_bound : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ 1 ≤ C := by
  obtain ⟨C, hC, hscale⟩ := PolynomialAtomRow.preparation.exists_compression_root_bound
    (θ := 1) (by norm_num)
  obtain ⟨A, hA, hbound⟩ := hscale (1 / 20000) (by norm_num) (by norm_num)
  refine ⟨C, A, hC, hA, ?_⟩
  have h := hbound (univ : Finset (Fin 2)) (fun _ => 2) (fun _ => 0) ⟨0, 0⟩ truth 2 0
    (fun _ => False) (by norm_num) rfl
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun y _ => by fin_cases y <;> norm_num [truth]) (by simp)
    (fun _ => 0) (by simp) (by simp) 1 (by norm_num)
    (fun _ _ => clippedError_le_one _ _ _) (by simp) 0 (mem_univ 0)
  simpa [error_eq_one] using h

/-- The integrated theorem applies to a genuine nonzero root error, with empty event charges. -/
theorem unit_error_moment_bound : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
    rowNormPow 4 1 1 (fun (_ : Unit) (_ : Fin 2) => True) (fun _ _ => True)
      (fun _ _ y => PolynomialAtomRow.preparation.stateRootError 1 univ 2
        ⟨0, 0⟩ ⟨0, ![![1, 0], ![0, 0]]⟩ y) ≤ 512 * C ^ 4 := by
  classical
  obtain ⟨C, hC, hscale⟩ := PolynomialAtomRow.preparation.exists_compression_rowNormPow_le
    (θ := 1) (by norm_num)
  obtain ⟨A, hA, hbound⟩ := hscale (1 / 20000) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, A, hC, hA, ?_⟩
  have h := hbound (Ω := Unit) (V := Fin 2) 1 1 (by norm_num)
    (fun _ _ => True) (fun _ _ => True) (fun _ => 2) 2 0 (by norm_num) (by simp)
    (fun _ _ _ => 0) (fun _ _ => ⟨0, 0⟩) (fun _ _ => truth)
    (by simp) (fun _ _ y _ _ => by fin_cases y <;> norm_num [truth])
    (fun _ _ y _ _ => by fin_cases y <;> norm_num [truth]) (by simp)
    (fun _ _ _ => 0) (fun _ _ => 1) (by simp) (by simp) (by simp)
    (fun _ _ _ _ _ => clippedError_le_one _ _ _)
  norm_num [vertexNormPow, Fin.univ_succ, truth] at h ⊢
  nlinarith only [h]

end ComplexityTests.PolynomialAtomCompression
