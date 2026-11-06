/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.RegressionEquality
import all Complexity.Computability.Complexity.Problems.RegressionEquality
import Mathlib.Tactic

/-! Actual equality-target OLS, binary encoding, and reduction edge cases. -/

open Cslib.LeastSquares.EqualityDeletion Cslib.Complexity Turing.MultiTapeTM
open scoped List

namespace RegressionEquality

-- The source construction is actually computed, including all observations and budget.
example : expand (fromSubsetSum ([2, 3, 9], 5)) =
    ([(false, 0), (true, 2), (true, 3), (true, 9), (true, -5), (true, 0)], 2) := by
  decide +kernel

-- Actual inverse-matrix equality, with a positive Gram determinant.
example : ExactFit (data [2, 3, -5, 0]) :=
  (exactFit_data_iff _).mpr ⟨by simp, by norm_num⟩

-- Equality differs from a sign-only target: a strictly negative sum is rejected.
example : ¬ ExactFit (data [2, -5, 0]) := by
  rw [exactFit_data_iff]
  norm_num

-- A zero response by itself does not produce a nonsingular two-column fit.
example : ¬ ExactFit [(1, 0)] := by
  exact not_exactFit_ones [0]

-- The sole regressor-zero observation cannot be discarded, regardless of responses.
example (l : List ℤ) : ¬ ExactFit (l.map fun z : ℤ => ((1 : ℚ), (z : ℚ))) :=
  not_exactFit_ones l

example : expand (fromSubsetSum ([2, 3, 9], 5)) ∈ BinaryProblem := by
  rw [reduction_mem_iff, mem_SubsetSum_iff_sublist]
  exact ⟨[2, 3], by decide, by norm_num⟩

example : expand (fromSubsetSum ([2, 4], 3)) ∉ BinaryProblem := by
  rw [reduction_mem_iff, mem_SubsetSum_iff_sublist]
  rintro ⟨s, hs, hz⟩
  have hmem := List.mem_sublists.mpr hs
  have hcases : s = [] ∨ s = [2] ∨ s = [4] ∨ s = [2, 4] := by
    simpa [List.sublists, or_assoc, or_comm, or_left_comm] using hmem
  rcases hcases with rfl | rfl | rfl | rfl <;> norm_num at hz

-- Zero entries are removed without changing the source problem.
example : expand (fromSubsetSum ([0, 0, 2, 0], 2)) ∈ BinaryProblem := by
  rw [reduction_mem_iff, mem_SubsetSum_iff_sublist]
  exact ⟨[2], by decide, rfl⟩

example : expand (fromSubsetSum ([], 0)) ∈ BinaryProblem := by
  rw [reduction_mem_iff, mem_SubsetSum_iff_sublist]
  exact ⟨[], by simp, rfl⟩

example : expand (fromSubsetSum ([], 1)) ∉ BinaryProblem := by
  rw [reduction_mem_iff, mem_SubsetSum_iff_sublist]
  simp

example : expand (fromSubsetSum ([0, 0], 1)) ∉ BinaryProblem := by
  rw [reduction_mem_iff, mem_SubsetSum_iff_sublist]
  rintro ⟨s, hs, hz⟩
  have hmem := List.mem_sublists.mpr hs
  have hcases : s = [] ∨ s = [0] ∨ s = [0, 0] := by
    simpa [List.sublists, or_assoc, or_comm, or_left_comm] using hmem
  rcases hcases with rfl | rfl | rfl <;> norm_num at hz

-- Repetitions are distinct selectable observations, not a set of numerical values.
example : expand (fromSubsetSum ([2, 2], 4)) ∈ BinaryProblem := by
  rw [reduction_mem_iff, mem_SubsetSum_iff_sublist]
  exact ⟨[2, 2], List.Sublist.refl _, rfl⟩

example : NPHard binaryEncoding BinaryProblem := binary_npHard

example : ComputableInPolyTime (fun a => expand (fromSubsetSum a))
    (encPair (encList encNat) encNat) binaryEncoding := computableInPolyTime_reduction

end RegressionEquality
