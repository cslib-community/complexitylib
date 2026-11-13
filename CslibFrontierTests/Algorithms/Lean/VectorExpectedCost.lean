/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorExpectation
import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorDimensionBound

/-!
# Finite expected-cost and dimension-bound clients

A nonempty input in the binary cube of dimension two has expected tick cost at most 161,
including the bad-element contribution. The dimension estimate also handles zero input scale.
-/

namespace CslibFrontierTests.Algorithms.Lean.VectorExpectedCost

open Finset Cslib.Algorithms.Lean.SubsetConvThreeSum

example : avgTimeOf (fun q σ => vtrialM 2 2 0 (p := q) σ) 1 2 [1, 2] [3, 5] [4, 6, 9] ≤
    161 := by
  have h := avg_time_vthreeSumM_le (r := 2) (d := 2) (s := 0) (e := 2) (μ := 1) (M := 6)
    (A := [1, 2]) (B := [3, 5]) (C := [4, 6, 9])
    (Nat.zero_le _) (by norm_num) (by norm_num) (by decide) (by decide)
    (by simp) (by simp) (by decide)
  have hv : #(balancedVecs 2 2) = 2 := by decide
  have hH : #((Fintype.piFinset fun _ : Fin 2 => range 2).filter
      fun x => ∑ i, x i ≤ 0) = 1 := by decide
  have hW : #(primeWindow 2) = 2 := by decide
  have hlog : Nat.log 2 6 = 2 := by decide
  dsimp only at h
  rw [hv, hH] at h
  norm_num [balancedSize, Finset.sum_range_succ, hW, hlog] at h
  exact h

/-- For zero input scale the least index is one, so the dimension estimate is exact. -/
example : vDim 2 0 0 = 2 := by
  have hs := (vDimIndex_spec (r := 2) (by norm_num) 0 0).1
  have hl : vDimIndex 2 0 0 ≤ 1 := by
    by_contra h
    exact vDimIndex_min (r := 2) (by norm_num) 0 0 (j := 1) (by omega) (by decide)
  have : vDimIndex 2 0 0 = 1 := by omega
  simp [vDim, this]

example : (2 : ℕ) ^ (2 * vDim 2 0 0) ≤
    2 ^ (2 * 2) * (960 * (Nat.factorial 2) ^ (vDimIndex 2 0 0 - 1) * (0 * 0) + 1) :=
  pow_two_mul_vDim_le (by norm_num) 0 0

end CslibFrontierTests.Algorithms.Lean.VectorExpectedCost
