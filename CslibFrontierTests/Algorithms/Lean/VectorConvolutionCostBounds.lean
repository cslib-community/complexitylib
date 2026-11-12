/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.VectorConvolution.CostBounds

/-!
# Tests for the cube counts and the explicit cost of convolution in `[r]^d`

* `card_Iic_filter_le_sum_le` at `C = (2, 1)`, `s = 2`: the vectors `(2, 0)`, `(1, 1)`, `(2, 1)`
  below `C` of size at least `2` are `3 ≤ (3 choose 0) + (3 choose 1) = 4`, both computed.
* `card_cube_sum_le_le_of_le_mul` on `[3]^4` with `δ = 1/2` and `s = 2`: the `15` small vectors,
  computed, are at most `81 exp (-1/2)`.
* `time_solveM_le` instantiated for the run of the `[3]^2` test of `VectorConvolution`.
-/

namespace CslibFrontierTests.Algorithms.Lean.VectorConvolutionCostBounds

open Finset Real Cslib Cslib.Algorithms.Lean.VectorConvolution

/-- Three vectors below `(2, 1)` have size at least `2`. -/
example : #((Iic (![2, 1] : Fin 2 → ℕ)).filter fun y => 2 ≤ ∑ i, y i) = 3 := by decide

/-- The bound is `∑_{j ≤ 1} (3 choose j) = 4`. -/
example : #((Iic (![2, 1] : Fin 2 → ℕ)).filter fun y => 2 ≤ ∑ i, y i) ≤ 4 :=
  (card_Iic_filter_le_sum_le _ 2).trans (by decide)

/-- `15` vectors of `[3]^4` have size at most `2`. -/
theorem card_small : #((Fintype.piFinset fun _ : Fin 4 => range 3).filter
    fun x => ∑ i, x i ≤ 2) = 15 := by decide

/-- The Chernoff bound at `δ = 1/2`: `15 ≤ 81 exp (-1/2)`. -/
example : (15 : ℝ) ≤ 81 * exp (-(1 / 2)) := by
  have h := card_cube_sum_le_le_of_le_mul (ι := Fin 4) (r := 3) (s := 2) (by norm_num)
    (δ := 1 / 2) (by norm_num) (by norm_num)
  rw [card_small] at h
  norm_num at h ⊢
  exact h

/-- The explicit cost bound applies to the queries of size `2` in `[3]^2` with `s = 1`, `ε = 1`. -/
example (f g : (Fin 2 → ℕ) → ℤ) :
    ((solveM (List.finRange 2) 3 1 f g [![2, 0], ![1, 1], ![0, 2]]).time : ℝ) ≤
      3 * (3 * 2 + 1) * (3 ^ 2 * exp (-2 * 1 ^ 2 / (2 * (3 - 1) ^ 2)) +
        3 * ∑ j ∈ range (2 - 1 + 1), ((2 : ℕ).choose j : ℝ)) := by
  have h := time_solveM_le (List.nodup_finRange 2) List.mem_finRange (r := 3) (s := 1) (t := 2)
    (by norm_num) (ε := 1) (by norm_num) (by norm_num) f g
    (Cs := [![2, 0], ![1, 1], ![0, 2]]) (by decide)
  norm_num at h ⊢
  exact h

end CslibFrontierTests.Algorithms.Lean.VectorConvolutionCostBounds
