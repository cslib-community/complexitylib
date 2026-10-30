/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Probability.PairwiseIndependentHash.HierarchyChannels
import Mathlib.Tactic.FinCases

/-!
# Tests for the hierarchy with affine channels on radix identifiers
-/

namespace ComplexityTests.HierarchyChannels

open Finset Matrix Cslib.Probability

/-- A walk on three time layers: from `0` to `1` and from `1` to `2`, each with probability
`1 / 2`. -/
private noncomputable def C : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

private theorem hC : C.IsStrictUpperTriangular := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [C]

private theorem hC0 : ∀ x y, 0 ≤ C x y := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem hC1 : C *ᵥ 1 ≤ 1 := by
  intro x; fin_cases x <;> norm_num [C, mulVec, dotProduct, Fin.sum_univ_three]

/-- The probability of reaching layer `2`: `1 / 4`, `1 / 2`, `1`. -/
private noncomputable def p : Fin 3 → ℝ := ![1 / 4, 1 / 2, 1]

/-- The final-success reward: one at layer `2`. -/
private noncomputable def e₀ : Fin 3 → ℝ := ![0, 0, 1]

private theorem hp : (1 - C) *ᵥ p = e₀ := by
  ext i; fin_cases i <;> norm_num [C, p, e₀, mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.sub_apply, one_apply]

private theorem hp0 : 0 ≤ p := by intro i; fin_cases i <;> norm_num [p]

private theorem hp1 : p ≤ 1 := by intro i; fin_cases i <;> norm_num [p]

-- Parameters exist for `q = 2 ^ 2` and the affine channel constants.
example : Nonempty (HierarchyParams (2 ^ (1 + 1)) 1 (2 ^ (1 + 1)) (2 ^ (1 + 1)) 4) :=
  HierarchyParams.nonempty (by norm_num) one_pos

/-- The transported reward of stage `l` at the all-primary copy of layer `0`, for the walk with
radix identifiers and the affine stage channels. -/
private noncomputable def W (P : HierarchyParams (2 ^ (1 + 1)) 1 (2 ^ (1 + 1)) (2 ^ (1 + 1)) 4)
    (l : ℕ) : ℝ :=
  let X := stageChannel (1 + 1) (fun l => 3 * (P.m + 1) ^ l)
    (V := fun l => Fin (3 * (P.m + 1) ^ l)) fun _ v => v.val
  (rewardTransport (hierarchyProj P (radixCopyEquiv 3 P.m) X X C)
    (hierarchyCorrection P (radixCopyEquiv 3 P.m) X X C) l *ᵥ e₀)
    (primaryCopy P (V := fun l => Fin (3 * (P.m + 1) ^ l)) (radixCopyEquiv 3 P.m) 0 l)

-- The hierarchy approximates the acceptance probability `1 / 4` from below, within `3 · 2^(-l)`.
private theorem W_bound (P : HierarchyParams (2 ^ (1 + 1)) 1 (2 ^ (1 + 1)) (2 ^ (1 + 1)) 4)
    (l : ℕ) : 0 ≤ 1 / 4 - W P l ∧ 1 / 4 - W P l ≤ 3 * ((2 : ℝ) ^ 1)⁻¹ ^ l := by
  have h := sub_hierarchyReward_le_radix (c := 1) (n := 3) P (S := C) hC hC0 hC1 hp hp0 hp1 0 l
  simpa [W, p] using h

-- From stage `5` on the reward is positive, so acceptance is detected.
example (P : HierarchyParams (2 ^ (1 + 1)) 1 (2 ^ (1 + 1)) (2 ^ (1 + 1)) 4) : 0 < W P 5 := by
  have := (W_bound P 5).2
  norm_num at this ⊢
  linarith

end ComplexityTests.HierarchyChannels
