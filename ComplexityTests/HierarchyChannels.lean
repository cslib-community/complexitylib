/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
import Complexity.Probability.PairwiseIndependentHash.HierarchyChannels
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the hierarchy with bounded computable affine channels on radix identifiers

Evaluation checks exercise least-prime search at the zero-identifier boundary, a composite lower
bound, and a prime lower bound. The formal examples use minimality and binary-length bounds and
verify the retained channel interface with the new computable side.
-/

namespace ComplexityTests.HierarchyChannels

open Finset Matrix Cslib.Probability

-- Both parameters execute using natural arithmetic: these checks do not evaluate a real ceiling.
/-- info: [2, 11, 17, 2, 2] -/
#guard_msgs in
#eval [stageModulus (fun _ => 0) 0, stageModulus (fun _ => 0) 3,
  stageModulus (fun _ => 17) 3, stageSide (fun _ => 0) 0, stageSide (fun _ => 5) 2]

-- A prime identifier bound above the power-of-two bound is selected exactly.
example : stageModulus (fun _ => 17) 3 = 17 := by
  apply le_antisymm (stageModulus_le_of_prime _ _ (by norm_num) (by norm_num))
  simpa using le_stageModulus (fun _ => 17) 3

private theorem modulus_five : stageModulus (fun _ => 5) 2 = 5 := by
  apply le_antisymm (stageModulus_le_of_prime _ _ (by norm_num) (by norm_num))
  simpa using le_stageModulus (fun _ => 5) 2

-- The arithmetic side agrees with the nonintegral mathematical ratio ceil(5/4).
example : stageSide (fun _ => 5) 2 = 2 ∧
    ⌈(stageModulus (fun _ => 5) 2 : ℝ) * (2⁻¹ : ℝ) ^ 2⌉₊ = 2 := by
  have h : stageSide (fun _ => 5) 2 = 2 := by
    norm_num [stageSide, modulus_five, Nat.ceilDiv_eq_add_pred_div]
  exact ⟨h, (stageSide_eq_ceil (fun _ => 5) 2).symm.trans h⟩

-- An identifier bound exponential in the stage index needs only a linear binary-length bound.
example (r l : ℕ) :
    (stageModulus (fun i => 2 ^ (r * i)) l).size ≤ max (l + 1) (r * l + 1) + 1 := by
  simpa only [Nat.size_pow] using size_stageModulus_le (fun i => 2 ^ (r * i)) l

-- At stage two, identifiers below five use modulus five and side two: the actual retention
-- density is 2/5, while the requested stage rate is 1/4. The original uniform constants apply.
example :
    let X := stageChannel 1 (fun _ => 5) (V := fun _ => Fin 5) (fun _ v => v.val) 2
    RetentionChannels X X (1 / 4) (2 / 5) 1 2 2 4 := by
  intro X
  have h := retentionChannels_stageChannel (H := 1) (M := fun _ => 5)
    (V := fun _ => Fin 5) (ident := fun _ v => v.val)
    (fun _ => Fin.val_injective) (fun _ v => v.isLt) 2
  convert h using 1 <;> norm_num [stageSide, modulus_five, Nat.ceilDiv_eq_add_pred_div]

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
