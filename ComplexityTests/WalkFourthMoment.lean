/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Foundations.Combinatorics.Expander.AffinePlane
import Complexity.Foundations.Combinatorics.Expander.FourthMoment
import Mathlib.Algebra.Field.ZMod

/-!
# Fourth moments of the random walk

Jensen's inequality for the walk on a concrete function, where it is strict, and the
fourth-moment decay on the affine-plane expander over `𝔽₅`: two steps shrink the fourth moment of
every function of expectation zero by at least the factor `2 / 5`.
-/

namespace ComplexityTests.WalkFourthMoment

open Cslib Cslib.RotationMap Finset
open scoped BigOperators

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

-- One step of the affine-plane walk on `𝔽₃ × 𝔽₃` from `(0, 0)` averages `f` over the line
-- `{(c, 0)}`; for the indicator of `(1, 0)` this is `1 / 3`, and `(1 / 3) ^ 2 < 1 / 3`.
example : (affinePlane (ZMod 3)).walk (fun p ↦ if p = (1, 0) then (1 : ℝ) else 0) (0, 0) ^ 2 ≤
    (affinePlane (ZMod 3)).walk (fun p ↦ (if p = (1, 0) then (1 : ℝ) else 0) ^ 2) (0, 0) :=
  sq_walk_le _ _ _

private theorem walk_indicator :
    (affinePlane (ZMod 3)).walk (fun p ↦ if p = (1, 0) then (1 : ℝ) else 0) (0, 0) = 1 / 3 := by
  rw [walk_affinePlane, Fintype.expect_eq_sum_div_card]
  simp [ZMod.card]

-- Here Jensen's inequality is strict.
example : (affinePlane (ZMod 3)).walk (fun p ↦ if p = (1, 0) then (1 : ℝ) else 0) (0, 0) ^ 2 <
    (affinePlane (ZMod 3)).walk (fun p ↦ (if p = (1, 0) then (1 : ℝ) else 0) ^ 2) (0, 0) := by
  have h : (fun p : ZMod 3 × ZMod 3 ↦ (if p = (1, 0) then (1 : ℝ) else 0) ^ 2) =
      fun p ↦ if p = (1, 0) then (1 : ℝ) else 0 := funext fun p ↦ by split_ifs <;> norm_num
  rw [h, walk_indicator]
  norm_num

-- Two steps of the affine-plane walk over `𝔽₅` shrink fourth moments by the factor `2 / 5`.
example (f : ZMod 5 × ZMod 5 → ℝ) (hf : 𝔼 v, f v = 0) :
    𝔼 v, ((affinePlane (ZMod 5)).walk ^ 2) f v ^ 4 ≤ 2 * (1 / 5) * 𝔼 v, f v ^ 4 := by
  have h := (affinePlane (ZMod 5)).expect_walk_pow_two_mul_pow_four_le hf 1
  have hl := spectralExpansion_affinePlane_le (ZMod 5)
  have hl₀ := (affinePlane (ZMod 5)).spectralExpansion_nonneg
  have hsq : (affinePlane (ZMod 5)).spectralExpansion ^ (2 * 1) ≤ 1 / 5 := by
    calc _ ≤ Real.sqrt (1 / Fintype.card (ZMod 5)) ^ 2 := by
          rw [mul_one]
          exact pow_le_pow_left₀ hl₀ hl 2
      _ = 1 / 5 := by
          rw [Real.sq_sqrt (by positivity), ZMod.card]
          norm_num
  have h4 : 0 ≤ 𝔼 v, f v ^ 4 := expect_nonneg fun v _ ↦ by positivity
  rw [mul_one] at h
  nlinarith

end ComplexityTests.WalkFourthMoment
