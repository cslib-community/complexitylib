/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PropertyTesting.Distribution.ClosenessCollision

/-! Concrete instances of the cross-collision moments and the collision tester for closeness. -/

namespace ComplexityTests.DistributionTestingCloseness

open Cslib.Probability.PMF Cslib.DistributionTesting

-- Cross collisions of concrete samples: each `0` of `0, 1, 0` collides with both `0`s of `0, 0`.
example : crossCollisionCount (![0, 1, 0] : Fin 3 → Fin 2) (![0, 0] : Fin 2 → Fin 2) = 4 := by
  decide

example : crossCollisionCount (![0, 0] : Fin 2 → Fin 2) (![1, 1, 1] : Fin 3 → Fin 2) = 0 := by
  decide

-- The statistic of `0, 0` against `0, 1`: one collision within, two across, `1 + 0 - 2 / 2 = 0`.
example : closenessStatistic (![0, 0] : Fin 2 → Fin 2) ![0, 1] = 0 := by
  have h1 : collisionCount (![0, 0] : Fin 2 → Fin 2) = 1 := by decide
  have h2 : collisionCount (![0, 1] : Fin 2 → Fin 2) = 0 := by decide
  have h3 : crossCollisionCount (![0, 0] : Fin 2 → Fin 2) ![0, 1] = 2 := by decide
  rw [closenessStatistic_eq, h1, h2, h3]
  norm_num

-- Two samples of a fair coin against three samples of a constant coin share `2 · 3 · 1 / 2 = 3`
-- collisions on average.
example : ∑ x : Fin 2 → Bool, ∑ y : Fin 3 → Bool, (iid (uniformOfFintype Bool) 2 x).toReal *
    (iid (PMF.pure true) 3 y).toReal * crossCollisionCount x y = 3 := by
  rw [sum_sum_iid_mul_crossCollisionCount]
  norm_num [PMF.pure_apply]

-- Point masses on different values: the statistic of three samples each has mean
-- `C(3, 2) · ‖p - q‖₂² = 3 · 2 = 6`.
example : ∑ x : Fin 3 → Bool, ∑ y : Fin 3 → Bool, (iid (PMF.pure true) 3 x).toReal *
    (iid (PMF.pure false) 3 y).toReal * closenessStatistic x y = 6 := by
  rw [sum_sum_iid_mul_closenessStatistic]
  norm_num [PMF.pure_apply]

-- The `ℓ₂` tester uses `√b`: uniform on four points has `‖p‖₂² = 1 / 4`, so `55` samples of each
-- give acceptance probability at least `2 / 3` with `ε = 1` (here `36 · 1 / 2 = 54 · 1 / 3`).
example : 2 / 3 ≤ acceptProb₂ (closenessTester (α := Fin 4) 55 1) (uniformOfFintype (Fin 4))
    (uniformOfFintype (Fin 4)) := by
  have hcp : collisionProbability (uniformOfFintype (Fin 4)) ≤ 1 / 4 := by
    rw [collisionProbability_uniform, Fintype.card_fin]
    norm_num
  have hsqrt : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h := le_acceptProb₂_closenessTester (k := 55) (ε := 1) (δ := 1 / 3) (by norm_num) hcp hcp
    (by rw [hsqrt]; norm_num) (by simp)
  linarith

/-- The collision tester with `217` samples of each distribution is a closeness tester on `Bool`
with proximity `1 / 2` (here `27 · 2 = 216 / 4`). -/
theorem isClosenessTester_bool :
    IsClosenessTester (closenessTester (α := Bool) 217 (2 * (1 / 2) / Real.sqrt 2)) (1 / 2) := by
  have h := isClosenessTester_closenessTester (α := Bool) (k := 217) (ε := 1 / 2) (by norm_num)
    (by rw [Fintype.card_bool]; norm_num)
  simpa only [Fintype.card_bool, Nat.cast_ofNat] using h

-- Nonvacuity: it rejects two point masses on different values with probability at least `2 / 3`.
example : acceptProb₂ (closenessTester (α := Bool) 217 (2 * (1 / 2) / Real.sqrt 2))
    (PMF.pure true) (PMF.pure false) ≤ 1 / 3 := by
  refine isClosenessTester_bool.reject _ _ ?_
  rw [dist_eq]
  norm_num [PMF.pure_apply]

end ComplexityTests.DistributionTestingCloseness
