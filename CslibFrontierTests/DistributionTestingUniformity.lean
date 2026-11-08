/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PropertyTesting.Distribution.UniformityCollision
import CslibFrontier.Computability.PropertyTesting.Distribution.UniformityLowerBound

/-! Concrete instances of the collision moments, the collision tester and Paninski's lower bound
for uniformity testing. -/

namespace ComplexityTests.DistributionTestingUniformity

open Cslib.Probability.PMF Cslib.DistributionTesting

-- The collision count of concrete sample tuples: three of the six pairs of `0, 1, 0, 0` collide.
example : collisionCount (![0, 1, 0, 0] : Fin 4 → Fin 2) = 3 := by decide

example : collisionCount (![0, 1, 2] : Fin 3 → Fin 3) = 0 := by decide

-- Exact mean for a point mass: every pair of the `3` samples collides.
example : ∑ x : Fin 3 → Bool, (iid (PMF.pure true) 3 x).toReal * collisionCount x = 3 := by
  rw [sum_iid_mul_collisionCount, collisionProbability_eq_sum]
  simp [Nat.choose]

-- Exact mean and variance for two fair coins: the collision count is a fair Bernoulli variable.
example : ∑ x : Fin 2 → Bool, (iid (uniformOfFintype Bool) 2 x).toReal * collisionCount x =
    1 / 2 := by
  rw [sum_iid_mul_collisionCount, collisionProbability_uniform]
  simp

example : ∑ x : Fin 2 → Bool, (iid (uniformOfFintype Bool) 2 x).toReal *
    ((collisionCount x : ℝ) - (2 : ℕ).choose 2 * collisionProbability (uniformOfFintype Bool)) ^ 2 =
      1 / 4 := by
  rw [sum_iid_mul_collisionCount_sub_sq, collisionProbability_uniform]
  simp only [Fintype.sum_bool, uniformOfFintype_apply, Fintype.card_bool]
  norm_num

-- The sample-size hypothesis of the collision tester is satisfiable: `n = 4`, `ε = 1 / 2`,
-- `k = 321` meets `40 √n ≤ (k - 1) ε²` with equality.
theorem isTester_collisionTester_fin_four :
    IsTester (collisionTester (α := Fin 4) 321 (1 / 2)) {uniformOfFintype (Fin 4)} (1 / 2) :=
  isTester_collisionTester (by norm_num) (by
    rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num)

-- The soundness promise is not vacuous: a point mass is at distance `3 / 4` from uniform on
-- `Fin 4`, so the tester rejects it with probability at least `2 / 3`.
example : dist (PMF.pure (0 : Fin 4)) (uniformOfFintype (Fin 4)) = 3 / 4 := by
  rw [dist_eq, Fin.sum_univ_four]
  simp only [PMF.pure_apply, uniformOfFintype_apply, Fintype.card_fin]
  norm_num

example : acceptProb (collisionTester (α := Fin 4) 321 (1 / 2)) (PMF.pure 0) ≤ 1 / 3 := by
  refine isTester_collisionTester_fin_four.reject _ fun q hq => ?_
  rw [Set.mem_singleton_iff] at hq
  rw [hq, dist_eq, Fin.sum_univ_four]
  simp only [PMF.pure_apply, uniformOfFintype_apply, Fintype.card_fin]
  norm_num

-- At bias `ε = 1`, Paninski's distribution vanishes off the sign vector: it is uniform on half of
-- the domain, the birthday instance.
example (σ : Fin 3 → Bool) (i : Fin 3) :
    (paninski (ε := 1) (by norm_num) σ (i, !σ i)).toReal = 0 := by
  rw [paninski_apply_toReal, paninskiWeight]
  cases σ i <;> norm_num

example (σ : Fin 3 → Bool) :
    dist (paninski (ε := 1 / 2) (by norm_num [abs_of_pos]) σ) (uniformOfFintype (Fin 3 × Bool)) =
      1 / 4 := by
  rw [dist_paninski_uniform, abs_of_pos (by norm_num)]
  norm_num

-- The birthday bound: no single-sample tester distinguishes uniform on `Fin 4` from distributions
-- at distance `1 / 2`.
example (T : (Fin 1 → Fin 4) → PMF Bool) : ¬ IsTester T {uniformOfFintype (Fin 4)} (1 / 2) := by
  intro hT
  have h := four_mul_card_le_of_isTester_uniform ⟨2, by simp⟩ hT
  simp at h

-- No tester has proximity `0`, at any sample size.
example (k : ℕ) (T : (Fin k → Fin 4) → PMF Bool) : ¬ IsTester T {uniformOfFintype (Fin 4)} 0 := by
  intro hT
  have h := card_le_of_isTester_uniform ⟨2, by simp⟩ hT (by norm_num)
  norm_num at h

end ComplexityTests.DistributionTestingUniformity
