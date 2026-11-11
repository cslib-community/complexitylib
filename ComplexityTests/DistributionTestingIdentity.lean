/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PropertyTesting.Distribution.IdentityReduction

/-! Concrete instances of Goldreich's reduction from identity testing to uniformity testing. -/

namespace ComplexityTests.DistributionTestingIdentity

open Cslib.Probability.PMF Cslib.DistributionTesting

/-- A two-point distribution with masses `1 / 3` and `2 / 3`. -/
noncomputable def third : PMF Bool :=
  PMF.ofFintype (fun b => if b then 2 / 3 else 1 / 3) (by
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
    rw [ENNReal.div_add_div_same, show (2 : ENNReal) + 1 = 3 by norm_num]
    exact ENNReal.div_self (by norm_num) (by norm_num))

theorem third_true_toReal : (third true).toReal = 2 / 3 := by
  simp only [third, PMF.ofFintype_apply, ↓reduceIte]
  rw [ENNReal.toReal_div]
  norm_num

theorem third_false_toReal : (third false).toReal = 1 / 3 := by
  simp only [third, PMF.ofFintype_apply, ↓reduceIte, Bool.false_eq_true]
  rw [ENNReal.toReal_div]
  norm_num

-- On `Bool` (`n = 2`), `third` has grains `⌊4 / 3⌋ = 1` and `⌊8 / 3⌋ = 2`, so blocks of `3` and `4`
-- cells and a leftover block of `4 - 3 = 1` cell: `8 = 4 n` cells in all.
example : identityGrain third false = 1 := by
  rw [identityGrain, third_false_toReal, Fintype.card_bool, Nat.floor_eq_iff (by norm_num)]
  norm_num

example : identityGrain third true = 2 := by
  rw [identityGrain, third_true_toReal, Fintype.card_bool, Nat.floor_eq_iff (by norm_num)]
  norm_num

example : identityBlock third none = 1 := by
  have h0 : identityGrain third false = 1 := by
    rw [identityGrain, third_false_toReal, Fintype.card_bool, Nat.floor_eq_iff (by norm_num)]
    norm_num
  have h1 : identityGrain third true = 2 := by
    rw [identityGrain, third_true_toReal, Fintype.card_bool, Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [identityBlock_none, Fintype.sum_bool, h0, h1, Fintype.card_bool]
  norm_num

example : Fintype.card (IdentityDomain third) = 8 := by
  rw [card_identityDomain, Fintype.card_bool]

-- For a point mass on `Fin 4` the leftover block is empty: the grain of `0` is `⌊8⌋ = 8`.
example : identityBlock (PMF.pure (0 : Fin 4)) none = 0 := by
  rw [identityBlock_none]
  simp [identityGrain, Fin.sum_univ_four, PMF.pure_apply]
  norm_num

-- The kernel maps the target to the uniform distribution on its cells, even with an empty
-- leftover block.
example : (PMF.pure (0 : Fin 4)).bind (identityKernel (PMF.pure 0)) =
    uniformOfFintype (IdentityDomain (PMF.pure (0 : Fin 4))) :=
  bind_identityKernel_self _

-- The sample-size hypothesis is satisfiable: `n = 4`, `ε = 1 / 2`, `k = 5761` meets
-- `720 √n ≤ (k - 1) ε²` with equality.
theorem isTester_identityTester_pure :
    IsTester (identityTester (PMF.pure (0 : Fin 4)) 5761 (1 / 2)) {PMF.pure 0} (1 / 2) :=
  isTester_identityTester _ (by norm_num) (by
    rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num)

-- The soundness promise is not vacuous: the uniform distribution is at distance `3 / 4` from the
-- point mass, so the identity tester accepts it with probability at most `1 / 3`.
example : acceptProb (identityTester (PMF.pure (0 : Fin 4)) 5761 (1 / 2)) (uniformOfFintype _) ≤
    1 / 3 := by
  refine isTester_identityTester_pure.reject _ fun q hq => ?_
  rw [Set.mem_singleton_iff] at hq
  rw [hq, dist_eq, Fin.sum_univ_four]
  simp only [PMF.pure_apply, uniformOfFintype_apply, Fintype.card_fin]
  norm_num

end ComplexityTests.DistributionTestingIdentity
