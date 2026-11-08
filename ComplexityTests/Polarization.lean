/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.StatisticalDistance.Polarization

/-! # Polarization of statistical distance

Checked instances of the XOR Lemma, the direct-product lower bound and the Polarization Lemma on
Boolean distributions: a uniform bit against a point mass, two disjoint point masses, the failure
of the XOR identity at `k = 0`, and the constant thresholds `α = 2/3`, `β = 1/3`.
-/

namespace ComplexityTests.Polarization

open Cslib.Probability.PMF
open scoped Cslib.Probability.PMF

/-- A uniform bit. -/
noncomputable def U : PMF Bool := Cslib.Probability.PMF.uniformOfFintype Bool

/-- A uniform bit and a point mass are at distance `1/2`. -/
theorem dist_U_pure : dist U (PMF.pure true) = 1 / 2 := by
  rw [dist_eq]
  simp [U, Cslib.Probability.PMF.uniformOfFintype_apply]
  norm_num

/-- Disjoint point masses are at distance `1`. -/
theorem dist_pure_false_true : dist (PMF.pure false) (PMF.pure true) = 1 :=
  dist_eq_one_of_disjoint_support (by simp [PMF.support_pure])

-- XOR Lemma: three coordinates cube the distance `1/2`.
example : dist (xorMix U (PMF.pure true) 3 false) (xorMix U (PMF.pure true) 3 true) = 1 / 8 := by
  rw [dist_xorMix _ _ (by norm_num), dist_U_pure]
  norm_num

-- XOR Lemma: disjoint inputs stay at distance `1`.
example (k : ℕ) (hk : k ≠ 0) :
    dist (xorMix (PMF.pure false) (PMF.pure true) k false)
      (xorMix (PMF.pure false) (PMF.pure true) k true) = 1 := by
  rw [dist_xorMix _ _ hk, dist_pure_false_true, one_pow]

/-- A distribution on a one-point type is the point mass. -/
theorem eq_pure_of_unique {β : Type*} [Unique β] (p : PMF β) : p = PMF.pure default := by
  ext x
  rw [Subsingleton.elim x default, PMF.pure_apply_self]
  have h := p.tsum_coe
  rwa [tsum_fintype, Fintype.sum_unique] at h

-- With `k = 0` the XOR identity fails: both sides live on a one-point type, so their distance is
-- `0`, while `dist (pure false) (pure true) ^ 0 = 1`.
example : dist (xorMix (PMF.pure false) (PMF.pure true) 0 false)
    (xorMix (PMF.pure false) (PMF.pure true) 0 true) = 0 := by
  rw [eq_pure_of_unique (xorMix _ _ 0 false), eq_pure_of_unique (xorMix _ _ 0 true), dist_self]

-- Direct-product lower bound: `32` copies of a uniform bit and of a point mass are at distance at
-- least `1 - 2 exp (-4) ≥ 7/8`.
example : 7 / 8 ≤ dist (iid U 32) (iid (PMF.pure true) 32) := by
  have h := one_sub_two_mul_exp_le_dist_iid U (PMF.pure true) 32
  rw [dist_U_pure] at h
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.add_one_le_exp 1
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h4 : Real.exp (-((32 : ℕ) * (1 / 2 : ℝ) ^ 2) / 2) = Real.exp (-1) ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h4] at h
  have : Real.exp (-1) ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le he 4
  norm_num at this ⊢
  linarith

-- Polarization, upper bound: identical inputs stay at distance `0`.
example (lam ell k : ℕ) (hlam : lam ≠ 0) (hk : k ≠ 0) :
    dist (polarize U U lam ell k false) (polarize U U lam ell k true) = 0 := by
  refine le_antisymm ?_ dist_nonneg
  have h := dist_polarize_le U U lam ell k
  rwa [dist_self, zero_pow hlam, mul_zero, zero_pow hk] at h

-- The Polarization Lemma applies to the thresholds `α = 2/3`, `β = 1/3`: here `β < α² = 4/9`.
example : ∃ m b : ℕ, m ≠ 0 ∧
    Cslib.PolynomiallyBounded (fun k => m * (Nat.log 2 k + 1)) ∧
    Cslib.PolynomiallyBounded (fun k => 2 ^ (b * (Nat.log 2 k + 1))) ∧
    ∀ (p₀ p₁ : PMF Bool) (k : ℕ),
      (2 / 3 ≤ dist p₀ p₁ →
        1 - (1 / 2) ^ k ≤ dist (polarize p₀ p₁ (m * (Nat.log 2 k + 1))
          (2 ^ (b * (Nat.log 2 k + 1))) k false) (polarize p₀ p₁ (m * (Nat.log 2 k + 1))
          (2 ^ (b * (Nat.log 2 k + 1))) k true)) ∧
      (dist p₀ p₁ ≤ 1 / 3 →
        dist (polarize p₀ p₁ (m * (Nat.log 2 k + 1)) (2 ^ (b * (Nat.log 2 k + 1))) k false)
          (polarize p₀ p₁ (m * (Nat.log 2 k + 1)) (2 ^ (b * (Nat.log 2 k + 1))) k true) ≤
          (1 / 2) ^ k) := by
  obtain ⟨m, b, hm, hlam, hell, h⟩ :=
    exists_polarization (α := 2 / 3) (β := 1 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  exact ⟨m, b, hm, hlam, hell, fun p₀ p₁ k => h p₀ p₁ k⟩

-- Both branches of the Polarization Lemma are reachable: disjoint point masses are far, and a
-- distribution is near itself.
example : (2 / 3 : ℝ) ≤ dist (PMF.pure false) (PMF.pure true) ∧ dist U U ≤ (1 / 3 : ℝ) := by
  rw [dist_pure_false_true, dist_self]
  norm_num

end ComplexityTests.Polarization
