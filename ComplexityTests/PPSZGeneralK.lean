/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.GeneralK
import ComplexityTests.PPSZUnique
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-! PPSZ for unique k-SAT in the limit, for general `k`: the constant `μ_3` agrees with the
`k = 3` module, `μ_4 / 3` lies between `0.35` and `π² / 18 < 0.55` and is below `μ_3 / 2`, sample
values of `R` and `S`, the general headline recovers the `k = 3` headline, and the headline applied
to the uniquely satisfiable 3-CNF formula of `ComplexityTests.PPSZUnique` for `k = 3` and `k = 4`.
-/

namespace ComplexityTests.PPSZGeneralK

open Cslib.Logic.PL Cslib.Complexity.PPSZ

/-! ### The constant `μ_k` -/

/-- The savings for `k = 3` are `μ_3 / 2 = 2 - 2 log 2`, the integral of `Limit.lean`. -/
example : mu 3 / ((3 : ℝ) - 1) = 2 - 2 * Real.log 2 := by
  rw [mu_three]
  ring

/-- `μ_2 = ∑_{j ≥ 1} 1 / (j (j + 1)) = 1`: the sum telescopes. -/
example : mu 2 = 1 := by
  have h : HasSum (fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1 / ((2 : ℕ) - 1)))) 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity)]
    have hs : ∀ n : ℕ, ∑ j ∈ Finset.range n,
        1 / (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1 / ((2 : ℕ) - 1))) = 1 - 1 / ((n : ℝ) + 1) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        field_simp
        ring
    simp_rw [hs]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
  exact h.tsum_eq

/-- For `k = 2` the recursion is `x ↦ r + (1 - r) x`, whose only fixed point is `1` for
`r ∈ (0, 1]`. -/
example {r : ℝ} (hr : r ∈ Set.Ioc (0 : ℝ) 1) : R 2 r = 1 := by
  have h := R_eq (k := 2) (Set.Ioc_subset_Icc_self hr)
  norm_num at h
  nlinarith [hr.1]

/-- `∑_{j ≥ 1} 1 / (j (j + 1 / 3)) ≥ 3 / 4 + 3 / 14 + 1 / 10`, so `μ_4 / 3 > 0.35`. -/
example : 0.35 < mu 4 / ((4 : ℝ) - 1) := by
  have h := (summable_mu (k := 4) (by norm_num)).sum_le_tsum (Finset.range 3)
    fun j _ => by positivity
  rw [← mu] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- `1 / (j (j + 1 / 3)) ≤ 1 / j²`, so `μ_4 ≤ π² / 6`. -/
theorem mu_four_le : mu 4 ≤ Real.pi ^ 2 / 6 := by
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using h
  rw [← hz.tsum_eq, mu]
  refine (summable_mu (k := 4) (by norm_num)).tsum_le_tsum (fun j => ?_) hz.summable
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  refine one_div_le_one_div_of_le (by positivity) ?_
  norm_num
  nlinarith

example : mu 4 / ((4 : ℝ) - 1) < 0.55 := by
  have hpi : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have := mu_four_le
  norm_num
  linarith

/-- The savings decrease from `k = 3` to `k = 4`: `μ_4 / 3 ≤ π² / 18 < 2 - 2 log 2 = μ_3 / 2`. -/
example : mu 4 / ((4 : ℝ) - 1) < mu 3 / ((3 : ℝ) - 1) := by
  have := mu_four_le
  rw [mu_three]
  nlinarith [Real.pi_lt_d4, Real.pi_pos, Real.log_two_lt_d9]

/-! ### The limit `R` and its inverse `S` -/

example : R 3 (1 / 3) = 1 / 4 := by
  rw [R_three ⟨by norm_num, by norm_num⟩]
  norm_num [R3]

/-- `R 4 = 1` on `[2 / 3, 1]`. -/
example : R 4 (3 / 4) = 1 := R_eq_one (by norm_num) (by norm_num) (by norm_num)

/-- `R 4 (S 4 t) = t` for `t ∈ [0, 1)`. -/
example : R 4 (S 4 (1 / 2)) = 1 / 2 := R_S (by norm_num) ⟨by norm_num, by norm_num⟩

example : S 4 0 = 0 := by
  rw [S, Real.zero_rpow (by norm_num)]
  norm_num

/-- `μ_k / (k - 1)` bounds every finite-depth average: `qbar 3 2 = 31 / 70 ≤ μ_3 / 2`. -/
example : (31 / 70 : ℝ) ≤ mu 3 / (((3 : ℕ) : ℝ) - 1) := by
  rw [← qbar_three_two]
  exact qbar_le_mu_div (by norm_num) 2

/-! ### The headline -/

/-- The general headline for `k = 3` is the headline of `Limit.lean`. -/
example : ∀ ε > 0, ∃ w : ℕ, ∀ (n : ℕ) (φ : CNF (Fin n)) (σ : Fin n → Bool), φ.eval σ = true →
    (∀ τ, φ.eval τ = true → τ = σ) → (∀ c ∈ φ, c.length ≤ 3) →
    (2 : ℝ) ^ (-((2 * Real.log 2 - 1 + ε) * n)) ≤ ((round φ w) fun x => some (σ x)).toReal := by
  have h := round_success_unique_limit (k := 3) (by norm_num)
  rw [show (1 : ℝ) - mu 3 / (((3 : ℕ) : ℝ) - 1) = 2 * Real.log 2 - 1 by
    rw [mu_three]
    push_cast
    ring] at h
  exact h

/-- For `k = 3` and `ε = 1 / 100`, some `w` makes one round succeed on the formula `φ` of
`ComplexityTests.PPSZUnique`. -/
example : ∃ w : ℕ, (2 : ℝ) ^ (-((1 - mu 3 / (((3 : ℕ) : ℝ) - 1) + 1 / 100) * 3)) ≤
    ((round PPSZUnique.φ w) fun _ => some true).toReal := by
  obtain ⟨w, hw⟩ := round_success_unique_limit (k := 3) (by norm_num) (1 / 100) (by norm_num)
  refine ⟨w, ?_⟩
  exact_mod_cast hw 3 PPSZUnique.φ (fun _ => true) PPSZUnique.φ_sat PPSZUnique.φ_unique
    PPSZUnique.φ_len

/-- A 3-CNF formula is a 4-CNF formula, so the `k = 4` headline applies to `φ` as well. -/
example : ∃ w : ℕ, (2 : ℝ) ^ (-((1 - mu 4 / (((4 : ℕ) : ℝ) - 1) + 1 / 100) * 3)) ≤
    ((round PPSZUnique.φ w) fun _ => some true).toReal := by
  obtain ⟨w, hw⟩ := round_success_unique_limit (k := 4) (by norm_num) (1 / 100) (by norm_num)
  refine ⟨w, ?_⟩
  exact_mod_cast hw 3 PPSZUnique.φ (fun _ => true) PPSZUnique.φ_sat PPSZUnique.φ_unique
    fun c hc => (PPSZUnique.φ_len c hc).trans (by norm_num)

end ComplexityTests.PPSZGeneralK
