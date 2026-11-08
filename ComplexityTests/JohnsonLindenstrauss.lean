/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.BitString.Rademacher
public import Complexity.Probability.JohnsonLindenstrauss
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Unit tests for the Johnson–Lindenstrauss lemma

Verifies non-vacuity and concrete behavior of:
1. the Rademacher moments of `Cslib.BitString.expect_sq_sum_mul_signVal` and
   `Cslib.BitString.expect_sum_mul_signVal_pow_four` on a two-coordinate sum;
2. `Cslib.Probability.signProjection` on explicit seeds: a seed whose projection doubles a squared
   norm (so the failure event of `Cslib.Probability.dens_lt_norm_signProjection_sq_le` is
   nonempty) and a seed that preserves it;
3. the per-vector bound `Cslib.Probability.dens_lt_abs_norm_signProjection_sq_sub_le` at explicit
   parameters, and the hypotheses of
   `Cslib.Probability.one_sub_rpow_le_dens_forall_norm_signProjection_sq_mem_Icc` and
   `Cslib.Probability.exists_linearMap_forall_norm_sq_mem_Icc`, which are satisfiable with explicit
   parameters for two points, and the trivial case `n = 1`, `k = 0`.
-/

public section

namespace ComplexityTests.JohnsonLindenstrauss

open Cslib Cslib.BitString Cslib.Probability Real
open scoped BigOperators

/-! ## 1. Rademacher moments -/

/-- The sum `x₀ + 2 x₁` of two independent signs has second moment `1 + 4 = 5`. -/
example : 𝔼 x : Fin 2 → Bool, (∑ i, ![1, 2] i * signVal (x i)) ^ 2 = 5 := by
  rw [expect_sq_sum_mul_signVal]
  norm_num [Fin.sum_univ_two]

/-- The same sum has fourth moment `3 · 5² - 2 (1 + 16) = 41`. -/
example : 𝔼 x : Fin 2 → Bool, (∑ i, ![1, 2] i * signVal (x i)) ^ 4 = 41 := by
  rw [expect_sum_mul_signVal_pow_four]
  norm_num [Fin.sum_univ_two]

/-! ## 2. Explicit seeds -/

/-- The vector `(1, 1)` with squared norm `2`. -/
noncomputable abbrev x₁₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1]

theorem norm_x₁₁_sq : ‖x₁₁‖ ^ 2 = 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [Fin.sum_univ_two]

/-- A single all-`+1` row maps `(1, 1)` to `2`: the squared norm doubles. -/
theorem norm_signProjection_const_sq :
    ‖signProjection (fun (_ : Fin 1) (_ : Fin 2) => false) x₁₁‖ ^ 2 = 4 := by
  rw [norm_signProjection_sq]
  norm_num [Fin.sum_univ_two]

/-- Hence the upper-tail failure event is nonempty for `k = 1` and `ε = 1/2`: the bound of
`dens_lt_norm_signProjection_sq_le` is about a genuinely random event. -/
example : (fun (_ : Fin 1) (_ : Fin 2) => false) ∈
    ({b | (1 + 1 / 2 : ℝ) * ‖x₁₁‖ ^ 2 < ‖signProjection b x₁₁‖ ^ 2} :
      Finset (Fin 1 → Fin 2 → Bool)) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [norm_x₁₁_sq, norm_signProjection_const_sq]
  norm_num

/-- Rows `(+1, +1)` and `(+1, -1)` (a scaled Hadamard matrix) preserve the norm of `(1, 1)`. -/
example : ‖signProjection (fun (j : Fin 2) (i : Fin 2) => decide (j = 1 ∧ i = 1)) x₁₁‖ ^ 2 =
    ‖x₁₁‖ ^ 2 := by
  rw [norm_signProjection_sq, norm_x₁₁_sq]
  norm_num [Fin.sum_univ_two]

/-! ## 3. The dimension bound -/

/-- The two-sided per-vector bound for `ε = 1/2` and `k = 400`: the failure probability is at most
`2 exp (-200 / 12) < 2 · 10⁻⁷`. -/
example (x : EuclideanSpace ℝ (Fin 3)) :
    (Finset.dens ({b | 1 / 2 * ‖x‖ ^ 2 < |‖signProjection b x‖ ^ 2 - ‖x‖ ^ 2|} :
      Finset (Fin 400 → Fin 3 → Bool)) : ℝ) ≤ 2 * exp (-(50 / 3)) := by
  have h := dens_lt_abs_norm_signProjection_sq_sub_le 400 x (ε := 1 / 2) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Two points, `ε = 1/2`, `β = 1`, `k = 50`: since `(4 + 2) / (1/8 - 1/24) = 72` and
`72 log 2 < 50`, all distances are preserved with probability at least `1/2`. -/
example (p : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    1 / 2 ≤ (Finset.dens ({b | ∀ i j, ‖signProjection b (p i - p j)‖ ^ 2 ∈
      Set.Icc ((1 - 1 / 2) * ‖p i - p j‖ ^ 2) ((1 + 1 / 2) * ‖p i - p j‖ ^ 2)} :
        Finset (Fin 50 → Fin 3 → Bool)) : ℝ) := by
  have h := one_sub_rpow_le_dens_forall_norm_signProjection_sq_mem_Icc p (k := 50)
    (ε := 1 / 2) (β := 1) (by norm_num) (by norm_num) (by
      push_cast
      nlinarith [log_two_lt_d9])
  rw [Nat.cast_ofNat, rpow_neg_one] at h
  exact le_trans (by norm_num) h

/-- Two points, `ε = 1`: `24 log 2 < 17`, so a linear map into dimension `17` preserves the distance
within a factor `1 ± 1`. -/
example (p : Fin 2 → EuclideanSpace ℝ (Fin 100)) :
    ∃ f : EuclideanSpace ℝ (Fin 100) →ₗ[ℝ] EuclideanSpace ℝ (Fin 17), ∀ i j,
      ‖f (p i) - f (p j)‖ ^ 2 ∈ Set.Icc ((1 - 1) * ‖p i - p j‖ ^ 2) ((1 + 1) * ‖p i - p j‖ ^ 2) :=
  exists_linearMap_forall_norm_sq_mem_Icc p one_pos le_rfl (by
    push_cast
    nlinarith [log_two_lt_d9])

/-- A single point needs no dimensions: `log 1 = 0`, so `k = 0` is allowed. -/
example (p : Fin 1 → EuclideanSpace ℝ (Fin 5)) :
    ∃ b : Fin 0 → Fin 5 → Bool, ∀ i j, ‖signProjection b (p i - p j)‖ ^ 2 ∈
      Set.Icc ((1 - 1 / 2) * ‖p i - p j‖ ^ 2) ((1 + 1 / 2) * ‖p i - p j‖ ^ 2) :=
  exists_signProjection_forall_norm_sq_mem_Icc p (by norm_num) (by norm_num) (by simp)

end ComplexityTests.JohnsonLindenstrauss
