/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric.Slices

/-! # Conditional integration with unequal and empty slices

The four endpoint slices have densities `2/3`, `1`, `0`, and `1/3`. The error is nonconstant
and correlated with retention. Scaling it by one half contracts its fourth moment by `1/16`,
with the same sharp contraction after integration.
-/

public section

open Finset
open scoped BigOperators

namespace RootMetricSlicesTests

/-- One source is always present; the other is present only in environment zero. -/
abbrev source (σ : Fin 3) (x : Bool) : Prop := x = false ∨ σ = 0
/-- One endpoint is always present; the other excludes environment zero. -/
abbrev target (σ : Fin 3) (y : Bool) : Prop := y = true ∨ σ ≠ 0

/-- A sample that varies across the three environments. -/
def input (σ : Fin 3) (_x _y : Bool) : ℝ := σ.val + 1

/-- The same sample scaled by one half. -/
noncomputable def error (σ : Fin 3) (x y : Bool) : ℝ := input σ x y / 2

example : ({σ | source σ true ∧ target σ false} : Finset (Fin 3)) = ∅ := by
  ext σ
  simp [source, target]

/-- Nonconstant retained-pair input moment. -/
theorem input_moment : Cslib.rowNormPow 4 1 1 source target input = 196 / 3 := by
  norm_num [Cslib.rowNormPow, expect_eq_sum_div_card, Fin.sum_univ_succ,
    Fintype.sum_bool, sum_filter, filter_insert, filter_singleton, source, target, input]

/-- The output moment is exactly one sixteenth of the input, despite unequal slice sizes. -/
theorem error_moment : Cslib.rowNormPow 4 1 1 source target error = 49 / 12 := by
  norm_num [Cslib.rowNormPow, expect_eq_sum_div_card, Fin.sum_univ_succ,
    Fintype.sum_bool, sum_filter, filter_insert, filter_singleton, source, target, error, input]

/-- A conditional estimate integrates without any reciprocal-density loss. -/
theorem integrated_contraction : Cslib.rowNormPow 4 1 1 source target error ≤
    (1 / 16) * Cslib.rowNormPow 4 1 1 source target input := by
  apply Cslib.rowNormPow_le_of_conditional_expect_le (by norm_num)
  intro x y
  have hpoint (σ : Fin 3) : |error σ x y| ^ 4 = (1 / 16 : ℝ) * |input σ x y| ^ 4 := by
    norm_num [error, abs_div, div_pow]
    ring
  simp_rw [hpoint]
  rw [← mul_expect]


/-- The exact decomposition also applies without nonempty-slice assumptions. -/
example : Cslib.rowNormPow 4 1 1 source target input =
    (1 * (1 : ℝ))⁻¹ * ∑ x, ∑ y,
      (({σ | source σ x ∧ target σ y} : Finset (Fin 3)).dens : ℝ) *
        𝔼 σ ∈ ({σ | source σ x ∧ target σ y} : Finset (Fin 3)), |input σ x y| ^ 4 :=
  Cslib.rowNormPow_eq_sum_dens_mul_expect input

end RootMetricSlicesTests
