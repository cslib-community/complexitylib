/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric.Conditioning

/-! # Conditioning on one retained start

The actual retention density is `1/2`, while the nominal rate is `1/4`. All error lies at one
retained vertex, so the conditional moment bound is sharp. The tail examples cover a nonempty
bad event and the strict threshold at the error itself.
-/

open Finset
open scoped BigOperators

public section

namespace RootMetricConditioningTests

/-- Retain one vertex on one of the two environments. -/
abbrev retained (σ x : Bool) : Prop := σ = true ∧ x = true

/-- All error is concentrated at the retained vertex and environment. -/
def error (σ x : Bool) : ℝ := if retained σ x then 2 else 0

private theorem retained_event : ({σ | retained σ true} : Finset Bool) = {true} := by
  ext σ
  simp only [mem_filter, mem_univ, true_and, retained, and_true, mem_singleton]

private theorem retained_nonempty : ({σ | retained σ true} : Finset Bool).Nonempty := by
  rw [retained_event]
  exact singleton_nonempty _

/-- A sharp global moment bound with distinct nominal and actual retention rates. -/
theorem integrated_moment : Cslib.vertexNormPow 4 8 (1 / 4) retained error = 4 := by
  norm_num [Cslib.vertexNormPow, expect_eq_sum_div_card, Fintype.sum_bool,
    Finset.sum_filter, Finset.filter_insert, retained, error]

/-- The conditional moment is sixteen, exactly the global bound times the factor four. -/
theorem conditional_moment :
    (𝔼 σ ∈ ({σ | retained σ true} : Finset Bool), |error σ true| ^ 4) = 16 := by
  rw [retained_event]
  norm_num [error, retained]

/-- The new theorem applies to the concrete correlated error and retention mask. -/
theorem conditional_bound :
    (𝔼 σ ∈ ({σ | retained σ true} : Finset Bool), |error σ true| ^ 4) ≤
      8 * (1 / 4) / (({σ | retained σ true} : Finset Bool).dens : ℝ) *
        Cslib.vertexNormPow 4 8 (1 / 4) retained error := by
  exact Cslib.expect_retained_vertex_pow_le (N := 8) (u := 1 / 4) (p := 4)
    (X := retained) (by norm_num) error true retained_nonempty

open Classical in
/-- The tail theorem counts bad draws inside the retained event. -/
theorem tail_bound :
    (#{σ ∈ ({σ | retained σ true} : Finset Bool) | (1 : ℝ) < |error σ true|} : ℝ) /
      #({σ | retained σ true} : Finset Bool) ≤
        (8 * (1 / 4) / (({σ | retained σ true} : Finset Bool).dens : ℝ) *
          Cslib.vertexNormPow 4 8 (1 / 4) retained error) / 1 ^ 4 := by
  exact Cslib.retained_vertex_tail_le (N := 8) (u := 1 / 4) (p := 4)
    (X := retained) (by norm_num) error true retained_nonempty (by norm_num)

open Classical in
example : #{σ ∈ ({σ | retained σ true} : Finset Bool) | (1 : ℝ) < |error σ true|} = 1 := by
  rw [retained_event]
  norm_num [error, retained, Finset.filter_singleton]

open Classical in
example : #{σ ∈ ({σ | retained σ true} : Finset Bool) | (2 : ℝ) < |error σ true|} = 0 := by
  rw [retained_event]
  norm_num [error, retained]

example : ¬ ({σ | retained σ false} : Finset Bool).Nonempty := by
  simp [retained]

end RootMetricConditioningTests
