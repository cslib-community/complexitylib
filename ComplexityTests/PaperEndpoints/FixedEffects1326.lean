/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedEffects
import all Complexity.Statistics.LeastSquares.FixedEffects
import all Complexity.Foundations.Optimization.FiniteMinPlus
import Mathlib.Tactic.NormNum

/-! Executable rational fixed-effects audits, including singular first crossings. -/

open Cslib.LeastSquares.FixedEffects

namespace FixedEffects1326

/-- Three observations with positive full-data slope. -/
public def groups : List (List Point) := [[(0, 0), (1, 2), (2, 1)]]

/-- The exact recovered witness removes the first observation. -/
public def result : List Choice := [⟨1, [(1, 2), (2, 1)]⟩]

/-- Both the full slope and the recovered sign reversal are computed from data. -/
public theorem computed_audit :
    slope [⟨0, [(0, 0), (1, 2), (2, 1)]⟩] = 1 / 2 ∧
    audit groups = some result ∧ deletions result = 1 ∧ slope result = -1 ∧
    denominator result = 1 / 2 := by
  decide +kernel

/-- Optimality quantifies over every actual retained sublist, not just tested candidates. -/
public theorem optimal : Feasible groups result ∧
    ∀ q, Feasible groups q → 1 ≤ deletions q := by
  have h := audit_optimal_of_negative_numerator groups result computed_audit.2.1
    (by norm_num [numerator, result, Cslib.FiniteMinPlus.total, cross, mean])
  exact ⟨h.1, fun q hq => computed_audit.2.2.1 ▸ h.2 q hq⟩

/-- Two genuine groups require convolution: neither group alone can reverse the panel. -/
public theorem two_group_audit : audit (groups ++ groups) = some (result ++ result) ∧
    deletions (result ++ result) = 2 ∧ numerator (result ++ result) = -1 := by
  decide +kernel

/-- Empty groups disappear; singleton groups do not change the slope or optimal cost. -/
public theorem empty_and_singleton_groups :
    audit [[], [(0, 0), (1, 2), (2, 1)], [(8, 9)]] =
      some [⟨0, []⟩, ⟨1, [(1, 2), (2, 1)]⟩, ⟨0, [(8, 9)]⟩] := by
  decide +kernel

/-- A positive two-point slope becomes singular at the first zero crossing. -/
public theorem singular_crossing :
    slope [⟨0, [(0, 0), (1, 1)]⟩] = 1 ∧
    audit [[(0, 0), (1, 1)]] = some [⟨1, [(0, 0)]⟩] ∧
    denominator [⟨1, [(0, 0)]⟩] = 0 ∧
    ¬ Feasible [[(0, 0), (1, 1)]] [⟨1, [(0, 0)]⟩] := by
  simp only [Feasible, Valid, Cslib.FiniteMinPlus.Admissible, List.map_cons, List.map_nil,
    List.forall₂_cons, List.forall₂_nil_left_iff]
  decide +kernel

/-- Zero numerator can also have positive scatter: the tie-break retains a nonsingular pair. -/
public theorem nonsingular_zero_crossing :
    audit [[(0, 0), (0, 1), (1, 1)]] = some [⟨1, [(0, 1), (1, 1)]⟩] ∧
    denominator [⟨1, [(0, 1), (1, 1)]⟩] = 1 / 2 := by
  decide +kernel

/-- Repeated observations are separate input samples, not deduplicated points. -/
public theorem repeated_observations :
    (choices [(0, 0), (0, 0)]).length = 4 ∧ audit [[], []] = some [⟨0, []⟩, ⟨0, []⟩] := by
  decide +kernel

end FixedEffects1326
