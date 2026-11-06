/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedEffects.Resources
import all Complexity.Statistics.LeastSquares.FixedEffects.Resources
import all Complexity.Foundations.Optimization.FiniteMinPlus.Cached
import all Complexity.Statistics.LeastSquares.FixedEffects
import all Cslib.Algorithms.Lean.TimeM
import Mathlib.Tactic.NormNum

/-! Computed cached curves, doubling, materialized recovery and resource contracts. -/

open Cslib.LeastSquares.FixedEffects
open Cslib.LeastSquares.FixedEffects.Resources

namespace FixedEffectsResources1326

/-- Positive original numerator, with a nonsingular one-deletion optimum. -/
public def groups : List (List Point) := [[(0, 0), (1, 2), (2, 1)]]

/-- The retained observations returned by both the reference and efficient algorithms. -/
public def plan : List Choice := [⟨1, [(1, 2), (2, 1)]⟩]

/-- The actual pipeline computes the retained observations and a counted execution. -/
public theorem computed :
    (run groups).ret.map (fun r => r.hit.entry.plan) = some plan ∧
    (run groups).ret.map Result.retained = some [[(1, 2), (2, 1)]] ∧
    (run groups).ret.map (fun r => r.hit.index) = some 1 ∧
    (run groups).time = 493 := by
  decide +kernel

/-- Two groups force a failed cap-one round and a successful cap-two round. -/
public theorem doubling :
    (attempt (curves (groups ++ groups)).ret 1).ret = none ∧
    (run (groups ++ groups)).ret.map (fun r => r.hit.index) = some 2 ∧
    (run (groups ++ groups)).ret.map Result.retained =
      some [[(1, 2), (2, 1)], [(1, 2), (2, 1)]] ∧
    (run (groups ++ groups)).time = 1295 := by
  decide +kernel

/-- Empty inputs terminate; their fixed initialization cost is not claimed O(n). -/
public theorem empty_input :
    (run []).ret.map Result.retained = some [] ∧ (run []).time = 10 := by
  decide +kernel

/-- Empty groups still have a read cost; repeated observations are not deduplicated. -/
public theorem empty_and_repeated :
    (inputSize [[], [], [(0, 0), (0, 0)]]).time = 5 ∧
    (run [[], []]).ret.map Result.retained = some [[], []] ∧
    (subsets [(0, 0), (0, 0)]).ret.length = 4 := by
  decide +kernel

/-- The efficient tie-break retains nonsingular data at a zero numerator crossing. -/
public theorem zero_crossing :
    (run [[(0, 0), (0, 1), (1, 1)]]).ret.map Result.retained =
      some [[(0, 1), (1, 1)]] := by
  decide +kernel

/-- A singular first crossing is returned without asserting feasibility. -/
public theorem singular :
    (run [[(0, 0), (1, 1)]]).ret.map (fun r => r.hit.index) = some 1 ∧
    (run [[(0, 0), (1, 1)]]).ret.map
      (fun r => denominator r.hit.entry.plan) = some 0 := by
  decide +kernel

/-- Universal correctness and resource conclusions are applied to computed output,
not supplied as hypotheses in an algorithm structure. -/
public theorem optimal_and_bounded :
    ∃ r, (run groups).ret = some r ∧ Feasible groups r.hit.entry.plan ∧
      (∀ q, Feasible groups q → r.hit.index ≤ deletions q) ∧
      (run groups).time ≤ 300 * (3 * 2 ^ 3 + 3 * r.hit.index) := by
  obtain ⟨r, hr⟩ := run_exists groups
  have hp : r.hit.entry.plan = plan := by
    have := computed.1
    rw [hr] at this
    exact Option.some.inj this
  have hspec := run_time_of_nondegenerate groups 3 r hr
    (by simp [groups]) (by simp [groups])
    (by norm_num [groups, fullPlan, numerator, Cslib.FiniteMinPlus.total, cross, mean])
    ⟨r.hit.entry.plan, (run_spec groups r hr).1, (run_spec groups r hr).2.1, rfl,
      by rw [hp]; norm_num [plan, denominator, Cslib.FiniteMinPlus.total, variance, mean]⟩
  exact ⟨r, hr, hspec.1, hspec.2.1, by simpa [groups, sampleSize,
    Cslib.FiniteMinPlus.total] using hspec.2.2⟩

end FixedEffectsResources1326
