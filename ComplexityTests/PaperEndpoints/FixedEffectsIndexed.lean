/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedEffects.Indexed
import all Complexity.Statistics.LeastSquares.FixedEffects.Indexed
import all Complexity.Statistics.LeastSquares.FixedEffects.Resources
import all Complexity.Statistics.LeastSquares.FixedEffects
import all Complexity.Foundations.Optimization.FiniteMinPlus.Cached
import Mathlib.Tactic

/-! Original-index refinement and group survival beyond the small-deletion bound. -/

open Cslib.LeastSquares Cslib.LeastSquares.FixedEffects
open Cslib.LeastSquares.FixedEffects.Resources

namespace FixedEffectsIndexed

/-- One genuine one-deletion optimum and a singleton group whose dummy survives. -/
public def groups : List (List Point) := [[(0, 0), (1, 2), (2, 1)], [(7, 7)]]
/-- Actual returned observations, including the singleton. -/
public def plan : List Choice := [⟨1, [(1, 2), (2, 1)]⟩, ⟨0, [(7, 7)]⟩]

public theorem computed :
    (run groups).ret.map (fun r => r.hit.entry.plan) = some plan ∧
      (run groups).ret.map (fun r => r.hit.index) = some 1 := by
  decide +kernel

-- An optimum of one deletion is not strictly below the singleton's group size.
example : (groups.get ⟨1, by decide⟩).length = 1 := by decide

/-- The source nondegeneracy hypothesis is checked on the actual returned plan. -/
public theorem indexed_execution :
    ∃ (r : Result) (s : Finset (Sigma (Indexed.Rows groups))),
      (run groups).ret = some r ∧ Indexed.Corresponds groups r.hit.entry.plan s ∧
      MatrixModel.PreservesGroups s ∧
      Cslib.LeastSquares.Feasible (MatrixModel.row (Indexed.x groups))
        (fun p => Indexed.y groups p.1 p.2) (Pi.single none 1) 0
        (fun p => if p ∈ s then 1 else 0) ∧
      s.card = 3 ∧
      integralStability (MatrixModel.row (Indexed.x groups))
        (fun p => Indexed.y groups p.1 p.2) (Pi.single none 1) 0 = 1 ∧
      (run groups).time ≤ 300 * (4 * 2 ^ 3 + 4) := by
  obtain ⟨r, hr⟩ := run_exists groups
  have hp : r.hit.entry.plan = plan := by
    have hh := computed.1
    rw [hr] at hh
    exact Option.some.inj hh
  have hi : r.hit.index = 1 := by
    have hh := computed.2
    rw [hr] at hh
    exact Option.some.inj hh
  obtain ⟨s, hs, hpres, _, hf, hc, he, ht⟩ := Indexed.run_indexed_optimal groups 3 r hr
    (by simp [groups]) (by simp [groups])
    (by norm_num [groups, fullPlan, numerator, Cslib.FiniteMinPlus.total, cross, mean])
    ⟨r.hit.entry.plan, (run_spec groups r hr).1, (run_spec groups r hr).2.1, rfl,
      by rw [hp]; norm_num [plan, denominator, Cslib.FiniteMinPlus.total, variance, mean]⟩
  have hn : Fintype.card (Sigma (Indexed.Rows groups)) = 4 := by
    rw [Indexed.card_rows]
    rfl
  have hcard := Finset.card_le_univ s
  rw [hn, hi] at hc
  rw [Fintype.card_sigma] at hcard
  have hle : s.card ≤ 4 := by simpa only [← Fintype.card_sigma, hn] using hcard
  refine ⟨r, s, hr, hs, hpres, hf, by omega, hi ▸ he, ?_⟩
  simpa only [hi, show sampleSize groups = 4 from rfl, Nat.mul_one] using ht

-- Equal-valued observations remain two distinct retained original positions.
example : ∃ t : Finset (Fin ([(0, 0), (0, 0), (0, 0)] : List Point).length),
    Indexed.Represents [(0, 0), (0, 0), (0, 0)] [(0, 0), (0, 0)] t ∧ t.card = 2 := by
  obtain ⟨t, ht⟩ := Indexed.represents_of_sublist
    [(0, 0), (0, 0), (0, 0)] [(0, 0), (0, 0)] (by decide)
  exact ⟨t, ht, Indexed.card_represents ht⟩

-- Refitted subset equality permits empty original groups, without falsely
-- asserting that their original zero dummy columns become positive definite.
example : refittedIntegralStability [[], [(0, 0), (1, -1)]] =
    MatrixModel.subsetStability (Indexed.x [[], [(0, 0), (1, -1)]])
      (Indexed.y [[], [(0, 0), (1, -1)]]) :=
  Indexed.refittedIntegralStability_eq_subsetStability _

-- Every original subset, including those erasing groups, has a valid executable plan.
example (gs : List (List Point)) (s : Finset (Sigma (Indexed.Rows gs))) :
    ∃ p, Valid gs p ∧ Indexed.Corresponds gs p s ∧
      deletions p = Fintype.card (Sigma (Indexed.Rows gs)) - s.card := by
  obtain ⟨p, hp⟩ := Indexed.plan_of_subset gs s
  exact ⟨p, hp.valid, hp, hp.deletions⟩

end FixedEffectsIndexed
