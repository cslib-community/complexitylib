/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveLowerCost
import Mathlib.Tactic

/-! A correlated two-turn client of conditional revealed-progress accounting. -/

open Finset Cslib.Optimization.OneConstraint Cslib.Probability.StochasticOracle
noncomputable section
namespace StochasticOracleAdaptiveLowerCostTests

@[expose] public def coin : Distribution Bool ℝ :=
  ⟨fun _ => 1 / 2, fun _ => by norm_num, by norm_num [Fintype.sum_bool]⟩

-- Both turns use the same bit. The second history exposes the first bit, so a
-- bound p = 1/2 would be false there; the valid uniform envelope is p = 1.
public theorem correlated_lower_cost : (3 : ℝ) ≤ coin.mean (fun _ => ∑ _t : Fin 2, (3 : ℝ)) := by
  have h := conditional_lower_cost coin 2 (fun _ => Bool)
    (fun t ω => if t = 0 then false else ω)
    (fun _ _ => 1) (fun _ ω => if ω then 1 else 0) (fun _ _ => 3)
    (fun ω => ω = true) 2 1 3 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num [coin, Distribution.mean, Fintype.sum_bool])
    (by intro ω; cases ω <;> norm_num [Fin.sum_univ_two]) (by norm_num)
    (by
      intro t h
      rw [one_mul]
      apply sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (coin.nonneg ω)
      split_ifs <;> norm_num)
    (by
      intro t h
      rw [mul_sum]
      apply sum_le_sum
      intro ω _
      split_ifs <;> ring_nf <;> rfl)
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

-- The progress events coincide, rather than being independent Bernoulli trials.
public theorem correlated_progress_not_independent :
    coin.mean (fun ω => if ω = true ∧ ω = true then 1 else 0) ≠
    coin.mean (fun ω => if ω = true then 1 else 0) *
      coin.mean (fun ω => if ω = true then 1 else 0) := by
  norm_num [coin, Distribution.mean, Fintype.sum_bool]

-- Zero issued turns and zero required progress are permitted by the accounting
-- lemma, even though the source's nonempty-cover application uses positive r.
public theorem zero_turn_cost : (0 : ℝ) ≤ coin.mean (fun _ => ∑ _t : Fin 0, (0 : ℝ)) := by
  norm_num [Distribution.mean_const]

end StochasticOracleAdaptiveLowerCostTests
