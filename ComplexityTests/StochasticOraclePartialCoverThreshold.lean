/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.PartialCoverThreshold
import Mathlib.Tactic

/-! # Exact rational threshold and selector clients -/

open Cslib.Probability.StochasticOracle.PartialCover.Instance
open Cslib.Algorithms.Lean.Multicover

-- Exact equality at a power and strictly between powers.
example : rationalRepetitions (1/2) (1/8) (by norm_num) (by norm_num) (by norm_num) = 3 := by
  rw [rationalRepetitions, Nat.find_eq_iff]
  constructor
  · norm_num
  · intro n hn
    interval_cases n <;> norm_num
example : rationalRepetitions (1/2) (1/9) (by norm_num) (by norm_num) (by norm_num) = 4 := by
  rw [rationalRepetitions, Nat.find_eq_iff]
  constructor
  · norm_num
  · intro n hn
    interval_cases n <;> norm_num
example : rationalRepetitions (1/2) 1 (by norm_num) (by norm_num) (by norm_num) = 0 := by
  rw [rationalRepetitions, Nat.find_eq_zero]
  norm_num
example : rationalRepetitions (1/2) 2 (by norm_num) (by norm_num) (by norm_num) = 0 := by
  rw [rationalRepetitions, Nat.find_eq_zero]
  norm_num

-- Compiled evaluation exercises the actual search and repeated greedy output.
set_option linter.hashCommand false
/-- info: 3 -/
#guard_msgs in
#eval rationalRepetitions (1/2) (1/8) (by norm_num) (by norm_num) (by norm_num)

private def singletonOracle : Oracle Unit := ⟨{()}, 1⟩

/-- info: 3 -/
#guard_msgs in
#eval (rationalBatch [singletonOracle] (1/2) (1/8)
  (by norm_num) (by norm_num) (by norm_num)).length

/-- info: 0 -/
#guard_msgs in
#eval (rationalBatch ([] : List (Oracle Unit)) (1/2) (1/8)
  (by norm_num) (by norm_num) (by norm_num)).length

-- Three parallel calls with outcome-dependent bills below the unit cap.
-- No independence is imposed on the bills or latencies.
example (ω : Bool) :
    let calls := rationalBatch [singletonOracle] (1/2) (1/8)
      (by norm_num) (by norm_num) (by norm_num)
    (∑ _i : Fin calls.length, if ω then (1 : ℝ) else 0) ≤
      (bill (batch [singletonOracle] (repetitions ((1/2 : ℚ) : ℝ) ((1/8 : ℚ) : ℝ))) : ℝ) ∧
    ∀ _i : Fin calls.length, (if ω then (2 : ℝ) else 1) ≤ 2 := by
  apply rationalBatch_execution [singletonOracle] (1/2) (1/8)
    (by norm_num) (by norm_num) (by norm_num) 2
    (fun _ ω => if ω then 1 else 0) (fun _ ω => if ω then 2 else 1) (fun _ => 2)
    ?_ ?_ (by simp) ω
  · intro i ω
    have hm := mem_run [singletonOracle] _ _ (List.get_mem
      (rationalBatch [singletonOracle] (1/2) (1/8)
        (by norm_num) (by norm_num) (by norm_num)) i)
    simp only [List.mem_singleton] at hm
    rw [hm]
    cases ω <;> norm_num [singletonOracle]
  · intro i ω
    cases ω <;> norm_num
