/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Agnostic
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Halving
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Checked examples for agnostic online learning

The two-element class of constant classifiers on `Unit` has Littlestone dimension at most `1`.
Over `100` rounds, the agnostic learner's expected regret against it is below `45`, while every
deterministic learner can be forced to regret at least `50`. A deterministic learner's expected
mistakes are its mistakes, and the experts of the agnostic learner are the sets of at most `d`
rounds below `T`.
-/

open Cslib.MachineLearning.OnlineLearning.MistakeBound Finset

namespace CslibFrontierTests.AgnosticOnline

/-- The two constant classifiers on `Unit`. -/
def constants : Finset (Unit → Bool) := {fun _ => true, fun _ => false}

theorem littlestoneDim_constants_le : littlestoneDim (↑constants : Set (Unit → Bool)) ≤ 1 := by
  have h := littlestoneDim_le_log_card constants
  have hcard : constants.card = 2 := by decide
  rwa [hcard, Nat.log_eq_one_iff'.mpr ⟨le_rfl, by norm_num⟩, Nat.cast_one] at h

/-- A deterministic learner's expected mistakes are its mistakes: the constant-`true` learner errs
once on `[((), true), ((), false)]`. -/
example : expectedMistakes (OnlineLearner.toRandomized fun _ _ => true)
    [((), true), ((), false)] = 1 := by
  rw [expectedMistakes_toRandomized]
  norm_num [mistakes, mistakesFrom]

/-- The rounds `{0, 2}` form an expert for `T = 3`, `d = 2`, but not for `d = 1`. -/
example : ({0, 2} : Finset ℕ) ∈ flipSets 3 2 := mem_flipSets.mpr ⟨by decide, by decide⟩

example : ({0, 2} : Finset ℕ) ∉ flipSets 3 1 := fun h => by
  have := (mem_flipSets.mp h).2
  simp at this

/-- `2 √(100 log 101) < 45`. -/
theorem two_mul_sqrt_lt : 2 * √((100 : ℕ) * (1 : ℕ) * Real.log ((100 : ℕ) + 1)) < 45 := by
  have hlog : Real.log 101 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have : (2.7 : ℝ) ^ 5 < Real.exp 1 ^ 5 := by
      gcongr
      linarith [Real.exp_one_gt_d9]
    rw [h5]
    norm_num at this ⊢
    linarith
  have h225 : √(506.25 : ℝ) = 22.5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  have hsq : √(100 * Real.log 101) < 22.5 := by
    rw [← h225]
    gcongr
    linarith
  have hcast : ((100 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * Real.log (((100 : ℕ) : ℝ) + 1) =
      100 * Real.log 101 := by
    norm_num
  rw [hcast]
  linarith

/-- **Randomization helps.** Over `100` rounds, the agnostic learner's expected mistakes exceed
those of the best constant classifier by less than `45`. -/
example (S : List (Unit × Bool)) (hS : S.length ≤ 100) (c : Unit → Bool)
    (hc : c ∈ (↑constants : Set (Unit → Bool))) :
    expectedMistakes (agnosticSOA (↑constants) 100 1) S <
      (S.countP fun p => c p.1 ≠ p.2) + 45 :=
  (expectedMistakes_agnosticSOA_le littlestoneDim_constants_le S hS hc).trans_lt
    (by linarith [two_mul_sqrt_lt])

/-- **Deterministic learners cannot.** Every deterministic learner can be made to err in all
`100` rounds while a constant classifier errs in at most `50`. -/
example (A : OnlineLearner Unit) :
    ∃ S : List (Unit × Bool), S.length = 100 ∧ mistakes A S = 100 ∧
      ∃ c ∈ (↑constants : Set (Unit → Bool)), 2 * S.countP (fun p => c p.1 ≠ p.2) ≤ 100 :=
  exists_mistakes_eq_length_of_const_mem (by simp [constants]) (by simp [constants]) A () 100

end CslibFrontierTests.AgnosticOnline
