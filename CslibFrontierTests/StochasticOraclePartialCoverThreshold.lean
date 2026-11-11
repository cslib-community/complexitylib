/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverThreshold
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

-- Joint output and correlated random resources; billing also includes failed batches.
noncomputable section
open Cslib.Optimization.OneConstraint
open Cslib.Probability.StochasticOracle.PartialCover
open Finset

private def one : Instance Unit Unit where
  ground := univ
  sets _ := {()}
  sets_subset _ := subset_univ _
  weight _ := 1
  weight_nonneg _ := by norm_num
  dual _ := 1
  dual_nonneg _ := by norm_num
  dual_feasible _ := by simp

-- A deterministic successful response is admissible at every reached history.
private def certain : ResponseKernel Unit := fun _ => Distribution.pure {()}

private theorem certain_admissible (vs : List (Finset Unit))
    (h : List (Finset Unit)) (C : Finset Unit) :
    one.Admissible 1 (1/2) certain h C vs := by
  induction vs generalizing h C with
  | nil => trivial
  | cons V vs ih =>
    refine ⟨?_, fun P _ => ih (P :: h) (one.step 1 C P)⟩
    intro e _ he
    have hC : C = ∅ := by
      ext u
      cases u
      simp only [Finset.notMem_empty, iff_false]
      intro hu
      exact he (mem_biUnion.mpr ⟨(), hu, by simp [one]⟩)
    subst C
    norm_num [certain, event, Distribution.mean_pure, Certified, cost, covered, one]

example :
    let calls := batch [singletonOracle] (repetitions ((1/2 : ℚ) : ℝ) (1/8))
    let joint := (one.law 1 certain [] ∅ (calls.map Oracle.eligible)).bind
      (fun P => (pair false true (1/2 : ℝ) (by norm_num) (by norm_num)).map
        (fun r => (P, r)))
    (7/8 : ℝ) ≤ joint.mean (fun x => if
      one.covered x.1 = one.ground ∧ one.cost x.1 ≤ ∑ e ∈ one.ground, one.dual e ∧
      (∑ _i : Fin (rationalBatch [singletonOracle] (1/2) (1/8)
        (by norm_num) (by norm_num) (by norm_num)).length,
        if x.2 then (1 : ℝ) else 0) ≤ (bill calls : ℝ) ∧
      (∀ _i : Fin (rationalBatch [singletonOracle] (1/2) (1/8)
        (by norm_num) (by norm_num) (by norm_num)).length,
        (if x.2 then (2 : ℝ) else 1) ≤ 2) then 1 else 0) := by
  have h := rationalBatch_joint_execution one rfl (by simp [one]) [singletonOracle]
    (by intro e; exact ⟨singletonOracle, by simp, by cases e; simp [singletonOracle]⟩)
    (1/2) (1/8) (by norm_num) (by norm_num) (by norm_num) 1 2 certain
    (fun _ => pair false true (1/2 : ℝ) (by norm_num) (by norm_num))
    (fun _ _ r => if r then 1 else 0) (fun _ _ r => if r then 2 else 1)
    (fun _ => 2) ?_ ?_ (by simp) ?_
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h ⊢
    simp only [Fintype.card_unique, Nat.cast_one, div_one] at h
    simpa only [one_mul,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, show (1 : ℝ) - 1/8 = 7/8 by norm_num] using h
  · intro i P r
    have hm := mem_run [singletonOracle] _ _ (List.get_mem _ i)
    simp only [List.mem_singleton] at hm
    rw [hm]
    cases r <;> norm_num [singletonOracle]
  · intro i P r
    cases r <;> norm_num
  · convert certain_admissible
      ((batch [singletonOracle] (repetitions ((1/2 : ℚ) : ℝ) (1/8))).map
        Oracle.eligible) [] ∅ using 1 <;> norm_num
