/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.ScalarActivity
import Mathlib.Algebra.BigOperators.Fin

/-! Real-score clients of ordered query-activity capacity, including ties and obstructions. -/

open Cslib Cslib.Circuits.Boolean.WeightedThreshold

private def tiedIndex (x : Fin 2 → Bool) : ℕ :=
  (x 0).toNat + (x 1).toNat

private theorem tiedIndex_bound (x : Fin 2 → Bool) : tiedIndex x < 3 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [tiedIndex, h0, h1]

private theorem tiedScore_eq (x : Fin 2 → Bool) :
    weightedSum (fun _ : Fin 2 => (1 : ℝ)) x = (tiedIndex x : ℝ) := by
  simp [weightedSum, tiedIndex, Fin.sum_univ_two]

private theorem tiedIndex_order (x y : Fin 2 → Bool) (h : tiedIndex x < tiedIndex y) :
    weightedSum (fun _ : Fin 2 => (1 : ℝ)) x < weightedSum (fun _ : Fin 2 => (1 : ℝ)) y := by
  simp only [tiedScore_eq]
  exact_mod_cast h

-- Four inputs, three score classes: the two weight-one inputs have the same score and label.
open scoped Classical in
example : ∃ t : DecisionTree ℝ ℕ,
    t.leafCount = 3 ∧ t.depth ≤ 2 ∧ t.energy ≤ 1 ∧
      ∀ x : Fin 2 → Bool,
        t.eval (fun θ => decide (θ ≤ weightedSum (fun _ => 1) x)) = tiedIndex x :=
  (exists_scalarComparisonTree_iff (fun _ => 1) tiedIndex 2 1 3
    tiedIndex_bound tiedIndex_order).mpr (by decide)

-- Concrete realization: both attainable threshold equalities must take the true branch.
private def tiedTree : DecisionTree ℝ ℕ :=
  .node 2 (.node 1 (.leaf 0) (.leaf 1)) (.leaf 2)

example : tiedTree.leafCount = 3 ∧ tiedTree.depth = 2 ∧ tiedTree.energy = 1 := by
  decide

open scoped Classical in
example (x : Fin 2 → Bool) :
    tiedTree.eval (fun θ => decide (θ ≤ weightedSum (fun _ => 1) x)) = tiedIndex x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [tiedTree, DecisionTree.eval, weightedSum, Fin.sum_univ_two, tiedIndex, h0, h1]

private noncomputable def signedWeight (i : Fin 2) : ℝ :=
  if i = 0 then -1 else 1 / 2

private def signedIndex (x : Fin 2 → Bool) : ℕ :=
  2 * (!x 0).toNat + (x 1).toNat

private theorem signedIndex_bound (x : Fin 2 → Bool) : signedIndex x < 4 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [signedIndex, h0, h1]

private theorem signedScore_eq (x : Fin 2 → Bool) :
    weightedSum signedWeight x = (signedIndex x : ℝ) / 2 - 1 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [weightedSum, Fin.sum_univ_two, signedWeight, signedIndex, h0, h1]

private theorem signedIndex_order (x y : Fin 2 → Bool) (h : signedIndex x < signedIndex y) :
    weightedSum signedWeight x < weightedSum signedWeight y := by
  have hcast : (signedIndex x : ℝ) < (signedIndex y : ℝ) := by exact_mod_cast h
  simp only [signedScore_eq]
  linarith

-- Negative and fractional coefficients give scores -1, -1/2, 0, 1/2 in index order.
open scoped Classical in
example : ∃ t : DecisionTree ℝ ℕ,
    t.leafCount = 4 ∧ t.depth ≤ 3 ∧ t.energy ≤ 1 ∧
      ∀ x, t.eval (fun θ => decide (θ ≤ weightedSum signedWeight x)) = signedIndex x :=
  (exists_scalarComparisonTree_iff signedWeight signedIndex 3 1 4
    signedIndex_bound signedIndex_order).mpr (by decide)

-- All four signed-score classes are genuinely attained.
example : ∀ j : Fin 4, ∃ x : Fin 2 → Bool, signedIndex x = j.val := by
  decide

-- Two queries with energy one have capacity three, not four.
open scoped Classical in
example : ¬∃ t : DecisionTree ℝ ℕ,
    t.leafCount = 4 ∧ t.depth ≤ 2 ∧ t.energy ≤ 1 ∧
      ∀ x, t.eval (fun θ => decide (θ ≤ weightedSum signedWeight x)) = signedIndex x := by
  intro h
  have hcap := (exists_scalarComparisonTree_iff signedWeight signedIndex 2 1 4
    signedIndex_bound signedIndex_order).mp h
  exact (by decide : ¬(0 < 4 ∧ 4 ≤ BitString.ballSize 2 1)) hcap

-- A zero direction and a constant class index require no queries, even on a nonempty cube.
open scoped Classical in
example : ∃ t : DecisionTree ℝ ℕ,
    t.leafCount = 1 ∧ t.depth ≤ 0 ∧ t.energy ≤ 0 ∧
      ∀ x : Fin 3 → Bool,
        t.eval (fun θ => decide (θ ≤ weightedSum (fun _ => 0) x)) = 0 := by
  apply (exists_scalarComparisonTree_iff (fun _ : Fin 3 => 0) (fun _ => 0) 0 0 1
    (fun _ => by decide) (fun _ _ h => by omega)).mpr
  decide

-- Dimension zero is included: its Boolean cube still has one input and one score class.
open scoped Classical in
example : ∃ t : DecisionTree ℝ ℕ,
    t.leafCount = 1 ∧ t.depth ≤ 0 ∧ t.energy ≤ 4 ∧
      ∀ x : Fin 0 → Bool,
        t.eval (fun θ => decide (θ ≤ weightedSum (fun _ => 0) x)) = 0 := by
  apply (exists_scalarComparisonTree_iff (fun _ : Fin 0 => 0) (fun _ => 0) 0 4 1
    (fun _ => by decide) (fun _ _ h => by omega)).mpr
  decide

-- Equal scores cannot carry different labels, regardless of the tree's resource bounds.
open scoped Classical in
example : ¬∃ t : DecisionTree ℝ ℕ, ∀ x : Fin 1 → Bool,
    t.eval (fun θ => decide (θ ≤ weightedSum (fun _ => 0) x)) = (x 0).toNat := by
  rintro ⟨t, ht⟩
  have hfalse := ht (fun _ => false)
  have htrue := ht (fun _ => true)
  simp only [weightedSum, zero_mul, Finset.sum_const_zero, Bool.toNat_false, Bool.toNat_true]
    at hfalse htrue
  omega
