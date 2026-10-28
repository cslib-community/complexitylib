/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Separable
import Mathlib.Data.Fintype.Powerset

/-!
Regression clients for finite quantiles and the leaf-count rectangle theorem.
-/

open Cslib

namespace ThresholdRectangles

-- All scores tie; both weak level sets retain every point, including at proportions zero and one.
example (a : ℝ) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∃ p ∈ ({-2, 0, 3} : Finset ℤ),
      a * 3 ≤ ((({-2, 0, 3} : Finset ℤ).filter fun _ => (7 : ℝ) ≤ 7).card : ℝ) ∧
      (1 - a) * 3 ≤ ((({-2, 0, 3} : Finset ℤ).filter fun _ => (7 : ℝ) ≤ 7).card : ℝ) := by
  simpa using Finset.exists_quantile ({-2, 0, 3} : Finset ℤ) (by simp) (fun _ => (7 : ℝ)) ha ha₁

-- At `a = 0` and `a = 1`, the quantile witness on `{-2, 0, 3}` must be `-2` and `3` respectively.
example : ∃ p ∈ ({-2, 0, 3} : Finset ℤ), p = -2 ∧
    3 ≤ (({-2, 0, 3} : Finset ℤ).filter fun x => p ≤ x).card := by
  obtain ⟨p, hp, hle, hge⟩ := Finset.exists_quantile ({-2, 0, 3} : Finset ℤ) (by simp) id
    (a := 0) (by norm_num) (by norm_num)
  have hge' : 3 ≤ (({-2, 0, 3} : Finset ℤ).filter fun x => p ≤ x).card := by
    simpa using hge
  clear hle hge
  refine ⟨p, hp, ?_, hge'⟩
  revert p hp hge'
  decide

example : ∃ p ∈ ({-2, 0, 3} : Finset ℤ), p = 3 ∧
    3 ≤ (({-2, 0, 3} : Finset ℤ).filter fun x => x ≤ p).card := by
  obtain ⟨p, hp, hle, hge⟩ := Finset.exists_quantile ({-2, 0, 3} : Finset ℤ) (by simp) id
    (a := 1) (by norm_num) (by norm_num)
  have hle' : 3 ≤ (({-2, 0, 3} : Finset ℤ).filter fun x => x ≤ p).card := by
    simpa using hle
  clear hle hge
  refine ⟨p, hp, ?_, hle'⟩
  revert p hp hle'
  decide

example : ¬ ∃ p ∈ (∅ : Finset ℤ), (0 : ℝ) ≤ 1 := by simp

private def tied : SeparableComparison (Fin 5) (Fin 7) :=
  ⟨fun _ => 0, fun _ => 0, 0⟩

-- Equality belongs to the true branch.
example (x : Fin 5) (y : Fin 7) : tied.eval x y = true := by
  norm_num [SeparableComparison.eval, tied]

private def compare : SeparableComparison (Fin 5) (Fin 7) :=
  ⟨fun x => x.val, fun y => y.val, 3⟩

example : compare.eval 0 0 = false := by norm_num [SeparableComparison.eval, compare]
example : compare.eval 1 2 = true := by norm_num [SeparableComparison.eval, compare]

private def unbalanced : DecisionTree (SeparableComparison (Fin 5) (Fin 7)) ℕ :=
  .node compare (.leaf 0) (.node tied (.leaf 1) (.leaf 1))

-- The false branch of the tied query is unreachable, but still counts as a structural leaf.
example : unbalanced.leafCount = 3 := rfl

example : unbalanced.path (fun q => q.eval 0 0) = [false] := by
  norm_num [unbalanced, DecisionTree.path, SeparableComparison.eval, compare]

example : unbalanced.path (fun q => q.eval 1 2) = [true, true] := by
  norm_num [unbalanced, DecisionTree.path, SeparableComparison.eval, compare, tied]

example : unbalanced.eval (fun q => q.eval 1 2) = 1 := by
  norm_num [unbalanced, DecisionTree.eval, SeparableComparison.eval, compare, tied]

-- Repeated leaf labels do not identify the two distinct paths.
example : (DecisionTree.node () (.leaf 1) (.leaf 1)).path (fun _ => false) = [false] := rfl
example : (DecisionTree.node () (.leaf 1) (.leaf 1)).path (fun _ => true) = [true] := rfl

-- A nonempty 5-by-7 domain supplies a same-leaf rectangle with both sides losing at most three.
example : ∃ (A : Finset (Fin 5)) (B : Finset (Fin 7)) (p : List Bool),
    A.Nonempty ∧ B.Nonempty ∧ 5 ≤ A.card * 3 ∧ 7 ≤ B.card * 3 ∧
      ∀ x ∈ A, ∀ y ∈ B, unbalanced.path (fun q => q.eval x y) = p := by
  obtain ⟨A, B, p, _, _, hA, hB, hAc, hBc, hp⟩ :=
    unbalanced.exists_leaf_rectangle Finset.univ Finset.univ (by simp) (by simp)
  exact ⟨A, B, p, hA, hB, by simpa [unbalanced, DecisionTree.leafCount] using hAc,
    by simpa [unbalanced, DecisionTree.leafCount] using hBc, hp⟩

-- A one-leaf tree retains the whole product domain, including in infinite ambient types.
example : ∃ (A B : Finset ℤ) (p : List Bool),
    A ⊆ {-2, 0, 3} ∧ B ⊆ {5} ∧ A.Nonempty ∧ B.Nonempty ∧ 3 ≤ A.card ∧ 1 ≤ B.card ∧
      ∀ x ∈ A, ∀ y ∈ B,
        (DecisionTree.leaf () : DecisionTree (SeparableComparison ℤ ℤ) Unit).path
          (fun q => q.eval x y) = p := by
  simpa [DecisionTree.leafCount] using
    (DecisionTree.leaf () : DecisionTree (SeparableComparison ℤ ℤ) Unit).exists_leaf_rectangle
      {-2, 0, 3} {5} (by simp) (by simp)

-- The area corollary gives a genuine lower bound for XOR; every monochromatic rectangle has
-- area at most two. This finite predicate check is independent of the tree implementation.
private theorem xor_area (A B : Finset Bool) (b : Bool)
    (h : ∀ x ∈ A, ∀ y ∈ B, (x ^^ y) = b) : A.card * B.card ≤ 2 := by
  revert A B b
  decide

example (t : DecisionTree (SeparableComparison Bool Bool) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = (x ^^ y)) : 2 ≤ t.leafCount := by
  have h := t.card_mul_le_mul_leafCount_sq Finset.univ Finset.univ (by simp) (by simp)
    (R := 2) (fun A _ B _ b hb => xor_area A B b fun x hx y hy =>
      (ht x y).symm.trans (hb x hx y hy))
  norm_num only [Finset.card_univ, Fintype.card_bool] at h
  nlinarith [t.leafCount_pos]

-- The computing hypothesis has a concrete separable-comparison instance.
private def xorTree : DecisionTree (SeparableComparison Bool Bool) Bool :=
  .node ⟨fun x => x.toNat, fun y => y.toNat, 1⟩ (.leaf false)
    (.node ⟨fun x => x.toNat, fun y => y.toNat, 2⟩ (.leaf true) (.leaf false))

example : ∃ t : DecisionTree (SeparableComparison Bool Bool) Bool,
    ∀ x y, t.eval (fun q => q.eval x y) = (x ^^ y) := by
  refine ⟨xorTree, ?_⟩
  intro x y
  cases x <;> cases y <;> norm_num [xorTree, DecisionTree.eval, SeparableComparison.eval]

-- Structural node count, rank, decision-list predicate, and energy on `unbalanced`.
example :
    unbalanced.nodeCount = 2 ∧
      unbalanced.leafCount = 2 + 1 ∧
      unbalanced.rank = 1 ∧
      unbalanced.energy = 2 :=
  ⟨rfl, unbalanced.leafCount_eq_nodeCount_add_one, rfl, rfl⟩

example : unbalanced.IsDecisionList ∧ unbalanced.rank ≤ 1 := by
  have hdl : unbalanced.IsDecisionList := Or.inl ⟨rfl, Or.inl ⟨rfl, trivial⟩⟩
  exact ⟨hdl, hdl.rank_le_one⟩

example :
    unbalanced.leafCount =
        ∑ j ∈ Finset.range (unbalanced.rank + 1), unbalanced.depth.choose j ∧
      unbalanced.leafCount <
        ∑ j ∈ Finset.range (unbalanced.energy + 1), unbalanced.depth.choose j :=
  ⟨le_antisymm unbalanced.leafCount_le_sum_choose_rank (by decide),
    lt_of_le_of_ne unbalanced.leafCount_le_sum_choose_energy (by decide)⟩

-- Concrete `BiMonotoneComparison` queries using `ofMax` and `ofMin`.
private noncomputable def maxCompare : BiMonotoneComparison (Fin 5) (Fin 7) :=
  BiMonotoneComparison.ofMax (fun x => x.val) (fun y => y.val) 2

private noncomputable def minCompare : BiMonotoneComparison (Fin 5) (Fin 7) :=
  BiMonotoneComparison.ofMin (fun x => x.val) (fun y => y.val) 1

example : maxCompare.eval 0 1 = false := by
  norm_num [maxCompare, BiMonotoneComparison.eval_ofMax]

example : maxCompare.eval 0 2 = true := by
  norm_num [maxCompare, BiMonotoneComparison.eval_ofMax]

example : minCompare.eval 1 0 = false := by
  norm_num [minCompare, BiMonotoneComparison.eval_ofMin]

example : minCompare.eval 1 2 = true := by
  norm_num [minCompare, BiMonotoneComparison.eval_ofMin]

private noncomputable def biTree : DecisionTree (BiMonotoneComparison (Fin 5) (Fin 7)) ℕ :=
  .node maxCompare (.leaf 0) (.node minCompare (.leaf 1) (.leaf 2))

example : ∃ (A : Finset (Fin 5)) (B : Finset (Fin 7)) (p : List Bool),
    A.Nonempty ∧ B.Nonempty ∧ 5 ≤ A.card * 3 ∧ 7 ≤ B.card * 3 ∧
      ∀ x ∈ A, ∀ y ∈ B, biTree.path (fun q => q.eval x y) = p := by
  obtain ⟨A, B, p, _, _, hA, hB, hAc, hBc, hp⟩ :=
    biTree.exists_leaf_rectangle_biMonotone Finset.univ Finset.univ (by simp) (by simp)
  exact ⟨A, B, p, hA, hB, by simpa [biTree, DecisionTree.leafCount] using hAc,
    by simpa [biTree, DecisionTree.leafCount] using hBc, hp⟩

/--
info: 'Cslib.DecisionTree.IsDecisionList.rank_le_one' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.IsDecisionList.rank_le_one

end ThresholdRectangles
