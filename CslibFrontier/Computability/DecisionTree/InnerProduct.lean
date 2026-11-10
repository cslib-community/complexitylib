/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Separable
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.Nat.Choose.Real
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles
import Mathlib.Tactic.Positivity

/-!
# Inner-product lower bounds for separable and bi-monotone comparison trees

A separable-comparison or bi-monotone-comparison tree computing the inner product modulo two on
`ι → Bool` has leaf count `L` satisfying `2 ^ Fintype.card ι ≤ L ^ 2`. This division-free form of
`L ≥ 2 ^ (Fintype.card ι / 2)` follows from the generic leaf-rectangle theorem and the Hadamard
rectangle bound. Query scores are arbitrary real functions; the result imposes no restriction
on their magnitudes or on the tree depth, and does not require a threshold circuit model.

Combining the leaf bound with the structural leaf bounds in `Leaves.lean` and the partial
binomial-sum estimates in `CslibFrontier/Foundations/Data/Nat/Choose/Real.lean` yields
internal-node,
decision-list, bounded-rank,
and bounded-energy lower bounds for inner product.

## Main results

* `Cslib.DecisionTree.two_pow_le_leafCount_sq_of_biMonotone_dotProduct`,
  `Cslib.DecisionTree.two_pow_le_leafCount_sq_of_dotProduct`: the inner-product leaf bounds.
* `Cslib.DecisionTree.two_pow_le_nodeCount_add_one_sq_of_dotProduct`: the internal-node bound.
* `Cslib.DecisionTree.two_pow_le_depth_add_one_sq_of_isDecisionList_dotProduct`: the
  decision-list depth bound.
* `Cslib.DecisionTree.two_pow_le_sum_choose_rank_sq_of_dotProduct`,
  `Cslib.DecisionTree.le_rank_mul_logb_depth_of_dotProduct`,
  `Cslib.DecisionTree.rank_mul_rpow_le_depth_of_dotProduct`: bounded-rank tradeoffs.
* `Cslib.DecisionTree.two_pow_le_sum_choose_energy_sq_of_dotProduct`,
  `Cslib.DecisionTree.le_energy_mul_logb_depth_of_dotProduct`,
  `Cslib.DecisionTree.energy_mul_rpow_le_depth_of_dotProduct`: tree-energy tradeoffs.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Corollaries 2.5, 2.7, and 2.8]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

open Cslib.BitString

namespace Cslib.DecisionTree

/-- Computing inner product modulo two with a bi-monotone comparison tree requires the square of
the leaf count to be at least the cardinality of the Boolean cube. The statement includes zero
coordinates. -/
theorem two_pow_le_leafCount_sq_of_biMonotone_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (BiMonotoneComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ t.leafCount ^ 2 := by
  classical
  have h := t.card_mul_le_mul_leafCount_sq_biMonotone Finset.univ Finset.univ (by simp) (by simp)
    (R := 2 ^ Fintype.card ι) (fun A _ B _ b hb =>
      card_mul_le_two_pow_of_dotProduct_eq A B b fun x hx y hy =>
        (ht x y).symm.trans (hb x hx y hy))
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

/-- Computing inner product modulo two requires the square of the leaf count to be at least
the cardinality of the Boolean cube. The statement includes zero coordinates. -/
theorem two_pow_le_leafCount_sq_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ t.leafCount ^ 2 := by
  have h := two_pow_le_leafCount_sq_of_biMonotone_dotProduct
    (t.mapQueries SeparableComparison.toBiMonotone)
    fun x y => by simpa [Function.comp_def] using ht x y
  simpa using h

/-- Every bi-monotone comparison tree computing inner product modulo two satisfies
`2 ^ Fintype.card ι ≤ (nodeCount + 1) ^ 2`. -/
theorem two_pow_le_nodeCount_add_one_sq_of_biMonotone_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (BiMonotoneComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (t.nodeCount + 1) ^ 2 := by
  rw [← t.leafCount_eq_nodeCount_add_one]
  exact t.two_pow_le_leafCount_sq_of_biMonotone_dotProduct ht

/-- Every separable-comparison tree computing inner product modulo two satisfies
`2 ^ Fintype.card ι ≤ (nodeCount + 1) ^ 2`. -/
theorem two_pow_le_nodeCount_add_one_sq_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (t.nodeCount + 1) ^ 2 := by
  rw [← t.leafCount_eq_nodeCount_add_one]
  exact t.two_pow_le_leafCount_sq_of_dotProduct ht

/-- Every separable-comparison tree of rank at most `1` computing inner product modulo two
satisfies `2 ^ Fintype.card ι ≤ (depth + 1) ^ 2`. -/
theorem two_pow_le_depth_add_one_sq_of_rank_le_one_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (hr : t.rank ≤ 1)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (t.depth + 1) ^ 2 :=
  (t.two_pow_le_leafCount_sq_of_dotProduct ht).trans
    (Nat.pow_le_pow_left (t.leafCount_le_depth_add_one_of_rank_le_one hr) 2)

/-- Every separable-comparison decision list computing inner product modulo two satisfies
`2 ^ Fintype.card ι ≤ (depth + 1) ^ 2`. -/
theorem two_pow_le_depth_add_one_sq_of_isDecisionList_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (hl : t.IsDecisionList)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (t.depth + 1) ^ 2 :=
  t.two_pow_le_depth_add_one_sq_of_rank_le_one_dotProduct hl.rank_le_one ht

/-- Every separable-comparison decision list computing inner product modulo two satisfies
`2 ^ Fintype.card ι ≤ (nodeCount + 1) ^ 2`. -/
theorem two_pow_le_nodeCount_add_one_sq_of_isDecisionList_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (_hl : t.IsDecisionList)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (t.nodeCount + 1) ^ 2 :=
  t.two_pow_le_nodeCount_add_one_sq_of_dotProduct ht

/-- Every bi-monotone comparison tree computing inner product modulo two satisfies the binomial-sum
rank-depth lower bound `2 ^ Fintype.card ι ≤ (∑ j ≤ rank, depth.choose j) ^ 2`. -/
theorem two_pow_le_sum_choose_rank_sq_of_biMonotone_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (BiMonotoneComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (∑ j ∈ Finset.range (t.rank + 1), t.depth.choose j) ^ 2 :=
  (t.two_pow_le_leafCount_sq_of_biMonotone_dotProduct ht).trans
    (Nat.pow_le_pow_left t.leafCount_le_sum_choose_rank 2)

/-- Every separable-comparison tree computing inner product modulo two satisfies the binomial-sum
rank-depth lower bound `2 ^ Fintype.card ι ≤ (∑ j ≤ rank, depth.choose j) ^ 2`. -/
theorem two_pow_le_sum_choose_rank_sq_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (∑ j ∈ Finset.range (t.rank + 1), t.depth.choose j) ^ 2 :=
  (t.two_pow_le_leafCount_sq_of_dotProduct ht).trans
    (Nat.pow_le_pow_left t.leafCount_le_sum_choose_rank 2)

/-- Logarithmic rank-depth tradeoff for a separable-comparison tree computing inner product modulo
two. At rank zero, this forces `Fintype.card ι = 0`. -/
theorem le_rank_mul_logb_depth_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    (Fintype.card ι : ℝ) / 2 ≤
      t.rank * Real.logb 2 (Real.exp 1 * t.depth / t.rank) :=
  le_mul_logb_of_two_pow_le_sum_choose_sq t.rank_le_depth
    (t.two_pow_le_sum_choose_rank_sq_of_dotProduct ht)

/-- Depth lower bound in terms of rank for a separable-comparison tree computing inner product
modulo two: `(rank / exp 1) * 2 ^ (m / (2 * rank)) ≤ depth`. -/
theorem rank_mul_rpow_le_depth_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    t.rank / Real.exp 1 * (2 : ℝ) ^ ((Fintype.card ι : ℝ) / (2 * t.rank)) ≤ t.depth :=
  mul_rpow_le_of_two_pow_le_sum_choose_sq t.rank_le_depth
    (t.two_pow_le_sum_choose_rank_sq_of_dotProduct ht)

/-- Every bi-monotone comparison tree computing inner product modulo two satisfies the binomial-sum
energy-depth lower bound `2 ^ Fintype.card ι ≤ (∑ j ≤ energy, depth.choose j) ^ 2`. -/
theorem two_pow_le_sum_choose_energy_sq_of_biMonotone_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (BiMonotoneComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (∑ j ∈ Finset.range (t.energy + 1), t.depth.choose j) ^ 2 :=
  (t.two_pow_le_leafCount_sq_of_biMonotone_dotProduct ht).trans
    (Nat.pow_le_pow_left t.leafCount_le_sum_choose_energy 2)

/-- Every separable-comparison tree computing inner product modulo two satisfies the binomial-sum
energy-depth lower bound `2 ^ Fintype.card ι ≤ (∑ j ≤ energy, depth.choose j) ^ 2`. -/
theorem two_pow_le_sum_choose_energy_sq_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (∑ j ∈ Finset.range (t.energy + 1), t.depth.choose j) ^ 2 :=
  (t.two_pow_le_leafCount_sq_of_dotProduct ht).trans
    (Nat.pow_le_pow_left t.leafCount_le_sum_choose_energy 2)

/-- Logarithmic energy-depth tradeoff for a separable-comparison tree computing inner product modulo
two. At energy zero, this forces `Fintype.card ι = 0`. -/
theorem le_energy_mul_logb_depth_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    (Fintype.card ι : ℝ) / 2 ≤
      t.energy * Real.logb 2 (Real.exp 1 * t.depth / t.energy) :=
  le_mul_logb_of_two_pow_le_sum_choose_sq t.energy_le_depth
    (t.two_pow_le_sum_choose_energy_sq_of_dotProduct ht)

/-- Depth lower bound in terms of energy for a separable-comparison tree computing inner product
modulo two: `(energy / exp 1) * 2 ^ (m / (2 * energy)) ≤ depth`. -/
theorem energy_mul_rpow_le_depth_of_dotProduct {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = x ⬝ᵥ y) :
    t.energy / Real.exp 1 * (2 : ℝ) ^ ((Fintype.card ι : ℝ) / (2 * t.energy)) ≤ t.depth :=
  mul_rpow_le_of_two_pow_le_sum_choose_sq t.energy_le_depth
    (t.two_pow_le_sum_choose_energy_sq_of_dotProduct ht)

end Cslib.DecisionTree
