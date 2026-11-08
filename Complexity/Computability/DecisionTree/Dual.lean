/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Cost

/-!
# The dual of a decision tree

The *dual* of a Boolean function `f` is `x ↦ ¬ f(¬ x)`, with `¬ x` the bitwise complement. The
dual of a decision tree (`DecisionTree.dual`) swaps the two children of every node and negates
every leaf. On `x` it follows the path of the original tree on `¬ x`, with the same queries
(`DecisionTree.queries_dual`, `DecisionTree.cost_dual`), and outputs the negated leaf
(`DecisionTree.eval_dual`). So it computes the dual of the function computed by the original tree
(`DecisionTree.Computes.dual`), and a function and its dual have the same decision tree complexity
(`DecisionTree.complexity_dual`). For example, De Morgan duality turns OR into AND, so lower and
upper bounds for an OR-rooted formula transfer to the AND-rooted one.

## Main definitions

* `Cslib.DecisionTree.dual`: swap the children of every node and negate every leaf.

## Main results

* `Cslib.DecisionTree.Computes.dual`: the dual tree computes the dual function.
* `Cslib.DecisionTree.complexity_dual`: `D(x ↦ ¬ f(¬ x)) = D(f)`.
-/

public section

namespace Cslib.DecisionTree

variable {ι : Type*}

/-- The dual of a decision tree: swap the two children of every node and negate every leaf. -/
@[expose] def dual : DecisionTree ι Bool → DecisionTree ι Bool
  | leaf b => leaf !b
  | node i t₀ t₁ => node i t₁.dual t₀.dual

@[simp] theorem dual_leaf (b : Bool) : (leaf b : DecisionTree ι Bool).dual = leaf !b :=
  rfl

@[simp] theorem dual_node (i : ι) (t₀ t₁ : DecisionTree ι Bool) :
    (node i t₀ t₁).dual = node i t₁.dual t₀.dual :=
  rfl

@[simp] theorem dual_dual (t : DecisionTree ι Bool) : t.dual.dual = t := by
  induction t with
  | leaf b => simp
  | node i t₀ t₁ ih₀ ih₁ => simp [ih₀, ih₁]

/-- On `x`, the dual tree outputs the negation of the original tree's output on `¬ x`. -/
@[simp] theorem eval_dual (t : DecisionTree ι Bool) (x : ι → Bool) :
    t.dual.eval x = !t.eval fun i => !x i := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [dual_node, eval_node, ih₀, ih₁]
    cases x i <;> rfl

@[simp] theorem depth_dual (t : DecisionTree ι Bool) : t.dual.depth = t.depth := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ => simp [ih₀, ih₁, max_comm]

/-- On `x`, the dual tree pays the original tree's query costs on `¬ x`. -/
@[simp] theorem weightedCost_dual (t : DecisionTree ι Bool) (w : ι → ℕ) (x : ι → Bool) :
    t.dual.weightedCost w x = t.weightedCost w fun i => !x i := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [dual_node, weightedCost_node, ih₀, ih₁]
    cases x i <;> rfl

/-- On `x`, the dual tree makes as many queries as the original tree on `¬ x`. -/
@[simp] theorem cost_dual (t : DecisionTree ι Bool) (x : ι → Bool) :
    t.dual.cost x = t.cost fun i => !x i :=
  weightedCost_dual t _ x

/-- On `x`, the dual tree queries the variables that the original tree queries on `¬ x`. -/
@[simp] theorem queries_dual [DecidableEq ι] (t : DecisionTree ι Bool) (x : ι → Bool) :
    t.dual.queries x = t.queries fun i => !x i := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [dual_node, queries_node, ih₀, ih₁]
    cases x i <;> rfl

/-- The dual tree computes the dual function `x ↦ ¬ f(¬ x)`. -/
theorem Computes.dual {t : DecisionTree ι Bool} {f : (ι → Bool) → Bool} (ht : t.Computes f) :
    t.dual.Computes fun x => !f fun i => !x i := fun x => by
  rw [eval_dual, ht]

/-- A function and its dual have the same decision tree complexity. -/
theorem complexity_dual [Finite ι] (f : (ι → Bool) → Bool) :
    complexity (fun x => !f fun i => !x i) = complexity f := by
  have key (g : (ι → Bool) → Bool) : complexity (fun x => !g fun i => !x i) ≤ complexity g := by
    obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity g
    exact (complexity_le_depth ht.dual).trans (by rw [depth_dual, hd])
  refine le_antisymm (key f) ?_
  convert key fun x => !f fun i => !x i
  simp only [Bool.not_not]

end Cslib.DecisionTree
