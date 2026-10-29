/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic

/-!
# Query costs of decision trees

`weightedCost` charges each query made on an input, including repeated queries. `weightedDepth`
is the largest cost of a structural root-to-leaf path. It bounds the actual cost, but equality
need not hold: repeated variables can make a structural path unreachable. Costs are natural
numbers and may be zero. Unit costs give the actual query count `cost` and the usual `depth`.

These quantities support composition when different queried bits have different computation
costs; no second notion of minimum decision-tree complexity is introduced.

## Main definitions

* `Cslib.DecisionTree.weightedCost`: the cost of the queries executed on one input.
* `Cslib.DecisionTree.cost`: the number of queries executed on one input.
* `Cslib.DecisionTree.weightedDepth`: the maximum structural path cost.

## Main results

* `Cslib.DecisionTree.weightedCost_le_weightedDepth`: structural cost bounds actual cost.
* `Cslib.DecisionTree.weightedDepth_le_depth_mul`: a uniform query bound gives a depth bound.
-/

public section

namespace Cslib.DecisionTree

variable {ι κ β : Type*}

/-- The total cost of queries executed on an input, counting repeated queries each time. -/
@[expose] def weightedCost : DecisionTree ι β → (ι → ℕ) → (ι → Bool) → ℕ
  | leaf _, _, _ => 0
  | node i left right, w, x =>
      cond (x i) (right.weightedCost w x) (left.weightedCost w x) + w i

/-- The number of queries executed on an input, including repeated queries. -/
@[expose] def cost (t : DecisionTree ι β) (x : ι → Bool) : ℕ :=
  t.weightedCost (fun _ => 1) x

/-- The maximum cost of a structural root-to-leaf path, including unreachable paths. -/
@[expose] def weightedDepth : DecisionTree ι β → (ι → ℕ) → ℕ
  | leaf _, _ => 0
  | node i left right, w => max (left.weightedDepth w) (right.weightedDepth w) + w i

@[simp] theorem weightedCost_leaf (b : β) (w : ι → ℕ) (x : ι → Bool) :
    (leaf b).weightedCost w x = 0 := rfl

@[simp] theorem weightedCost_node (i : ι) (left right : DecisionTree ι β)
    (w : ι → ℕ) (x : ι → Bool) :
    (node i left right).weightedCost w x =
      cond (x i) (right.weightedCost w x) (left.weightedCost w x) + w i := rfl

@[simp] theorem cost_leaf (b : β) (x : ι → Bool) : (leaf b).cost x = 0 := rfl

@[simp] theorem cost_node (i : ι) (left right : DecisionTree ι β) (x : ι → Bool) :
    (node i left right).cost x = cond (x i) (right.cost x) (left.cost x) + 1 := rfl

@[simp] theorem weightedDepth_leaf (b : β) (w : ι → ℕ) :
    (leaf b).weightedDepth w = 0 := rfl

@[simp] theorem weightedDepth_node (i : ι) (left right : DecisionTree ι β) (w : ι → ℕ) :
    (node i left right).weightedDepth w =
      max (left.weightedDepth w) (right.weightedDepth w) + w i := rfl

/-- Increasing query costs cannot decrease structural path cost. -/
theorem weightedDepth_mono (t : DecisionTree ι β) {w v : ι → ℕ} (h : ∀ i, w i ≤ v i) :
    t.weightedDepth w ≤ t.weightedDepth v := by
  induction t with
  | leaf => exact le_rfl
  | node i left right ihl ihr =>
    exact Nat.add_le_add (max_le_max ihl ihr) (h i)

/-- A constant query cost multiplies the ordinary structural depth. -/
@[simp] theorem weightedDepth_const (t : DecisionTree ι β) (c : ℕ) :
    t.weightedDepth (fun _ => c) = t.depth * c := by
  induction t with
  | leaf => simp
  | node i left right ihl ihr =>
    simp only [weightedDepth_node, depth_node, ihl, ihr, Nat.add_mul, Nat.one_mul]
    rw [max_mul]

/-- Charging at most `d` per query costs at most `depth * d` on every structural path. -/
theorem weightedDepth_le_depth_mul (t : DecisionTree ι β) {w : ι → ℕ} {d : ℕ}
    (h : ∀ i, w i ≤ d) : t.weightedDepth w ≤ t.depth * d :=
  (t.weightedDepth_mono h).trans_eq (t.weightedDepth_const d)

/-- The actual path cost is bounded by the largest structural path cost. -/
theorem weightedCost_le_weightedDepth (t : DecisionTree ι β) (w : ι → ℕ) (x : ι → Bool) :
    t.weightedCost w x ≤ t.weightedDepth w := by
  induction t with
  | leaf => exact le_rfl
  | node i left right ihl ihr =>
    simp only [weightedCost_node, weightedDepth_node]
    cases x i
    · exact Nat.add_le_add_right (ihl.trans (le_max_left _ _)) _
    · exact Nat.add_le_add_right (ihr.trans (le_max_right _ _)) _

/-- The number of queries executed on any input is at most the structural depth. -/
theorem cost_le_depth (t : DecisionTree ι β) (x : ι → Bool) : t.cost x ≤ t.depth := by
  simpa only [cost, weightedDepth_const, Nat.mul_one] using
    t.weightedCost_le_weightedDepth (fun _ => 1) x

/-- Relabelling queries pulls their costs back along the relabelling function. -/
@[simp] theorem weightedDepth_mapQueries (f : ι → κ) (t : DecisionTree ι β) (w : κ → ℕ) :
    (t.mapQueries f).weightedDepth w = t.weightedDepth (w ∘ f) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, ihl, ihr]

/-- Relabelling queries pulls back both the oracle and its query costs. -/
@[simp] theorem weightedCost_mapQueries (f : ι → κ) (t : DecisionTree ι β)
    (w : κ → ℕ) (x : κ → Bool) :
    (t.mapQueries f).weightedCost w x = t.weightedCost (w ∘ f) (x ∘ f) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, ihl, ihr]

end Cslib.DecisionTree
