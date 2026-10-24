/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.SearchTree.Basic

/-!
# Search-tree node-visit costs

The cost model counts visits to internal nodes. Empty-child tests, allocation, reconstruction,
order-comparison implementation, and pure client computation are not charged. In particular,
inserting into an empty tree costs zero in this model. These are not RAM instruction counts.

Each traversal below follows exactly the branch decisions of its corresponding operation. Search
and insertion follow the same path; minimum follows left children; successor follows one child
and retains a candidate when descending left. No operation scans both subtrees.

## Main definitions

* `searchVisits`, `minimumVisits`, `successorVisits`: node visits along the selected path.

## Main results

* `searchVisits_le_height`, `minimumVisits_le_height`, `successorVisits_le_height`: shape-dependent
  upper bounds, without any balancing assumption.
* `height_insert_le`: insertion increases height by at most one.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 12][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.SearchTree

variable {α : Type*} [LinearOrder α]

/-- Internal-node visits shared by membership and insertion. -/
def searchVisits (x : α) : BinaryTree α → Nat
  | .nil => 0
  | .node a l r => 1 + if x < a then searchVisits x l else if a < x then searchVisits x r else 0

/-- Internal-node visits of leftmost descent. -/
def minimumVisits : BinaryTree α → Nat
  | .nil => 0
  | .node _ l _ => 1 + minimumVisits l

/-- Internal-node visits of strict successor, including failed searches. -/
def successorVisits (x : α) : BinaryTree α → Nat
  | .nil => 0
  | .node a l r => 1 + if x < a then successorVisits x l else successorVisits x r

/-- Search and insertion visit at most `t.height` internal nodes. -/
theorem searchVisits_le_height (x : α) (t : BinaryTree α) :
    searchVisits x t ≤ t.height := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    simp only [searchVisits, BinaryTree.height]
    split
    · omega
    · split <;> omega

omit [LinearOrder α] in
/-- Leftmost minimum descent visits at most `t.height` internal nodes. -/
theorem minimumVisits_le_height (t : BinaryTree α) : minimumVisits t ≤ t.height := by
  induction t with
  | nil => rfl
  | node a l r il _ =>
    simp only [minimumVisits, BinaryTree.height]
    omega

/-- Successor search visits at most `t.height` internal nodes. -/
theorem successorVisits_le_height (x : α) (t : BinaryTree α) :
    successorVisits x t ≤ t.height := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    simp only [successorVisits, BinaryTree.height]
    split <;> omega

/-- This permits linear height growth; it is not a balancing theorem. -/
theorem height_insert_le (x : α) (t : BinaryTree α) :
    (insert x t).height ≤ t.height + 1 := by
  induction t with
  | nil => simp [insert]
  | node a l r il ir =>
    simp only [insert]
    split
    · simp only [BinaryTree.height]
      omega
    · split <;> simp only [BinaryTree.height] <;> omega

end Cslib.Algorithms.Lean.SearchTree
