/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BTree.Height

/-!
# B-tree well-formedness and height examples

Checked examples for `Cslib.DataStructure.BTree`: concrete trees at `t = 2` and `t = 3` that
`decide` accepts or rejects for occupancy, equal leaf depth and key order, and an instance of
the height bound. Ported from the examples of Jesse Alama's EpsilonEridani development.
-/

namespace CslibFrontierTests.BTree

open Cslib.DataStructure Cslib.DataStructure.BTree

/-! ### Well-formedness -/

/-- A root with one key and two leaf children is a well-formed 2-3-4 tree. -/
example : IsWF 2 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf)]) := by decide

/-- A node whose children differ in height is not well-formed for any `t`. -/
example (t : ℕ) :
    ¬ IsWF t (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf)]) [(1, (), .leaf)]) :=
  fun h => absurd h.balanced (by decide)

/-- Children of different heights violate equal leaf depth. -/
example :
    ¬ IsWF 2 (BTree.node (α := ℕ) (β := Unit) (.node .leaf [(0, (), .leaf)]) [(1, (), .leaf)]) := by
  decide

/-- A root with two keys and three leaf children is well-formed at `t = 3`. -/
example : IsWF 3 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf), (2, "b", .leaf)]) := by
  decide

/-- Occupancy depends on `t`: one-key children are full enough at `t = 2` and too sparse at
`t = 3`, where a non-root node needs at least two keys. -/
example :
    IsWF 2 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf)]) [(5, (), .node .leaf [(6, (), .leaf)])]) ∧
    ¬ IsWF 3 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf)]) [(5, (), .node .leaf [(6, (), .leaf)])]) := by decide

/-- The minimum degree is at least `2`, so even the empty tree is not well-formed at `t = 1`. -/
example : ¬ IsWF 1 (BTree.leaf : BTree ℕ Unit) := by decide

/-- At `t = 0` a root with one key is not well-formed. -/
example : ¬ IsWF 0 (BTree.node (α := ℕ) (β := Unit) .leaf [(1, (), .leaf)]) := by decide

/-- A non-empty root needs at least one key. -/
example : ¬ IsWF 2 (BTree.node (α := ℕ) (β := Unit) .leaf []) := by decide

/-- A node with no keys and a leaf child has height `1`. -/
example : (BTree.node (α := ℕ) (β := Unit) .leaf []).height = 1 := by decide

/-- Keys out of order are not well-formed. -/
example : ¬ IsWF 2 (BTree.node (α := ℕ) (β := Unit) .leaf [(2, (), .leaf), (1, (), .leaf)]) := by
  decide

/-! ### Size and height -/

/-- The bound at a root with one key and two leaf children: height `1`, size `1`. -/
example :
    (BTree.node (α := ℕ) (β := Unit) .leaf [(1, (), .leaf)]).height ≤
      Nat.log 2 (((BTree.node (α := ℕ) (β := Unit) .leaf [(1, (), .leaf)]).size + 1) / 2) + 1 := by
  decide

end CslibFrontierTests.BTree
