/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.BTree.Cost.Erase
public import Complexity.DataStructure.BTree.Cost.Insert
public import Complexity.DataStructure.BTree.Cost.OfSortedList
public import Complexity.DataStructure.BTree.Cost.Range

/-!
# B-tree node-visit cost examples

Checked node-visit counts of the `TimeM` instantiations on concrete trees, evaluated through
their `_def` equations. Ported from the examples of Jesse Alama's EpsilonEridani development.
-/

public section

namespace ComplexityTests.BTreeCost

open Cslib.DataStructure Cslib.DataStructure.BTree
open Cslib.Algorithms.Lean (TimeM)

/-! ### Point queries -/

/-- The empty tree is not visited. -/
example (k : ℕ) : (lookupT k (.leaf : BTree ℕ ℕ)).time = 0 := by
  simp [lookupT_def, lookupM]

/-- A node without keys is visited once before descending into its only child. -/
example (k : ℕ) : (rankT k (.node .leaf [] : BTree ℕ ℕ)).time = 1 := by
  simp [rankT_def, rankM_node_nil, rankM_leaf]

/-- A two-level tree at `t = 2`: lookup of `3` visits the root and one child. -/
example :
    (lookupT 3 (BTree.node (.node .leaf [(1, 1, .leaf)])
      [(2, 2, .node .leaf [(3, 3, .leaf)])] : BTree ℕ ℕ)).time = 2 := by
  simp [lookupT_def, lookupM]

/-! ### Range restriction -/

/-- The tree of the range-restriction examples, with eight entries. -/
def rangeTExample : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (2, "b", .leaf)])
    [(3, "c", .node .leaf [(4, "d", .leaf), (5, "e", .leaf)]),
     (6, "f", .node .leaf [(7, "g", .leaf), (8, "h", .leaf)])]

/-- An interval spanning all three children visits every node. -/
example : (rangeT 2 7 rangeTExample).time = 4 := by
  simp [rangeTExample, rangeT_def, rangeM_node, rangeRestM_cons, rangeRestM_nil, rangeM_leaf]

/-- An interval inside one child visits the root and that child. -/
example : (rangeT 4 5 rangeTExample).time = 2 := by
  simp [rangeTExample, rangeT_def, rangeM_node, rangeRestM_cons, rangeRestM_nil, rangeM_leaf]

/-- An interval above every key visits only the root and its last child. -/
example : (rangeT 9 10 rangeTExample).time = 2 := by
  simp [rangeTExample, rangeT_def, rangeM_node, rangeRestM_cons, rangeRestM_nil, rangeM_leaf]

/-! ### Insertion -/

/-- A two-level tree at `t = 2`: inserting `4` visits the root and its last child, whatever
splitting follows. -/
example :
    (insertT 2 4 4 (BTree.node (.node .leaf [(1, 1, .leaf)])
      [(2, 2, .node .leaf [(3, 3, .leaf)])] : BTree ℕ ℕ)).time = 2 := by
  simp [insertT_def, insertM, insertOrSplitM_node, insertRestM_cons]

/-! ### Erasure -/

/-- Erasing the only key of a one-node tree visits that node only: the root has no sibling. -/
example : (eraseT 2 1 (BTree.node .leaf [(1, 1, .leaf)] : BTree ℕ ℕ)).time = 1 := by
  rw [eraseT_def]
  decide

/-- A two-level tree at `t = 2`: erasing `1` visits the root, the left child, which underflows,
and its right sibling for the repair. -/
example :
    (eraseT 2 1 (BTree.node (.node .leaf [(1, 1, .leaf)])
      [(2, 2, .node .leaf [(3, 3, .leaf)])] : BTree ℕ ℕ)).time = 3 := by
  rw [eraseT_def]
  decide

/-! ### Bulk loading -/

/-- Four entries at `t = 2`: a root over two leaves, three nodes. -/
example : (ofSortedListT 2 [(1, ()), (2, ()), (3, ()), (4, ())]).time = 3 := by
  rw [ofSortedListT_def]
  rfl

/-- Seven entries at `t = 2`: a root over two full leaves, three nodes. -/
example : (ofSortedListT 2 ((List.range' 1 7).map (·, ()))).time = 3 := by
  rw [ofSortedListT_def]
  rfl

end ComplexityTests.BTreeCost
