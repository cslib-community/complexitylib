/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BTree.MinMax
public import CslibFrontier.DataStructure.BTree.PredSucc
public import CslibFrontier.DataStructure.BTree.Range
public import CslibFrontier.DataStructure.BTree.Rank

/-!
# B-tree query examples

Checked examples for the B-tree point and range queries: lookup, minimum, maximum, strict
predecessor and successor, closed-interval range restriction and rank, on well-formed trees
and on sorted trees with zero-key nodes. Ported from the examples of Jesse Alama's
EpsilonEridani development.
-/

public section

namespace CslibFrontierTests.BTreeQuery

open Cslib.DataStructure Cslib.DataStructure.BTree

/-! ### Lookup -/

/-- Sorted but not well-formed: a two-level tree whose child has no keys. Lookup still agrees
with the model, which is what `lookup_eq_of_isSortedAssoc` promises. -/
example : lookup 1 (BTree.node (α := ℕ) (β := String) (.node .leaf []) [(1, "a", .leaf)]) =
    some "a" := by simp

example : lookup 2 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf), (3, "c", .leaf)]) =
    none := by simp

example : slot 2 ([(1, "a", .leaf), (3, "c", .leaf)] : List (ℕ × String × BTree ℕ String)) = 1 := by
  decide

example : contains 3 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf), (3, "c", .leaf)]) =
    true := by simp

/-! ### Minimum and maximum -/

-- Examples exercise both descent and fallback, including nodes with no keys.
example : min? (BTree.leaf : BTree ℕ String) = none := by decide

example : max? (BTree.leaf : BTree ℕ String) = none := by simp

example : min? (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = some (1, "a") := by decide

example : max? (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = some (3, "c") := by simp

example : min? (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (1, "a") := by decide

example : max? (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (5, "e") := by simp

example : min? (BTree.node (α := ℕ) (β := String) (.node .leaf []) []) = none := by decide

example : max? (BTree.node (α := ℕ) (β := String) (.node .leaf []) []) = none := by simp

example : min? (BTree.node (α := ℕ) (β := String) (.node .leaf [])
    [(3, "c", .node .leaf [])]) = some (3, "c") := by decide

example : max? (BTree.node (α := ℕ) (β := String) (.node .leaf [])
    [(3, "c", .node .leaf [])]) = some (3, "c") := by simp

/-! ### Predecessor and successor -/

-- Examples cover strictness at present keys, gaps, boundary failure, descent and fallback.
example : pred? 2 (.leaf : BTree ℕ String) = none := by simp

example : succ? 2 (.leaf : BTree ℕ String) = none := by simp

example : pred? 3 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf), (5, "e", .leaf)]) = some (1, "a") := by simp

example : succ? 3 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf), (5, "e", .leaf)]) = some (5, "e") := by simp

example : pred? 4 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf), (5, "e", .leaf)]) = some (3, "c") := by simp

example : succ? 4 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf), (5, "e", .leaf)]) = some (5, "e") := by simp

example : pred? 1 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = none := by simp

example : succ? 3 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = none := by simp

example : pred? 6 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = some (3, "c") := by simp

example : succ? 0 (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = some (1, "a") := by simp

-- At an interior key, strict queries search its left and right children respectively.
example : pred? 3 (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (1, "a") := by simp

example : succ? 3 (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (5, "e") := by simp

-- The root separator wins when the chosen child's query fails.
example : pred? 5 (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (3, "c") := by simp

example : succ? 1 (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (3, "c") := by simp

-- A deeper candidate takes priority over the root separator.
example : pred? 6 (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (5, "e") := by simp

example : succ? 0 (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (1, "a") := by simp

-- Sorted trees with zero-key nodes need no occupancy hypothesis.
example : pred? 4 (BTree.node (α := ℕ) (β := String) (.node .leaf [])
    [(3, "c", .node .leaf [])]) = some (3, "c") := by simp

example : succ? 2 (BTree.node (α := ℕ) (β := String) (.node .leaf [])
    [(3, "c", .node .leaf [])]) = some (3, "c") := by simp

example : pred? 2 (BTree.node (α := ℕ) (β := String) (.node .leaf []) []) = none := by simp

example : succ? 2 (BTree.node (α := ℕ) (β := String) (.node .leaf []) []) = none := by simp

/-! ### Range restriction -/

/-- A well-formed tree of height two at `t = 2` and `t = 3`, with eight entries. -/
def rangeExample : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (2, "b", .leaf)])
    [(3, "c", .node .leaf [(4, "d", .leaf), (5, "e", .leaf)]),
     (6, "f", .node .leaf [(7, "g", .leaf), (8, "h", .leaf)])]

example : IsWF 2 rangeExample := by decide

example : IsWF 3 rangeExample := by decide

-- The interval includes entries from all three children and both root separators.
example : range 2 7 rangeExample =
    [(2, "b"), (3, "c"), (4, "d"), (5, "e"), (6, "f"), (7, "g")] := by
  simp [rangeExample]

example : range 7 2 rangeExample = [] := by simp [rangeExample]

example : range 3 3 rangeExample = [(3, "c")] := by simp [rangeExample]

example : range 0 0 rangeExample = [] := by simp [rangeExample]

example : range 9 10 rangeExample = [] := by simp [rangeExample]

-- Zero-key nodes are permitted by the query, even though they violate root occupancy.
example : range 1 2 (.node (.node .leaf [(1, "a", .leaf)]) []) = [(1, "a")] := by simp

/-! ### Rank -/

/-- A well-formed tree of height two at `t = 2` and `t = 3`, with odd keys from `1` to `15`. -/
def rankExample : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (3, "c", .leaf)])
    [(5, "e", .node .leaf [(7, "g", .leaf), (9, "i", .leaf)]),
     (11, "k", .node .leaf [(13, "m", .leaf), (15, "o", .leaf)])]

example : IsWF 2 rankExample := by decide

example : IsWF 3 rankExample := by decide

-- Equal root separators are excluded, while all entries of earlier children are counted.
example : rank 5 rankExample = 2 := by simp [rankExample, size]

example : rank 11 rankExample = 5 := by simp [rankExample, size]

-- Search in each child, including equality at a child key and a gap between keys.
example : rank 3 rankExample = 1 := by simp [rankExample, size]

example : rank 8 rankExample = 4 := by simp [rankExample, size]

example : rank 15 rankExample = 7 := by simp [rankExample, size]

example : rank 0 rankExample = 0 := by simp [rankExample]

example : rank 16 rankExample = 8 := by simp [rankExample, size]

example : rank 2 (.leaf : BTree ℕ String) = 0 := by simp

-- Sortedness suffices even for zero-key nodes, which need not satisfy occupancy.
example : rank 2 (.node (.node .leaf [(1, "a", .leaf)]) []) = 1 := by simp

end CslibFrontierTests.BTreeQuery
