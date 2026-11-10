/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BTree.Erase.MinMax

/-!
# B-tree erasure examples

Checked examples for B-tree erasure: borrowing from a sibling, merging, a root collapse,
erasure at an interior key, and erasure of the minimum and maximum. Ported from the examples
of Jesse Alama's EpsilonEridani development.
-/

namespace CslibFrontierTests.BTreeErase

open Cslib.DataStructure Cslib.DataStructure.BTree

/-! ### Erasure -/

/-- A root collapse at `t = 2`: erasing the only root key merges its two children. -/
example :
    (erase 2 2 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(1, (), .leaf)]) [(2, (), .node .leaf [(3, (), .leaf)])])).height = 1 := by
  decide

/-- After the collapse the tree is well-formed and holds the remaining keys. -/
example :
    let tr := erase 2 2 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(1, (), .leaf)]) [(2, (), .node .leaf [(3, (), .leaf)])])
    tr.toList = [(1, ()), (3, ())] ∧ IsWF 2 tr := by decide

/-- An interior key is replaced by its successor, and the child it came from, now empty, borrows
from its full sibling by merging and re-splitting: the height and the root key count stay. -/
example :
    let tr := erase 2 2 (BTree.node (α := ℕ) (β := String)
      (.node .leaf [(1, "a", .leaf)])
      [(2, "b", .node .leaf [(3, "c", .leaf)]), (4, "d", .node .leaf [(5, "e", .leaf),
        (6, "f", .leaf), (7, "g", .leaf)])])
    tr.height = 2 ∧ tr.rootKeys = 2 ∧
      tr.toList = [(1, "a"), (3, "c"), (4, "d"), (5, "e"), (6, "f"), (7, "g")] ∧ IsWF 2 tr := by
  decide

/-- Erasing the only key of a middle child merges it with its right sibling. -/
example :
    let tr := erase 2 3 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(1, (), .leaf)]) [(2, (), .node .leaf [(3, (), .leaf)]),
        (4, (), .node .leaf [(5, (), .leaf)])])
    tr.rootKeys = 1 ∧ tr.toList = [(1, ()), (2, ()), (4, ()), (5, ())] ∧ IsWF 2 tr := by
  decide

/-- Erasing the only key of the last child merges it into its left sibling. -/
example :
    let tr := erase 2 5 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(1, (), .leaf)]) [(2, (), .node .leaf [(3, (), .leaf)]),
        (4, (), .node .leaf [(5, (), .leaf)])])
    tr.rootKeys = 1 ∧ tr.children.map (·.toList) = [[(1, ())], [(3, ()), (4, ())]] ∧
      IsWF 2 tr := by
  decide

/-- An absent key leaves the entries in place. -/
example :
    (erase 2 7 (BTree.node (α := ℕ) (β := Unit) .leaf [(1, (), .leaf), (3, (), .leaf)])).toList =
      [(1, ()), (3, ())] := by decide

/-- At `t = 3` a three-key leaf-level child is erased from without repair. -/
example :
    let tr := erase 3 1 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf), (1, (), .leaf), (2, (), .leaf)])
      [(5, (), .node .leaf [(6, (), .leaf), (7, (), .leaf)])])
    tr.toList = [(0, ()), (2, ()), (5, ()), (6, ()), (7, ())] ∧ IsWF 3 tr := by decide

/-! ### Erasing the minimum and maximum -/

/-- `eraseMin?` returns the least entry and the rest. -/
example :
    ((eraseMin? 2 (BTree.node (α := ℕ) (β := String) .leaf
      [(1, "a", .leaf), (3, "c", .leaf)])).map fun p => (p.1, p.2.toList)) =
      some ((1, "a"), [(3, "c")]) := by decide

end CslibFrontierTests.BTreeErase
