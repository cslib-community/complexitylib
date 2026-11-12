/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BTree.Comparisons.Insert
public import CslibFrontier.DataStructure.BTree.Comparisons.Range

/-!
# B-tree comparison cost examples
-/

public section

namespace CslibFrontierTests.BTreeComparisons

open Cslib (FreeM)
open Cslib.DataStructure
open Cslib.DataStructure.BTree
open Cslib.Query (LEQuery)

private def exampleTree : BTree ℕ String :=
  BTree.node (BTree.node BTree.leaf [(1, "a", BTree.leaf), (2, "b", BTree.leaf)])
    [(3, "c", BTree.node BTree.leaf [(4, "d", BTree.leaf), (5, "e", BTree.leaf)]),
     (6, "f", BTree.node BTree.leaf [(7, "g", BTree.leaf), (8, "h", BTree.leaf)])]

example :
    (lookupQ 4 (BTree.node (BTree.node BTree.leaf [(1, 1, BTree.leaf)])
      [(2, 2, BTree.node BTree.leaf [(3, 3, BTree.leaf)])] : BTree ℕ ℕ)).countQueries
        orderOracle = 2 := by
  simp [lookupQ_def, lookupM]

example : (rangeQ 2 7 exampleTree).countQueries orderOracle = 16 := by
  simp [exampleTree, rangeQ_def, rangeM_node, rangeM_leaf, rangeRestM_cons, rangeRestM_nil]

example : (rangeQ 9 10 exampleTree).countQueries orderOracle = 8 := by
  simp [exampleTree, rangeQ_def, rangeM_node, rangeM_leaf, rangeRestM_cons, rangeRestM_nil]

example : (insertQ (t := 2) 4 "new" exampleTree).countQueries orderOracle = 5 := by
  simp [exampleTree, insertQ_def, insertM, insertOrSplitM, insertRestM]

def falseOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun _ _ => false

example :
    (lookupQ 4 (BTree.node (BTree.node BTree.leaf [(1, 1, BTree.leaf)])
      [(2, 2, BTree.node BTree.leaf [(3, 3, BTree.leaf)])] : BTree ℕ ℕ)).countQueries
        falseOracle = 2 := by
  simp [lookupQ_def, lookupM, falseOracle]

example : (insertQ (t := 2) 4 "new" exampleTree).eval orderOracle =
    insert (t := 2) 4 "new" exampleTree := by
  exact eval_insertQ

def exampleTreeFull : BTree ℕ String :=
  BTree.node (BTree.node BTree.leaf [(1, "a", BTree.leaf), (2, "b", BTree.leaf)])
    [(3, "c", BTree.node BTree.leaf [(4, "d", BTree.leaf), (5, "e", BTree.leaf)]),
     (6, "f", BTree.node BTree.leaf [(7, "g", BTree.leaf),
       (8, "h", BTree.leaf), (9, "i", BTree.leaf)])]

example : (insertQ (t := 2) 10 "j" exampleTreeFull).countQueries orderOracle = 5 := by
  simp [exampleTreeFull, insertQ_def, insertM, insertOrSplitM, insertRestM]

example : (insertQ (t := 2) 10 "j" exampleTreeFull).countQueries falseOracle = 5 := by
  simp [exampleTreeFull, falseOracle, insertQ_def, insertM, insertOrSplitM, insertRestM]

end CslibFrontierTests.BTreeComparisons
