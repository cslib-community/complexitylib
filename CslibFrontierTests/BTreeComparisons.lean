import CslibFrontier.DataStructure.BTree.Comparisons.Insert
import CslibFrontier.DataStructure.BTree.Comparisons.Range

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
  simp [lookupQ, lookupM]

example : (rangeQ 2 7 exampleTree).countQueries orderOracle = 16 := by
  simp [exampleTree, rangeQ, rangeM, rangeRestM]

example : (rangeQ 9 10 exampleTree).countQueries orderOracle = 8 := by
  simp [exampleTree, rangeQ, rangeM, rangeRestM]

example : (insertQ (t := 2) 4 "new" exampleTree).countQueries orderOracle = 5 := by
  simp [exampleTree, insertQ, insertM, insertOrSplitM, insertRestM]

private def falseOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun _ _ => false

example :
    (lookupQ 4 (BTree.node (BTree.node BTree.leaf [(1, 1, BTree.leaf)])
      [(2, 2, BTree.node BTree.leaf [(3, 3, BTree.leaf)])] : BTree ℕ ℕ)).countQueries
        falseOracle = 2 := by
  simp [lookupQ, lookupM, falseOracle]

end CslibFrontierTests.BTreeComparisons
