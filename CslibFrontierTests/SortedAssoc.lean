/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Data.TreeMap.SortedAssoc

/-!
# Sorted association list examples

Checked examples for the sorted association list model `List.IsSortedAssoc` and its operations
in `Cslib.SortedAssoc`, and for its agreement with `Std.TreeMap`. Ported from the examples of
Jesse Alama's EpsilonEridani development.
-/

namespace CslibFrontierTests.SortedAssoc

open Cslib

example : SortedAssoc.insert 2 20 [(1, 10), (3, 30)] = [(1, 10), (2, 20), (3, 30)] := by decide
example : SortedAssoc.insert 3 31 [(1, 10), (3, 30)] = [(1, 10), (3, 31)] := by decide
example : SortedAssoc.erase 3 [(1, 10), (3, 30)] = [(1, 10)] := by decide
example : List.lookup 3 [(1, 10), (3, 30)] = some 30 := by decide
example : List.lookup 2 [(1, 10), (3, 30)] = none := by decide
example : SortedAssoc.range 2 2 [(1, 10), (2, 20), (3, 30)] = [(2, 20)] := by decide
example : SortedAssoc.range 3 2 [(1, 10), (2, 20), (3, 30)] = [] := by decide
example : SortedAssoc.pred? 3 [(1, 10), (2, 20), (3, 30)] = some (2, 20) := by decide
example : SortedAssoc.succ? 3 [(1, 10), (2, 20), (3, 30)] = none := by decide
example : SortedAssoc.rank 3 [(1, 10), (2, 20), (3, 30)] = 2 := by decide
example : [(1, 10), (2, 20)].IsSortedAssoc := by decide
example : ¬ [(2, 20), (2, 21)].IsSortedAssoc := by decide
example : SortedAssoc.insert 2 "b" [(1, "a"), (3, "c")] = [(1, "a"), (2, "b"), (3, "c")] := by
  decide

/-- A tree map built from a sorted list lists that list; `decide` checks the sortedness. -/
example :
    (Std.TreeMap.ofList [(1, 'a'), (2, 'b'), (3, 'c')] compare).toList =
      [(1, 'a'), (2, 'b'), (3, 'c')] :=
  Std.TreeMap.toList_ofList_of_isSortedAssoc (by decide)

end CslibFrontierTests.SortedAssoc
