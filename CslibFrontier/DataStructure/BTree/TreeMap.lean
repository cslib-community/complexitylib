/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.OfSortedList
public import CslibFrontier.Foundations.Data.TreeMap.SortedAssoc

/-!
# Bulk loading and `Std.TreeMap`

The output of bulk loading agrees with Lean core's `Std.TreeMap`, ordered by the `compare` of the
linear order: on a sorted list `l`, the entries of `Std.TreeMap.ofList l compare` are `l` itself
(`Std.TreeMap.toList_ofList_of_isSortedAssoc`), and so are those of `ofSortedList t l`
(`toList_ofSortedList`).

## Main results

* `toList_ofSortedList_eq_treeMap`: bulk loading a sorted list gives the entries of the tree map
  built from it, for every minimum degree.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/TreeMap.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/TreeMap.lean).
-/

public section

variable {α β : Type} [LinearOrder α]

namespace Cslib.DataStructure.BTree

/-- Bulk loading a sorted list gives the entries of Lean core's tree map built from it: an output
equality, for every minimum degree. -/
theorem toList_ofSortedList_eq_treeMap (t : ℕ) {l : List (α × β)} (h : l.IsSortedAssoc) :
    (ofSortedList t l).toList = (Std.TreeMap.ofList l compare).toList :=
  (toList_ofSortedList t l).trans (Std.TreeMap.toList_ofList_of_isSortedAssoc h).symm

end Cslib.DataStructure.BTree
