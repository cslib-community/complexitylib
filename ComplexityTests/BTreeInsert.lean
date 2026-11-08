/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.BTree.TreeMap

/-!
# B-tree insertion and bulk-loading examples

Checked examples for B-tree insertion and bulk loading: a root split at `t = 2`, a child split
absorbed by the root, replacement of an existing key, the groups cut by `ofSortedList` at
`t = 2` and `t = 3`, and agreement with `Std.TreeMap`. Ported from the examples of Jesse
Alama's EpsilonEridani development. The closing client, `insertAll`, builds a map by repeated
insertion and carries well-formedness and the model equation through the fold.
-/

public section

namespace ComplexityTests.BTreeInsert

open Cslib.DataStructure Cslib.DataStructure.BTree

/-! ### Insertion -/

/-- A root split at `t = 2`: a fourth key into a full root raises the height. -/
example :
    (insert 2 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])).height = 2 := by decide

/-- The split root keeps its first two keys on the left and promotes the third. -/
example :
    (insert 2 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])).children.map (·.toList) =
    [[(1, ()), (2, ())], [(4, ())]] := by decide

/-- The tree after the root split is well-formed. -/
example :
    IsWF 2 (insert 2 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])) := by decide

/-- Below the root, a full child splits and the root absorbs its median without growing. -/
example :
    let tr := insert 2 0 "z" (BTree.node (α := ℕ) (β := String)
      (.node .leaf [(1, "a", .leaf), (2, "b", .leaf), (3, "c", .leaf)]) [(5, "e", .node .leaf
        [(6, "f", .leaf)])])
    tr.height = 2 ∧ tr.rootKeys = 2 ∧
      tr.toList = [(0, "z"), (1, "a"), (2, "b"), (3, "c"), (5, "e"), (6, "f")] ∧ IsWF 2 tr := by
  decide

/-- An existing key is replaced in place: no split, no growth. -/
example :
    let tr := insert 2 2 "B" (BTree.node (α := ℕ) (β := String) .leaf
      [(1, "a", .leaf), (2, "b", .leaf), (3, "c", .leaf)])
    tr.height = 1 ∧ tr.toList = [(1, "a"), (2, "B"), (3, "c")] := by decide

/-- At `t = 3` the same root has room for a fourth key. -/
example :
    (insert 3 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])).height = 1 := by decide

/-- Insertion into the empty tree grows a one-key root. -/
example : (insert 2 1 "a" (.leaf : BTree ℕ String)).toList = [(1, "a")] := by decide

/-! ### Bulk loading -/

/-- The empty list builds the empty tree. -/
example : ofSortedList 2 ([] : List (ℕ × Unit)) = .leaf := rfl

/-- `2 * t - 1 = 3` entries: a single root. -/
example : ofSortedList 2 [(1, ()), (2, ()), (3, ())] =
    .node .leaf [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)] := rfl

/-- Four entries: the look ahead cuts a first group of `t - 1 = 1`. -/
example : ofSortedList 2 [(1, ()), (2, ()), (3, ()), (4, ())] =
    .node (.node .leaf [(1, (), .leaf)])
      [(2, (), .node .leaf [(3, (), .leaf), (4, (), .leaf)])] := rfl

/-- Seven entries: two groups of three, and the key `4` moves up. -/
example : ofSortedList 2 ((List.range' 1 7).map (·, ())) =
    .node (.node .leaf [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])
      [(4, (), .node .leaf [(5, (), .leaf), (6, (), .leaf), (7, (), .leaf)])] := rfl

/-- At `t = 3`, six entries: a first group of `t - 1 = 2`. -/
example : ofSortedList 3 ((List.range' 1 6).map (·, ())) =
    .node (.node .leaf [(1, (), .leaf), (2, (), .leaf)])
      [(3, (), .node .leaf [(4, (), .leaf), (5, (), .leaf), (6, (), .leaf)])] := rfl

/-- Below `2` the loader uses minimum degree `2`. -/
example : ofSortedList 0 ((List.range' 1 7).map (·, ())) =
    ofSortedList 2 ((List.range' 1 7).map (·, ())) := rfl

/-- An unsorted list keeps its order. -/
example : (ofSortedList 2 [(3, ()), (1, ()), (2, ()), (5, ()), (4, ())]).toList =
    [(3, ()), (1, ()), (2, ()), (5, ()), (4, ())] := by decide

/-- The empty tree is well-formed. -/
example : isWF 2 (ofSortedList 2 ([] : List (ℕ × Unit))) = true := by decide

/-- Four entries at `t = 2`: a well-formed tree of two levels. -/
example : isWF 2 (ofSortedList 2 [(1, ()), (2, ()), (3, ()), (4, ())]) = true := by decide

/-- Twenty entries at `t = 2`: three levels, well-formed. -/
example : isWF 2 (ofSortedList 2 ((List.range' 1 20).map (·, ()))) = true := by decide

example : (ofSortedList 2 ((List.range' 1 20).map (·, ()))).height = 3 := by decide

/-- Twenty entries at `t = 3`: well-formed. -/
example : isWF 3 (ofSortedList 3 ((List.range' 1 20).map (·, ()))) = true := by decide

/-! ### Agreement with `Std.TreeMap` -/

/-- Four entries at `t = 2`: the same entries as the tree map. -/
example : (ofSortedList 2 [(1, 'a'), (2, 'b'), (3, 'c'), (4, 'd')]).toList =
    (Std.TreeMap.ofList [(1, 'a'), (2, 'b'), (3, 'c'), (4, 'd')] compare).toList :=
  toList_ofSortedList_eq_treeMap 2 (by decide)

/-! ### A client: building a map by repeated insertion -/

/-- Insert the entries of a list into a tree, left to right. -/
def insertAll (t : ℕ) (tr : BTree ℕ String) (l : List (ℕ × String)) : BTree ℕ String :=
  l.foldl (fun tr (k, v) => insert t k v tr) tr

/-- Repeated insertion keeps a tree well-formed. -/
theorem isWF_insertAll {t : ℕ} {tr : BTree ℕ String} (h : IsWF t tr) (l : List (ℕ × String)) :
    IsWF t (insertAll t tr l) := by
  induction l generalizing tr with
  | nil => exact h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    exact ih (h.insert k v)

/-- Repeated insertion acts on the entries as repeated insert-or-replace in the model. -/
theorem toList_insertAll {t : ℕ} {tr : BTree ℕ String} (h : IsWF t tr) (l : List (ℕ × String)) :
    (insertAll t tr l).toList =
      l.foldl (fun acc (k, v) => Cslib.SortedAssoc.insert k v acc) tr.toList := by
  induction l generalizing tr with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [insertAll, List.foldl_cons] at ih ⊢
    rw [ih (h.insert k v), toList_insert h]

/-- Unsorted input with a repeated key: the result is sorted, the later value wins, and the tree
is a well-formed two-level 2-3-4 tree. -/
example :
    let tr := insertAll 2 .leaf [(5, "e"), (1, "a"), (3, "c"), (2, "b"), (4, "d"), (3, "C")]
    tr.toList = [(1, "a"), (2, "b"), (3, "C"), (4, "d"), (5, "e")] ∧ tr.height = 2 ∧
      IsWF 2 tr := by
  decide

end ComplexityTests.BTreeInsert
