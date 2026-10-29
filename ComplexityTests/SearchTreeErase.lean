/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.SearchTree.Erase
public import ComplexityTests.SearchTree

/-!
# Worked search-tree deletion examples

Delete keys from the balanced-looking and the right-spine trees of `ComplexityTests.SearchTree`.
Deleting the root of the height-three tree promotes its successor from the right subtree; deleting
from the spine walks the whole search path. Absent keys leave the tree unchanged. All computation
is checked by the kernel, with no `native_decide`.
-/

@[expose] public section

namespace ComplexityTests.SearchTreeErase

open Cslib.Algorithms.Lean.SearchTree ComplexityTests.SearchTree

def medianFirst : BinaryTree Nat := build [4, 2, 6, 1, 3, 5, 7]
def sortedFirst : BinaryTree Nat := build [1, 2, 3, 4, 5, 6, 7]

-- Deleting the root replaces it by its successor, the leftmost key of the right subtree.
example :
    erase 4 medianFirst =
        .node 5 (.node 2 (.node 1 .nil .nil) (.node 3 .nil .nil))
          (.node 6 .nil (.node 7 .nil .nil)) ∧
      elements (erase 4 medianFirst) = {1, 2, 3, 5, 6, 7} ∧
      elements (erase 4 medianFirst) = (elements medianFirst).erase 4 ∧
      Ordered (erase 4 medianFirst) ∧
      eraseVisits 4 medianFirst = 3 :=
  ⟨rfl, by decide, elements_erase (ordered_build _) 4, ordered_erase (ordered_build _) 4, rfl⟩

-- On the right spine, deletion walks the search path plus one successor visit; a leaf or a node
-- without a right subtree is spliced out directly.
example :
    eraseVisits 4 sortedFirst = 5 ∧
      eraseVisits 7 sortedFirst = 7 ∧
      (erase 4 sortedFirst).height = 6 ∧
      (erase 7 sortedFirst).height = 6 ∧
      contains 4 (erase 4 sortedFirst) = false ∧
      contains 5 (erase 4 sortedFirst) = true ∧
      erase 1 medianFirst =
        .node 4 (.node 2 .nil (.node 3 .nil .nil))
          (.node 6 (.node 5 .nil .nil) (.node 7 .nil .nil)) ∧
      erase 5 (build [5]) = .nil ∧
      erase 5 (build [5, 3]) = .node 3 .nil .nil :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Deleting an absent key preserves shape as well as contents, and deletion followed by reinsertion
-- restores the set without necessarily restoring the tree shape.
example :
    erase 8 medianFirst = medianFirst ∧
      erase 0 (.nil : BinaryTree Nat) = .nil ∧
      eraseVisits 8 sortedFirst = 7 ∧
      elements (insert 4 (erase 4 medianFirst)) = elements medianFirst ∧
      insert 4 (erase 4 medianFirst) ≠ medianFirst :=
  ⟨erase_eq_of_notMem (by decide), rfl, rfl, by decide, by decide⟩

/--
info: 'Cslib.Algorithms.Lean.SearchTree.eraseVisits_le_height' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.eraseVisits_le_height
/--
info: 'Cslib.Algorithms.Lean.SearchTree.height_erase_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.height_erase_le

end ComplexityTests.SearchTreeErase
