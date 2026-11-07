/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (tests)

import Complexity.DataStructure.FusionTree.Tree

/-! Child-height clients need only the functional tree module, without RAM machinery. -/

open Cslib.DataStructure.FusionTree

-- The membership form applies to children of any shape, without a validity invariant.
example (t : Tree) : t.height < (Tree.node 0 [.leaf [], t]).height :=
  Tree.height_lt_node_of_mem (by simp)

-- The indexed form also works when a node has a single child, which is not a valid search node.
example (m : ℕ) (t : Tree) : t.height < (Tree.node m [t]).height :=
  Tree.height_getElem_lt_node m [t] ⟨0, by simp⟩
