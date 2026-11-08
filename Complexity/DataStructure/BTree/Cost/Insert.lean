/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.DataStructure.BTree.Cost.Query
public import Complexity.DataStructure.BTree.Insert

/-!
# Node-visit cost of B-tree insertion

`insertT` instantiates `insertM` at `TimeM ℕ` with the free comparator `leT` and
`visit := tick 1`, in the node-visit model of `Cslib.DataStructure.BTree.Cost.Query`.

Insertion visits each node of its search path once, on the way down; the splits on the way back
up and the new root grown on overflow cost no visits, because they only rebuild nodes already in
hand. The scan of a node's triples descends into at most one child, and visits nothing when it
defers to the child before them, so a node and the single child it descends into account for
every visit.

## Main definitions

* `insertT`: the instrumented insertion.

## Main results

* `ret_insertT`: the value of `insertT` is `insert`.
* `time_insertOrSplitM_le`: insertion into a subtree visits at most its height in nodes, on every
  tree.
* `time_insertT`, `time_insertT_le_log`: at most `height` visits, and with `IsWF.height_le_log`.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Cost/Insert.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Cost/Insert.lean).
-/

public section

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace Cslib.DataStructure.BTree

section NodeVisits

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α} {v : β} {tr : BTree α β}

/-- Insertion, charging one tick per node visited. -/
def insertT (t : ℕ) (k : α) (v : β) (tr : BTree α β) : TimeM ℕ (BTree α β) :=
  insertM t leT (tick 1) k v tr

/-- `insertT` is `insertM` with the free comparator and one tick per visit. -/
theorem insertT_def : insertT t k v tr = insertM t leT (tick 1) k v tr := (rfl)

/-- The value of `insertT` is `insert`. -/
@[simp] theorem ret_insertT : (insertT t k v tr).ret = insert t k v tr := by
  simpa only [insert_def, insertT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_insertM t leT (tick 1) k v tr)

/-- Insertion visits exactly the nodes that the bottom-up insertion into the tree visits: growing
a new root costs nothing. -/
theorem time_insertT_eq :
    (insertT t k v tr).time = (insertOrSplitM t leT (tick 1) k v tr).time := by
  simp [insertT, insertM]

/-- Insertion into the empty tree visits nothing. -/
@[simp] theorem time_insertT_leaf : (insertT t k v (.leaf : BTree α β)).time = 0 := by
  simp [insertT, insertM]

/-- When the scan of a node's triples defers to the child before them, it has visited nothing:
the scan descends into a child only past a key below the query, and then returns new triples. -/
theorem time_insertRestM_eq_zero_of_ret_eq_none {rest : List (Triple α β)}
    (h : (insertRestM t leT (tick 1) k v rest).ret = none) :
    (insertRestM t leT (tick 1) k v rest).time = 0 := by
  match rest with
  | [] => simp
  | (k', v', c) :: rest =>
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k <;> simp [insertRestM_cons, hk, hk']
    · simp only [insertRestM_cons, hk, decide_false, TimeM.ret_bind, TimeM.ret_pure,
        Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> simp at h

mutual
/-- The bottom-up insertion into a subtree visits at most `height` nodes. -/
theorem time_insertOrSplitM_le (tr : BTree α β) :
    (insertOrSplitM t leT (tick 1) k v tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp
  | .node first rest =>
    have h₁ := time_insertOrSplitM_le first
    have h₂ := time_insertRestM_le rest
    have h₃ := time_insertRestM_eq_zero_of_ret_eq_none (t := t) (k := k) (v := v) (rest := rest)
    have e : first.height + 1 ≤ (node first rest).height := height_first_succ_le
    rw [height_node] at e ⊢
    simp only [insertOrSplitM_node, TimeM.time_bind, TimeM.time_tick]
    split <;> simp_all <;> omega
termination_by sizeOf tr

/-- The insertion among the triples of a node visits at most as many nodes as the height of
the tallest of their children, `heightRest rest - 1`. -/
theorem time_insertRestM_le (rest : List (Triple α β)) :
    (insertRestM t leT (tick 1) k v rest).time ≤ heightRest rest - 1 := by
  match rest with
  | [] => simp
  | (k', v', c) :: rest =>
    have h₁ := time_insertOrSplitM_le c
    have h₂ := time_insertRestM_le rest
    have h₃ := time_insertRestM_eq_zero_of_ret_eq_none (t := t) (k := k) (v := v) (rest := rest)
    rw [heightRest_cons]
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k <;> simp [insertRestM_cons, hk, hk']
    · simp only [insertRestM_cons, hk, leT, decide_false, pure_bind, Bool.false_eq_true,
        ↓reduceIte, TimeM.time_bind]
      split <;> simp_all <;> omega
termination_by sizeOf rest
end

/-- Insertion visits at most `height` nodes. -/
theorem time_insertT : (insertT t k v tr).time ≤ tr.height := by
  rw [time_insertT_eq]
  exact time_insertOrSplitM_le tr

/-- Insertion into a well-formed tree visits logarithmically many nodes. -/
theorem time_insertT_le_log (h : IsWF t tr) :
    (insertT t k v tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  time_insertT.trans h.height_le_log

end NodeVisits

end Cslib.DataStructure.BTree
