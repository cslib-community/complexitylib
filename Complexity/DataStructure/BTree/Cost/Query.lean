/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.DataStructure.BTree.Height
public import Complexity.DataStructure.BTree.MinMax
public import Complexity.DataStructure.BTree.PredSucc
public import Complexity.DataStructure.BTree.Rank
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Node-visit costs of B-tree point queries

The point queries of `Cslib.DataStructure.BTree` are defined once over a monad, with a comparator
and a node-visit action. This file instantiates them at `TimeM ℕ` with the free comparator `leT`
and `visit := tick 1`. The transfer lemmas `Cslib.IsMonadHom.map_lookupM` and its siblings,
stated beside each polymorphic definition in the pattern of CSLib's
`Cslib.IsMonadHom.map_listMergeSortM`, applied to `TimeM.isMonadHom_pure_ret`, give the value of
each instrumented query as the pure query.

The cost model counts node visits: `visit := tick 1` in CSLib's `TimeM`, so the time of a
run is the number of nodes it visits. A visit is a descent into, or an inspection of, a node
other than the empty leaf. Empty-child tests, allocation, the rebuilding of nodes on the return
path, comparisons (`leT` is free) and client computation are not charged, as in
`Cslib.DataStructure.SearchTree.searchVisits`. These are node-visit counts, not machine
instruction counts. The tick placement is part of the polymorphic definition, and the transfer
lemma shows the value of each instrumented run is the pure operation.

Each query visits at most one node per level, so the time is at most `height` on every tree,
well-formed or not, because `height` is the longest root-to-leaf path.

## Main definitions

* `leT`: the free comparator of a linear order in `TimeM ℕ`.
* `lookupT`, `containsT`, `minT`, `maxT`, `predT`, `succT`, `rankT`: the instrumented queries.

## Main results

* `ret_lookupT`, `ret_rankT`: the value of each instrumented query is the pure query; likewise
  for the other queries.
* `time_lookupT`, `time_containsT`, `time_minT`, `time_maxT`, `time_predT`, `time_succT`,
  `time_rankT`: at most `height` visits.
* `time_lookupT_le_log`, `time_rankT_le_log`: with `IsWF.height_le_log`, at most
  `Nat.log t ((size + 1) / 2) + 1` visits on a well-formed tree; likewise for the other queries.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Cost/Query.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Cost/Query.lean).
-/

public section

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace Cslib.DataStructure.BTree

section NodeVisits

variable {α β : Type} {tr : BTree α β}

/-- Least entry, charging one tick per node visited. -/
def minT (tr : BTree α β) : TimeM ℕ (Option (α × β)) := minM (tick 1) tr

/-- `minT` is `minM` with one tick per visit. -/
theorem minT_def : minT tr = minM (tick 1) tr := (rfl)

/-- Greatest entry, charging one tick per node visited. -/
def maxT (tr : BTree α β) : TimeM ℕ (Option (α × β)) := maxM (tick 1) tr

/-- `maxT` is `maxM` with one tick per visit. -/
theorem maxT_def : maxT tr = maxM (tick 1) tr := (rfl)

/-- The value of `minT` is `min?`. -/
@[simp] theorem ret_minT : (minT tr).ret = min? tr := by
  simpa only [min?_def, minT, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_minM (tick 1) tr)

/-- The value of `maxT` is `max?`. -/
@[simp] theorem ret_maxT : (maxT tr).ret = max? tr := by
  simpa only [max?_def, maxT, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_maxM (tick 1) tr)

/-- The minimum search visits at most `height` nodes. -/
theorem time_minT {tr : BTree α β} : (minT tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp [minT, minM]
  | .node first rest =>
    have h := time_minT (tr := first)
    have e := height_first_succ_le (first := first) (rest := rest)
    simp only [minT] at h ⊢
    generalize (node first rest).height = H at e ⊢
    simp only [minM, TimeM.time_bind, TimeM.time_tick]
    split <;> simp <;> omega

/-- The maximum search visits at most `height` nodes. -/
theorem time_maxT {tr : BTree α β} : (maxT tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp [maxT, maxM_leaf]
  | .node first [] =>
    have h := time_maxT (tr := first)
    have e := height_first_succ_le (first := first) (rest := [])
    simp only [maxT] at h ⊢
    generalize (node first []).height = H at e ⊢
    simp [maxM_node_nil]
    omega
  | .node first [(k, v, c)] =>
    have h := time_maxT (tr := c)
    have e : c.height + 1 ≤ (node first [(k, v, c)]).height :=
      height_succ_le_of_mem_rest (List.mem_singleton_self (k, v, c))
    simp only [maxT] at h ⊢
    generalize (node first [(k, v, c)]).height = H at e ⊢
    simp only [maxM_node_singleton, TimeM.time_bind, TimeM.time_tick]
    split <;> simp <;> omega
  | .node first ((k, v, c) :: e :: rest) =>
    have h := time_maxT (tr := .node c (e :: rest))
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := e :: rest)
    simp only [maxT, maxM_node_cons_cons] at h ⊢
    omega
termination_by sizeOf tr

variable [LinearOrder α] {t : ℕ}

/-- The decidable comparator of a linear order, in `TimeM ℕ`: comparisons are free. -/
abbrev leT (a b : α) : TimeM ℕ Bool := pure (decide (a ≤ b))

/-- Lookup charging one tick per node visited. -/
def lookupT (k : α) (tr : BTree α β) : TimeM ℕ (Option β) := lookupM leT (tick 1) k tr

/-- `lookupT` is `lookupM` with the free comparator and one tick per visit. -/
theorem lookupT_def (k : α) : lookupT k tr = lookupM leT (tick 1) k tr := (rfl)

/-- Membership test charging one tick per node visited. -/
def containsT (k : α) (tr : BTree α β) : TimeM ℕ Bool := containsM leT (tick 1) k tr

/-- `containsT` is `containsM` with the free comparator and one tick per visit. -/
theorem containsT_def (k : α) : containsT k tr = containsM leT (tick 1) k tr := (rfl)

/-- The membership test is the success of lookup, at the same cost. -/
theorem containsT_eq (k : α) : containsT k tr = Option.isSome <$> lookupT k tr := by
  simp [containsT, containsM, lookupT]

/-- Strict predecessor, charging one tick per node visited. -/
def predT (k : α) (tr : BTree α β) : TimeM ℕ (Option (α × β)) := predM leT (tick 1) k tr

/-- `predT` is `predM` with the free comparator and one tick per visit. -/
theorem predT_def (k : α) : predT k tr = predM leT (tick 1) k tr := (rfl)

/-- Strict successor, charging one tick per node visited. -/
def succT (k : α) (tr : BTree α β) : TimeM ℕ (Option (α × β)) := succM leT (tick 1) k tr

/-- `succT` is `succM` with the free comparator and one tick per visit. -/
theorem succT_def (k : α) : succT k tr = succM leT (tick 1) k tr := (rfl)

/-- Rank, charging one tick per node visited. -/
def rankT (k : α) (tr : BTree α β) : TimeM ℕ ℕ := rankM leT (tick 1) k tr

/-- `rankT` is `rankM` with the free comparator and one tick per visit. -/
theorem rankT_def (k : α) : rankT k tr = rankM leT (tick 1) k tr := (rfl)

/-- The value of `lookupT` is `lookup`. -/
@[simp] theorem ret_lookupT (k : α) : (lookupT k tr).ret = lookup k tr := by
  simpa only [lookup_def, lookupT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_lookupM leT (tick 1) k tr)

/-- The value of `containsT` is `contains`. -/
@[simp] theorem ret_containsT (k : α) : (containsT k tr).ret = contains k tr := by
  simpa only [contains_def, containsT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_containsM leT (tick 1) k tr)

/-- The value of `predT` is `pred?`. -/
@[simp] theorem ret_predT (k : α) : (predT k tr).ret = pred? k tr := by
  simpa only [pred?_def, predT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_predM leT (tick 1) k tr)

/-- The value of `succT` is `succ?`. -/
@[simp] theorem ret_succT (k : α) : (succT k tr).ret = succ? k tr := by
  simpa only [succ?_def, succT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_succM leT (tick 1) k tr)

/-- The value of `rankT` is `rank`. -/
@[simp] theorem ret_rankT (k : α) : (rankT k tr).ret = rank k tr := by
  simpa only [rank_def, rankT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_rankM leT (tick 1) k tr)

/-! ### Node-visit bounds -/

/-- Lookup visits at most `height` nodes. -/
theorem time_lookupT {tr : BTree α β} (k : α) : (lookupT k tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp [lookupT, lookupM]
  | .node first [] =>
    have h := time_lookupT (tr := first) k
    have e := height_first_succ_le (first := first) (rest := [])
    simp only [lookupT] at h ⊢
    generalize (node first []).height = H at e ⊢
    simp [lookupM]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_lookupT (tr := first) k
    have h₂ := time_lookupT (tr := .node c rest) k
    have e₁ := height_first_succ_le (first := first) (rest := (k', v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k') (v := v) (c := c)
      (rest := rest)
    simp only [lookupT] at h₁ h₂ ⊢
    generalize (node first ((k', v, c) :: rest)).height = H at e₁ e₂ ⊢
    by_cases hk : k ≤ k' <;> by_cases hk' : k' ≤ k <;> simp [lookupM, hk, hk'] <;> omega
termination_by sizeOf tr

/-- The membership test visits at most `height` nodes. -/
theorem time_containsT (k : α) : (containsT k tr).time ≤ tr.height := by
  rw [containsT_eq, TimeM.time_map]
  exact time_lookupT k

/-- The predecessor search visits at most `height` nodes. -/
theorem time_predT {tr : BTree α β} (k : α) : (predT k tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp [predT, predM_leaf]
  | .node first [] =>
    have h := time_predT (tr := first) k
    have e := height_first_succ_le (first := first) (rest := [])
    simp only [predT] at h ⊢
    generalize (node first []).height = H at e ⊢
    simp [predM_node_nil]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_predT (tr := first) k
    have h₂ := time_predT (tr := .node c rest) k
    have e₁ := height_first_succ_le (first := first) (rest := (k', v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k') (v := v) (c := c)
      (rest := rest)
    simp only [predT] at h₁ h₂ ⊢
    generalize (node first ((k', v, c) :: rest)).height = H at e₁ e₂ ⊢
    by_cases hk : k ≤ k' <;> simp [predM_node_cons, hk] <;> omega
termination_by sizeOf tr

/-- The successor search visits at most `height` nodes. -/
theorem time_succT {tr : BTree α β} (k : α) : (succT k tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp [succT, succM_leaf]
  | .node first [] =>
    have h := time_succT (tr := first) k
    have e := height_first_succ_le (first := first) (rest := [])
    simp only [succT] at h ⊢
    generalize (node first []).height = H at e ⊢
    simp [succM_node_nil]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_succT (tr := first) k
    have h₂ := time_succT (tr := .node c rest) k
    have e₁ := height_first_succ_le (first := first) (rest := (k', v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k') (v := v) (c := c)
      (rest := rest)
    simp only [succT] at h₁ h₂ ⊢
    generalize (node first ((k', v, c) :: rest)).height = H at e₁ e₂ ⊢
    by_cases hk : k' ≤ k <;> simp [succM_node_cons, hk] <;> omega
termination_by sizeOf tr

/-- The rank search visits at most `height` nodes. -/
theorem time_rankT {tr : BTree α β} (k : α) : (rankT k tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp [rankT, rankM_leaf]
  | .node first [] =>
    have h := time_rankT (tr := first) k
    have e := height_first_succ_le (first := first) (rest := [])
    simp only [rankT] at h ⊢
    generalize (node first []).height = H at e ⊢
    simp [rankM_node_nil]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_rankT (tr := first) k
    have h₂ := time_rankT (tr := .node c rest) k
    have e₁ := height_first_succ_le (first := first) (rest := (k', v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k') (v := v) (c := c)
      (rest := rest)
    simp only [rankT] at h₁ h₂ ⊢
    generalize (node first ((k', v, c) :: rest)).height = H at e₁ e₂ ⊢
    by_cases hk : k ≤ k' <;> simp [rankM_node_cons, hk] <;> omega
termination_by sizeOf tr

/-- Lookup in a well-formed tree visits logarithmically many nodes. -/
theorem time_lookupT_le_log (h : IsWF t tr) (k : α) :
    (lookupT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_lookupT k).trans h.height_le_log

/-- The membership test in a well-formed tree visits logarithmically many nodes. -/
theorem time_containsT_le_log (h : IsWF t tr) (k : α) :
    (containsT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_containsT k).trans h.height_le_log

/-- The predecessor search in a well-formed tree visits logarithmically many nodes. -/
theorem time_predT_le_log (h : IsWF t tr) (k : α) :
    (predT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_predT k).trans h.height_le_log

/-- The successor search in a well-formed tree visits logarithmically many nodes. -/
theorem time_succT_le_log (h : IsWF t tr) (k : α) :
    (succT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_succT k).trans h.height_le_log

/-- The rank search in a well-formed tree visits logarithmically many nodes. -/
theorem time_rankT_le_log (h : IsWF t tr) (k : α) :
    (rankT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_rankT k).trans h.height_le_log

/-- The minimum search in a well-formed tree visits logarithmically many nodes. -/
theorem time_minT_le_log (h : IsWF t tr) :
    (minT tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  time_minT.trans h.height_le_log

/-- The maximum search in a well-formed tree visits logarithmically many nodes. -/
theorem time_maxT_le_log (h : IsWF t tr) :
    (maxT tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  time_maxT.trans h.height_le_log

end NodeVisits

end Cslib.DataStructure.BTree
